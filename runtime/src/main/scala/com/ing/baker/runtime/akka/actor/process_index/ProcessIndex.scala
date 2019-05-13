package com.ing.baker.runtime.akka.actor.process_index

import akka.actor.{ActorRef, NoSerializationVerificationNeeded, Props, Terminated}
import akka.event.{DiagnosticLoggingAdapter, Logging}
import akka.pattern.ask
import akka.persistence.{PersistentActor, RecoveryCompleted}
import akka.stream.Materializer
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.{InteractionTransition, Place, Transition}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.akka.actor.Util.logging._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.{ProcessInstance, ProcessInstanceRuntime}
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.akka.actor.serialization.Encryption
import com.ing.baker.runtime.akka.events.{ProcessCreated, RejectReason}
import com.ing.baker.runtime.akka.internal.{InteractionManager, RecipeRuntime}
import com.ing.baker.runtime.akka.{ProcessState, RuntimeEvent, events, namedCachedThreadPool, _}

import scala.collection.mutable
import scala.concurrent.duration._
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.util.{Failure, Success, Try}
import cats.data.OptionT
import cats.instances.future._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.ExceptionStrategy.{BlockTransition, Continue, RetryWithDelay}
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable
import com.ing.baker.types.Value

object ProcessIndex {

  def props(processIdleTimeout: Option[FiniteDuration],
            retentionCheckInterval: Option[FiniteDuration],
            configuredEncryption: Encryption,
            interactionManager: InteractionManager,
            recipeManager: ActorRef,
            ingredientsFilter: Seq[String])(implicit materializer: Materializer) =
    Props(new ProcessIndex(processIdleTimeout, retentionCheckInterval, configuredEncryption, interactionManager, recipeManager, ingredientsFilter))

  sealed trait ProcessStatus

  //message
  case object CheckForProcessesToBeDeleted extends NoSerializationVerificationNeeded

  //The process is created and not deleted
  case object Active extends ProcessStatus

  //The process was deleted
  case object Deleted extends ProcessStatus

  case class ActorMetadata(recipeId: String, processId: String, createdDateTime: Long, processStatus: ProcessStatus) extends BakerSerializable {

    def isDeleted: Boolean = processStatus == Deleted
  }

  // --- Events

  // when an actor is requested again after passivation
  case class ActorActivated(processId: String) extends BakerSerializable

  // when an actor is passivated
  case class ActorPassivated(processId: String) extends BakerSerializable

  // when an actor is deleted
  case class ActorDeleted(processId: String) extends BakerSerializable

  // when an actor is created
  case class ActorCreated(recipeId: String, processId: String, createdDateTime: Long) extends BakerSerializable

  private val bakerExecutionContext: ExecutionContext = namedCachedThreadPool(s"Baker.CachedThreadPool")
}

class ProcessIndex(processIdleTimeout: Option[FiniteDuration],
                   retentionCheckInterval: Option[FiniteDuration],
                   configuredEncryption: Encryption,
                   interactionManager: InteractionManager,
                   recipeManager: ActorRef,
                   ingredientsFilter: Seq[String])(implicit materializer: Materializer) extends PersistentActor {

  val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  import context.dispatcher

  private val processInquireTimeout: FiniteDuration = context.system.settings.config.getDuration("baker.process-inquire-timeout").toScala
  private val updateCacheTimeout: FiniteDuration = context.system.settings.config.getDuration("baker.process-index-update-cache-timeout").toScala
  private val index: mutable.Map[String, ActorMetadata] = mutable.Map[String, ActorMetadata]()
  private val recipeCache: mutable.Map[String, (CompiledRecipe, Long)] = mutable.Map[String, (CompiledRecipe, Long)]()

  // if there is a retention check interval defined we schedule a recurring message
  retentionCheckInterval.foreach { interval =>
    context.system.scheduler.schedule(interval, interval, context.self, CheckForProcessesToBeDeleted)
  }

  def updateCache() = {
    // TODO this is a synchronous ask on an actor which is considered bad practice, alternative?
    val futureResult = recipeManager.ask(GetAllRecipes)(updateCacheTimeout).mapTo[AllRecipes]
    val allRecipes = Await.result(futureResult, updateCacheTimeout)
    recipeCache ++= allRecipes.recipes.map(ri => ri.compiledRecipe.recipeId -> (ri.compiledRecipe, ri.timestamp))
  }

  def getRecipeWithTimeStamp(recipeId: String): Option[(CompiledRecipe, Long)] =
    recipeCache.get(recipeId) match {
      case None => {
        updateCache()
        recipeCache.get(recipeId)
      }
      case other => other
    }

  def getCompiledRecipe(recipeId: String): Option[CompiledRecipe] =
    getRecipeWithTimeStamp(recipeId).map { case (recipe, _) => recipe }

  def getOrCreateProcessActor(processId: String): ActorRef =
    context.child(processId).getOrElse(createProcessActor(processId))

  def createProcessActor(processId: String): ActorRef = {
    val recipeId = index(processId).recipeId
    val compiledRecipe: CompiledRecipe =
      getCompiledRecipe(recipeId).getOrElse(throw new IllegalStateException(s"No recipe with recipe id '$recipeId' exists"))
    createProcessActor(processId, compiledRecipe)
  }

  // creates a ProcessInstanceActor, does not do any validation
  def createProcessActor(processId: String, compiledRecipe: CompiledRecipe): ActorRef = {
    val runtime: ProcessInstanceRuntime[Place, Transition, ProcessState, RuntimeEvent] =
      new RecipeRuntime(compiledRecipe, interactionManager, context.system.eventStream)

    val processActorProps =
      ProcessInstance.props[Place, Transition, ProcessState, RuntimeEvent](
        compiledRecipe.name, compiledRecipe.petriNet, runtime,
        ProcessInstance.Settings(
          executionContext = bakerExecutionContext,
          encryption = configuredEncryption,
          idleTTL = processIdleTimeout,
          ingredientsFilter = ingredientsFilter))

    val processActor = context.actorOf(props = processActorProps, name = processId)

    context.watch(processActor)
    processActor
  }

  def shouldDelete(meta: ActorMetadata): Boolean = {
    meta.processStatus != Deleted &&
      getCompiledRecipe(meta.recipeId)
        .flatMap(_.retentionPeriod)
        .exists { p => meta.createdDateTime + p.toMillis < System.currentTimeMillis() }
  }

  def withActiveProcess(processId: String)(fn: ActorRef => Unit) = {
    context.child(processId) match {
      case None if !index.contains(processId) => sender() ! NoSuchProcess(processId)
      case None if index(processId).isDeleted => sender() ! ProcessDeleted(processId)
      case None =>
        persist(ActorActivated(processId)) { _ =>
          val actor = createProcessActor(processId)
          fn(actor)
        }
      case Some(actorRef) => fn(actorRef)
    }
  }

  def getInteractionJob(processId: String, interactionName: String, processActor: ActorRef): OptionT[Future, (InteractionTransition, Id)] = {
    // we find which job correlates with the interaction
    for {
      recipe     <- OptionT.fromOption(getCompiledRecipe(index(processId).recipeId))
      transition <- OptionT.fromOption(recipe.interactionTransitions.find(_.interactionName == interactionName))
      state      <- OptionT(processActor.ask(GetState)(processInquireTimeout).mapTo[InstanceState].map(Option(_)))
      jobId      <- OptionT.fromOption(state.jobs.collectFirst { case (jobId, job) if job.transitionId == transition.id => jobId }  )
    } yield (transition, jobId)
  }

  override def receiveCommand: Receive = {

    case GetIndex =>
      sender() ! Index(index.values.filter(_.processStatus == Active).toSeq)

    case CheckForProcessesToBeDeleted =>
      val toBeDeleted = index.values.filter(shouldDelete)
      if (toBeDeleted.nonEmpty)
        log.debug(s"Deleting processes: {}", toBeDeleted.mkString(","))

      toBeDeleted.foreach(meta => getOrCreateProcessActor(meta.processId) ! Stop(delete = true))

    case Terminated(actorRef) =>
      val processId = actorRef.path.name

      log.logWithMDC(Logging.DebugLevel, s"Actor terminated: $actorRef", Map("processId" -> processId))

      index.get(processId) match {
        case Some(meta) if shouldDelete(meta) =>
          persist(ActorDeleted(processId)) { _ =>
            index.update(processId, meta.copy(processStatus = Deleted))
          }
        case Some(meta) if meta.isDeleted =>
          log.logWithMDC(Logging.WarningLevel, s"Received Terminated message for already deleted process: ${meta.processId}", Map("processId" -> processId))
        case Some(_) =>
          persist(ActorPassivated(processId)) { _ => }
        case None =>
          log.logWithMDC(Logging.WarningLevel, s"Received Terminated message for non indexed actor: $actorRef", Map("processId" -> processId))
      }

    case CreateProcess(recipeId, processId) =>
      context.child(processId) match {
        case None if !index.contains(processId) =>

          // First check if the recipe exists
          getCompiledRecipe(recipeId) match {
            case Some(compiledRecipe) =>

              val createdTime = System.currentTimeMillis()

              // this persists the fact that we created a process instance
              persist(ActorCreated(recipeId, processId, createdTime)) { _ =>

                // after that we actually create the ProcessInstance actor
                val processState = ProcessState(processId, Map.empty[String, Value], List.empty)
                val initializeCmd = Initialize(compiledRecipe.initialMarking, processState)

                createProcessActor(processId, compiledRecipe).forward(initializeCmd)

                val actorMetadata = ActorMetadata(recipeId, processId, createdTime, Active)

                context.system.eventStream.publish(ProcessCreated(System.currentTimeMillis(), recipeId, compiledRecipe.name, processId))

                index += processId -> actorMetadata
              }

            case None => sender() ! NoRecipeFound(recipeId)
          }

        case _ if index(processId).isDeleted => sender() ! ProcessDeleted(processId)
        case _ => sender() ! ProcessAlreadyExists(processId)
      }

    case cmd @ ProcessEvent(processId: String, event: RuntimeEvent, _, waitForRetries, processEventTimout, streamReceiver) =>

      def rejectWith(msg: Any, rejectReason: RejectReason): Unit = {
        context.system.eventStream.publish(events.EventRejected(System.currentTimeMillis(), cmd.processId, cmd.correlationId, cmd.event, rejectReason))
        // Rejections are directly sent to the receiver side
        streamReceiver ! msg
      }

      def forwardEvent(processInstance: ActorRef, recipe: CompiledRecipe): Unit = {
        recipe.sensoryEvents.find(sensoryEvent => sensoryEvent.name == event.name) match {
          case None =>
            rejectWith(InvalidEvent(processId, s"No event with name '${event.name}' found in recipe '${recipe.name}'"), RejectReason.InvalidEvent)
          case Some(sensoryEvent) =>
            //Check If the sensory event is valid for this recipe
            val eventValidationErrors = event.validateEvent(sensoryEvent)

            if (eventValidationErrors.nonEmpty)
              rejectWith(InvalidEvent(processId, s"Invalid event: " + eventValidationErrors.mkString(",")), RejectReason.InvalidEvent)
            else {

              recipe.eventReceivePeriod match {

                // if the receive period is expired the event is rejected
                case Some(receivePeriod) if System.currentTimeMillis() - index(processId).createdDateTime > receivePeriod.toMillis =>
                  rejectWith(ReceivePeriodExpired(processId), RejectReason.ReceivePeriodExpired)

                // otherwise the event is forwarded
                case _ =>
                  (for {
                    _ <- Try(require(cmd.event != null, "Event can not be null"))
                    transition <- recipe.petriNet.transitions.find(_.label == cmd.event.name) match {
                      case Some(transition0) => Success(transition0)
                      case None => Failure(new IllegalArgumentException(s"No such event known in recipe: ${cmd.event.name}"))
                    }
                  } yield FireTransition(transition.id, cmd.event, cmd.correlationId)).fold(
                    { error => rejectWith(InvalidEvent(processId, error.getMessage), RejectReason.InvalidEvent) },
                    { event =>
                      val streamSender = context.actorOf(ProcessEventSender(streamReceiver, cmd, recipe, waitForRetries)(processEventTimout))
                      processInstance.tell(event, streamSender)
                    }
                  )
              }
            }
        }
      }

      context.child(processId) match {
        case None if !index.contains(processId) => rejectWith(NoSuchProcess(processId), RejectReason.NoSuchProcess)
        case None if index(processId).isDeleted => rejectWith(ProcessDeleted(processId), RejectReason.ProcessDeleted)

        case _ =>
          // here we activate the process (if required) and forward the event
          withActiveProcess(processId) { actorRef =>
            getCompiledRecipe(index(processId).recipeId).foreach { compiledRecipe: CompiledRecipe =>
              forwardEvent(actorRef, compiledRecipe)
            }
        }
      }

    case StopRetryingInteraction(processId, interactionName) =>

      withActiveProcess(processId) { processActor =>

        val originalSender = sender()

        // we find which job correlates with the interaction
        getInteractionJob(processId, interactionName, processActor).value.onComplete {
          case Success(Some((_, jobId))) => processActor.tell(OverrideExceptionStrategy(jobId, BlockTransition), originalSender)
          case Success(_)                => originalSender ! akka.actor.Status.Failure(new IllegalArgumentException("Interaction is not retrying"))
          case Failure(exception)        => originalSender ! akka.actor.Status.Failure(exception)
        }
      }

    case RetryBlockedInteraction(processId, interactionName) =>

      withActiveProcess(processId) { processActor =>

        val originalSender = sender()

        getInteractionJob(processId, interactionName, processActor).value.onComplete {
          case Success(Some((_, jobId))) => processActor.tell(OverrideExceptionStrategy(jobId, RetryWithDelay(0)), originalSender)
          case Success(_)                => originalSender ! akka.actor.Status.Failure(new IllegalArgumentException("Interaction is not blocked"))
          case Failure(exception)        => originalSender ! akka.actor.Status.Failure(exception)
        }
      }

    case ResolveBlockedInteraction(processId, interactionName, event) =>

      withActiveProcess(processId) { processActor =>

        val originalSender = sender()

        getInteractionJob(processId, interactionName, processActor).value.onComplete {
          case Success(Some((interaction, jobId))) =>
            RecipeRuntime.validateInteractionOutput(interaction, Some(event)) match {

              case None        =>
                val petriNet = getCompiledRecipe(index(processId).recipeId).get.petriNet
                val producedMarking = RecipeRuntime.createProducedMarking(petriNet.outMarking(interaction), Some(event))
                val transformedEvent = RecipeRuntime.transformInteractionEvent(interaction, event)

                processActor.tell(OverrideExceptionStrategy(jobId, Continue(producedMarking.marshall, transformedEvent)), originalSender)
              case Some(error) =>
                log.warning("Invalid event given: " + error)
                originalSender ! InvalidEvent(processId, error)
            }
          case Success(_)         => originalSender ! akka.actor.Status.Failure(new IllegalArgumentException("Interaction is not blocked"))
          case Failure(exception) => originalSender ! akka.actor.Status.Failure(exception)
        }
      }

    case GetProcessState(processId) =>

      withActiveProcess(processId) { actorRef => actorRef.forward(GetState) }

    case GetCompiledRecipe(processId) =>
      index.get(processId) match {
        case Some(processMetadata) if processMetadata.isDeleted => sender() ! ProcessDeleted(processId)
        case Some(processMetadata) =>
          getRecipeWithTimeStamp(processMetadata.recipeId) match {
            case Some((compiledRecipe, timestamp)) => sender() ! RecipeFound(compiledRecipe, timestamp)
            case None => sender() ! NoSuchProcess(processId)
          }
        case None => sender() ! NoSuchProcess(processId)
      }
    case cmd =>
      log.error(s"Unrecognized command $cmd")
  }

  // This Set holds all the actor ids to be created again after the recovery completed
  private val actorsToBeCreated: mutable.Set[String] = mutable.Set.empty

  override def receiveRecover: Receive = {
    case ActorCreated(recipeId, processId, createdTime) =>
      index += processId -> ActorMetadata(recipeId, processId, createdTime, Active)
      actorsToBeCreated += processId
    case ActorPassivated(processId) =>
      actorsToBeCreated -= processId
    case ActorActivated(processId) =>
      actorsToBeCreated += processId
    case ActorDeleted(processId) =>
      actorsToBeCreated -= processId
      index.get(processId) match {
        case Some(processMeta) =>
          index.update(processId, processMeta.copy(processStatus = Deleted))
        case None =>
          log.error(s"ActorDeleted persisted for non existing processId: $processId")
      }

    case RecoveryCompleted =>
      actorsToBeCreated.foreach(id => createProcessActor(id))
  }

  override def persistenceId: String = self.path.name
}
