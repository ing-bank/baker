package com.ing.baker.runtime.akka.actor.process_index

import akka.actor.{ActorRef, NoSerializationVerificationNeeded, Props, Terminated}
import akka.event.{DiagnosticLoggingAdapter, Logging}
import akka.pattern.ask
import akka.persistence.{PersistentActor, RecoveryCompleted}
import akka.stream.Materializer
import com.ing.baker.il.{CompiledRecipe, EventDescriptor}
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
import cats.data.{EitherT, OptionT}
import cats.effect.IO
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
      case None =>
        updateCache()
        recipeCache.get(recipeId)
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
      case None if !index.contains(processId) => sender() ! ProcessRejection.NoSuchProcess(processId)
      case None if index(processId).isDeleted => sender() ! ProcessRejection.ProcessDeleted(processId)
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

            case None =>
              sender() ! CreateProcessRejection.NoRecipeFound(recipeId, processId)
          }

        case _ if index(processId).isDeleted =>
          sender() ! CreateProcessRejection.ProcessDeleted(processId)
        case _ =>
          sender() ! CreateProcessRejection.ProcessAlreadyExists(processId)
      }

    case command@ProcessEvent(processId, event, correlationId, _, _) =>

      run { responseHandler =>
        for {
          instanceAndMeta <- fetchInstance
          (processInstance, metadata) = instanceAndMeta
          recipe <- fetchRecipe(metadata)
          _ <- initializeResponseHandler(recipe, responseHandler)
          transitionAndDescriptor <- validateEventIsInRecipe(recipe)
          (transition, descriptor) = transitionAndDescriptor
          _ <- validateEventIsSound(descriptor)
          _ <- validateWithinReceivePeriod(recipe, metadata)
          fireTransitionCommand = FireTransition(transition.id, event, correlationId)
          _ <- forwardToProcessInstance(fireTransitionCommand, processInstance, responseHandler)
        } yield ()
      }

      type FireEventIO[A] = EitherT[IO, FireSensoryEventRejection, A]

      def run(program: ActorRef => FireEventIO[Unit]): Unit = {
        val responseHandler = context.actorOf(
          SensoryEventResponseHandler(sender, command))
        program(responseHandler).value.unsafeRunAsync {
          case Left(exception) =>
            throw exception // TODO decide what to do, might never happen, except if we generalize it as a runtime for the actor
          case Right(Left(rejection)) =>
            responseHandler ! rejection
          case Right(Right(())) =>
            ()
        }
      }

      def reject[A](rejection: FireSensoryEventRejection): FireEventIO[A] =
        EitherT.leftT(rejection)

      def accept[A](a: A): FireEventIO[A] =
        EitherT.rightT(a)

      def continue: FireEventIO[Unit] =
        accept(())

      def sync[A](thunk: => A): FireEventIO[A] =
        EitherT.liftF(IO(thunk))

      def async[A](callback: (Either[Throwable, A] => Unit) => Unit): FireEventIO[A] =
        EitherT.liftF(IO.async(callback))

      def fetchCurrentTime: FireEventIO[Long] =
        EitherT.liftF(IO { System.currentTimeMillis() })

      def fetchInstance: FireEventIO[(ActorRef, ActorMetadata)] =
        context.child(processId) match {
          case Some(process) =>
            accept(process -> index(processId))
          case None if !index.contains(processId) =>
            reject(FireSensoryEventRejection.NoSuchProcess(processId))
          case None if index(processId).isDeleted =>
            reject(FireSensoryEventRejection.ProcessDeleted(processId))
          case None =>
            async { callback =>
              persist(ActorActivated(processId)) { _ =>
                callback(Right(createProcessActor(processId) -> index(processId)))
              }
            }
        }

      def fetchRecipe(metadata: ActorMetadata): FireEventIO[CompiledRecipe] =
        accept(getCompiledRecipe(metadata.recipeId).get)

      def initializeResponseHandler(recipe: CompiledRecipe, handler: ActorRef): FireEventIO[Unit] =
        sync(handler ! recipe)

      def validateEventIsInRecipe(recipe: CompiledRecipe): FireEventIO[(Transition, EventDescriptor)] = {
        val transition0 = recipe.petriNet.transitions.find(_.label == event.name)
        val sensoryEvent0 = recipe.sensoryEvents.find(_.name == event.name)
        (transition0, sensoryEvent0) match {
          case (Some(transition), Some(sensoryEvent)) =>
            accept(transition -> sensoryEvent)
          case _ =>
            reject(FireSensoryEventRejection.InvalidEvent(
              processId,
              s"No event with name '${event.name}' found in recipe '${recipe.name}'"
            ))
        }
      }

      def validateEventIsSound(descriptor: EventDescriptor): FireEventIO[Unit] = {
        val eventValidationErrors = event.validateEvent(descriptor)
        if (eventValidationErrors.nonEmpty)
          reject(FireSensoryEventRejection.InvalidEvent(
            processId,
            s"Invalid event: " + eventValidationErrors.mkString(",")
          ))
        else continue
      }

      def validateWithinReceivePeriod(recipe: CompiledRecipe, metadata: ActorMetadata): FireEventIO[Unit] = {
        def outOfReceivePeriod(current: Long, period: FiniteDuration): Boolean =
          current - metadata.createdDateTime > period.toMillis
        for {
          currentTime <- fetchCurrentTime
          _ <- recipe.eventReceivePeriod match {
            case Some(receivePeriod) if outOfReceivePeriod(currentTime, receivePeriod) =>
              reject(FireSensoryEventRejection.ReceivePeriodExpired(processId))
            case _ => continue
          }
        } yield ()
      }

      def forwardToProcessInstance(fireTransitionCommand: FireTransition, processInstance: ActorRef, responseHandler: ActorRef): FireEventIO[Unit] =
        sync(processInstance.tell(fireTransitionCommand, responseHandler))

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

              case None =>
                val petriNet = getCompiledRecipe(index(processId).recipeId).get.petriNet
                val producedMarking = RecipeRuntime.createProducedMarking(petriNet.outMarking(interaction), Some(event))
                val transformedEvent = RecipeRuntime.transformInteractionEvent(interaction, event)

                processActor.tell(OverrideExceptionStrategy(jobId, Continue(producedMarking.marshall, transformedEvent)), originalSender)
              case Some(error) =>
                log.warning("Invalid event given: " + error)
                originalSender ! InvalidEventWhenResolveBlocked(processId, error)
            }
          case Success(_)         => originalSender ! akka.actor.Status.Failure(new IllegalArgumentException("Interaction is not blocked"))
          case Failure(exception) => originalSender ! akka.actor.Status.Failure(exception)
        }
      }

    case GetProcessState(processId) =>

      withActiveProcess(processId) { actorRef => actorRef.forward(GetState) }

    case GetCompiledRecipe(processId) =>
      index.get(processId) match {
        case Some(processMetadata) if processMetadata.isDeleted => sender() ! ProcessRejection.ProcessDeleted(processId)
        case Some(processMetadata) =>
          getRecipeWithTimeStamp(processMetadata.recipeId) match {
            case Some((compiledRecipe, timestamp)) => sender() ! RecipeFound(compiledRecipe, timestamp)
            case None => sender() ! ProcessRejection.NoSuchProcess(processId)
          }
        case None => sender() ! ProcessRejection.NoSuchProcess(processId)
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
