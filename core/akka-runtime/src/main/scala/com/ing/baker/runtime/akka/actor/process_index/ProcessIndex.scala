package com.ing.baker.runtime.akka.actor.process_index

import akka.actor.{ActorRef, NoSerializationVerificationNeeded, Props, Terminated}
import akka.event.{DiagnosticLoggingAdapter, Logging}
import akka.pattern.ask
import akka.persistence.{PersistentActor, RecoveryCompleted}
import akka.sensors.actor.PersistentActorMetrics
import cats.data.{EitherT, OptionT}
import cats.effect.IO
import cats.instances.future._
import com.ing.baker.il.petrinet.{InteractionTransition, Place, Transition}
import com.ing.baker.il.{CompiledRecipe, EventDescriptor}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.RecipeManager
import com.ing.baker.runtime.akka.actor.Util.logging._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex._
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol.ExceptionStrategy.{BlockTransition, Continue, RetryWithDelay}
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.akka.actor.process_instance.{ProcessInstance, ProcessInstanceRuntime}
import com.ing.baker.runtime.akka.actor.serialization.BakerSerializable
import com.ing.baker.runtime.akka.internal.RecipeRuntime
import com.ing.baker.runtime.akka.{namedCachedThreadPool, _}
import com.ing.baker.runtime.model.InteractionsF
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeInstanceCreated, RecipeInstanceState}
import com.ing.baker.runtime.serialization.Encryption
import com.ing.baker.types.Value

import scala.collection.mutable
import scala.concurrent.duration._
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.util.{Failure, Success}

object ProcessIndex {

  def props(recipeInstanceIdleTimeout: Option[FiniteDuration],
            retentionCheckInterval: Option[FiniteDuration],
            configuredEncryption: Encryption,
            interactions: InteractionsF[IO],
            recipeManager: RecipeManager,
            ingredientsFilter: Seq[String]) =
    Props(new ProcessIndex(
      recipeInstanceIdleTimeout,
      retentionCheckInterval,
      configuredEncryption,
      interactions,
      recipeManager,
      ingredientsFilter))

  sealed trait ProcessStatus

  //message
  case object CheckForProcessesToBeDeleted extends NoSerializationVerificationNeeded

  //The process is created and not deleted
  case object Active extends ProcessStatus

  //The process was deleted
  case object Deleted extends ProcessStatus

  case class ActorMetadata(recipeId: String, recipeInstanceId: String, createdDateTime: Long, processStatus: ProcessStatus) extends BakerSerializable {

    def isDeleted: Boolean = processStatus == Deleted
  }

  // --- Events

  // when an actor is requested again after passivation
  case class ActorActivated(recipeInstanceId: String) extends BakerSerializable

  // when an actor is passivated
  case class ActorPassivated(recipeInstanceId: String) extends BakerSerializable

  // when an actor is deleted
  case class ActorDeleted(recipeInstanceId: String) extends BakerSerializable

  // when an actor is created
  case class ActorCreated(recipeId: String, recipeInstanceId: String, createdDateTime: Long) extends BakerSerializable

  private val bakerExecutionContext: ExecutionContext = namedCachedThreadPool(s"Baker.CachedThreadPool")
}

class ProcessIndex(recipeInstanceIdleTimeout: Option[FiniteDuration],
                   retentionCheckInterval: Option[FiniteDuration],
                   configuredEncryption: Encryption,
                   interactionManager: InteractionsF[IO],
                   recipeManager: RecipeManager,
                   ingredientsFilter: Seq[String]) extends PersistentActor with PersistentActorMetrics {

  override val log: DiagnosticLoggingAdapter = Logging.getLogger(this)

  import context.dispatcher

  private val processInquireTimeout: FiniteDuration = context.system.settings.config.getDuration("baker.process-inquire-timeout").toScala
  private val updateCacheTimeout: FiniteDuration = context.system.settings.config.getDuration("baker.process-index-update-cache-timeout").toScala
  private val index: mutable.Map[String, ActorMetadata] = mutable.Map[String, ActorMetadata]()
  private val recipeCache: mutable.Map[String, (CompiledRecipe, Long)] = mutable.Map[String, (CompiledRecipe, Long)]()

  // if there is a retention check interval defined we schedule a recurring message
  retentionCheckInterval.foreach { interval =>
    context.system.scheduler.scheduleAtFixedRate(interval, interval, context.self, CheckForProcessesToBeDeleted)
  }

  def updateCache() = {
    val futureResult: Future[Seq[(CompiledRecipe, Long)]] = recipeManager.all
    val allRecipes: Seq[(CompiledRecipe, Long)] = Await.result(futureResult, updateCacheTimeout)
    recipeCache ++= allRecipes.map {
      case (recipe, timestamp) => recipe.recipeId -> (recipe, timestamp)
    }
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

  def getOrCreateProcessActor(recipeInstanceId: String): ActorRef =
    context.child(recipeInstanceId).getOrElse(createProcessActor(recipeInstanceId))

  def createProcessActor(recipeInstanceId: String): ActorRef = {
    val recipeId = index(recipeInstanceId).recipeId
    val compiledRecipe: CompiledRecipe =
      getCompiledRecipe(recipeId).getOrElse(throw new IllegalStateException(s"No recipe with recipe id '$recipeId' exists"))
    createProcessActor(recipeInstanceId, compiledRecipe)
  }

  // creates a ProcessInstanceActor, does not do any validation
  def createProcessActor(recipeInstanceId: String, compiledRecipe: CompiledRecipe): ActorRef = {
    val runtime: ProcessInstanceRuntime[Place, Transition, RecipeInstanceState, EventInstance] =
      new RecipeRuntime(compiledRecipe, interactionManager, context.system.eventStream)

    val processActorProps =
      ProcessInstance.props[Place, Transition, RecipeInstanceState, EventInstance](
        compiledRecipe.name, compiledRecipe.petriNet, runtime,
        ProcessInstance.Settings(
          executionContext = bakerExecutionContext,
          encryption = configuredEncryption,
          idleTTL = recipeInstanceIdleTimeout,
          ingredientsFilter = ingredientsFilter))

    val processActor = context.actorOf(props = processActorProps, name = recipeInstanceId)

    context.watch(processActor)
    processActor
  }

  def shouldDelete(meta: ActorMetadata): Boolean = {
    meta.processStatus != Deleted &&
      getCompiledRecipe(meta.recipeId)
        .flatMap(_.retentionPeriod)
        .exists { p => meta.createdDateTime + p.toMillis < System.currentTimeMillis() }
  }

  private def withActiveProcess(recipeInstanceId: String)(fn: ActorRef => Unit): Unit = {
    context.child(recipeInstanceId) match {
      case None if !index.contains(recipeInstanceId) => sender() ! NoSuchProcess(recipeInstanceId)
      case None if index(recipeInstanceId).isDeleted => sender() ! ProcessDeleted(recipeInstanceId)
      case None =>
        persist(ActorActivated(recipeInstanceId)) { _ =>
          val actor = createProcessActor(recipeInstanceId)
          fn(actor)
        }
      case Some(actorRef) => fn(actorRef)
    }
  }

  def getInteractionJob(recipeInstanceId: String, interactionName: String, processActor: ActorRef): OptionT[Future, (InteractionTransition, Id)] = {
    // we find which job correlates with the interaction
    for {
      recipe <- OptionT.fromOption(getCompiledRecipe(index(recipeInstanceId).recipeId))
      transition <- OptionT.fromOption(recipe.interactionTransitions.find(_.interactionName == interactionName))
      state <- OptionT(processActor.ask(GetState)(processInquireTimeout).mapTo[InstanceState].map(Option(_)))
      jobId <- OptionT.fromOption(state.jobs.collectFirst { case (jobId, job) if job.transitionId == transition.id => jobId })
    } yield (transition, jobId)
  }

  override def receiveCommand: Receive = {

    case GetIndex =>
      sender() ! Index(index.values.filter(_.processStatus == Active).toSeq)

    case CheckForProcessesToBeDeleted =>
      val toBeDeleted = index.values.filter(shouldDelete)
      if (toBeDeleted.nonEmpty)
        log.debug(s"Deleting recipe instance: {}", toBeDeleted.mkString(","))

      toBeDeleted.foreach(meta => getOrCreateProcessActor(meta.recipeInstanceId) ! Stop(delete = true))

    case Terminated(actorRef) =>
      val recipeInstanceId = actorRef.path.name

      val mdc = Map(
        "processId" -> recipeInstanceId,
        "recipeInstanceId" -> recipeInstanceId,
      )

      log.logWithMDC(Logging.DebugLevel, s"Actor terminated: $actorRef", mdc)

      index.get(recipeInstanceId) match {
        case Some(meta) if shouldDelete(meta) =>
          persist(ActorDeleted(recipeInstanceId)) { _ =>
            index.update(recipeInstanceId, meta.copy(processStatus = Deleted))
          }
        case Some(meta) if meta.isDeleted =>
          log.logWithMDC(Logging.WarningLevel, s"Received Terminated message for already deleted recipe instance: ${meta.recipeInstanceId}", mdc)
        case Some(_) =>
          persist(ActorPassivated(recipeInstanceId)) { _ => }
        case None =>
          log.logWithMDC(Logging.WarningLevel, s"Received Terminated message for non indexed actor: $actorRef", mdc)
      }

    case CreateProcess(recipeId, recipeInstanceId) =>
      context.child(recipeInstanceId) match {
        case None if !index.contains(recipeInstanceId) =>

          // First check if the recipe exists
          getCompiledRecipe(recipeId) match {
            case Some(compiledRecipe) =>

              val createdTime = System.currentTimeMillis()

              // this persists the fact that we created a process instance
              persist(ActorCreated(recipeId, recipeInstanceId, createdTime)) { _ =>

                // after that we actually create the ProcessInstance actor
                val processState = RecipeInstanceState(recipeInstanceId, Map.empty[String, Value], List.empty)
                val initializeCmd = Initialize(compiledRecipe.initialMarking, processState)

                createProcessActor(recipeInstanceId, compiledRecipe).forward(initializeCmd)

                val actorMetadata = ActorMetadata(recipeId, recipeInstanceId, createdTime, Active)

                context.system.eventStream.publish(RecipeInstanceCreated(System.currentTimeMillis(), recipeId, compiledRecipe.name, recipeInstanceId))

                index += recipeInstanceId -> actorMetadata
              }

            case None =>
              sender() ! NoRecipeFound(recipeId)
          }

        case _ if index(recipeInstanceId).isDeleted =>
          sender() ! ProcessDeleted(recipeInstanceId)
        case _ =>
          sender() ! ProcessAlreadyExists(recipeInstanceId)
      }

    case command@ProcessEvent(recipeInstanceId, event, correlationId, _, _) =>

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
          SensoryEventResponseHandler(sender, command, ingredientsFilter))
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
        EitherT.liftF(IO.async_(callback))

      def fetchCurrentTime: FireEventIO[Long] =
        EitherT.liftF(IO {
          System.currentTimeMillis()
        })

      def fetchInstance: FireEventIO[(ActorRef, ActorMetadata)] =
        context.child(recipeInstanceId) match {
          case Some(process) =>
            accept(process -> index(recipeInstanceId))
          case None if !index.contains(recipeInstanceId) =>
            reject(FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId))
          case None if index(recipeInstanceId).isDeleted =>
            reject(FireSensoryEventRejection.RecipeInstanceDeleted(recipeInstanceId))
          case None =>
            async { callback =>
              persist(ActorActivated(recipeInstanceId)) { _ =>
                callback(Right(createProcessActor(recipeInstanceId) -> index(recipeInstanceId)))
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
              recipeInstanceId,
              s"No event with name '${event.name}' found in recipe '${recipe.name}'"
            ))
        }
      }

      def validateEventIsSound(descriptor: EventDescriptor): FireEventIO[Unit] = {
        val eventValidationErrors = event.validate(descriptor)
        if (eventValidationErrors.nonEmpty)
          reject(FireSensoryEventRejection.InvalidEvent(
            recipeInstanceId,
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
              reject(FireSensoryEventRejection.ReceivePeriodExpired(recipeInstanceId))
            case _ => continue
          }
        } yield ()
      }

      def forwardToProcessInstance(fireTransitionCommand: FireTransition, processInstance: ActorRef, responseHandler: ActorRef): FireEventIO[Unit] =
        sync(processInstance.tell(fireTransitionCommand, responseHandler))

    case StopRetryingInteraction(recipeInstanceId, interactionName) =>

      withActiveProcess(recipeInstanceId) { processActor =>

        val originalSender = sender()

        // we find which job correlates with the interaction
        getInteractionJob(recipeInstanceId, interactionName, processActor).value.onComplete {
          case Success(Some((_, jobId))) => processActor.tell(OverrideExceptionStrategy(jobId, BlockTransition), originalSender)
          case Success(_) => originalSender ! akka.actor.Status.Failure(new IllegalArgumentException("Interaction is not retrying"))
          case Failure(exception) => originalSender ! akka.actor.Status.Failure(exception)
        }
      }

    case RetryBlockedInteraction(recipeInstanceId, interactionName) =>

      withActiveProcess(recipeInstanceId) { processActor =>

        val originalSender = sender()

        getInteractionJob(recipeInstanceId, interactionName, processActor).value.onComplete {
          case Success(Some((_, jobId))) => processActor.tell(OverrideExceptionStrategy(jobId, RetryWithDelay(0)), originalSender)
          case Success(_) => originalSender ! akka.actor.Status.Failure(new IllegalArgumentException("Interaction is not blocked"))
          case Failure(exception) => originalSender ! akka.actor.Status.Failure(exception)
        }
      }

    case ResolveBlockedInteraction(recipeInstanceId, interactionName, event) =>

      withActiveProcess(recipeInstanceId) { processActor =>

        val originalSender = sender()

        getInteractionJob(recipeInstanceId, interactionName, processActor).value.onComplete {
          case Success(Some((interaction, jobId))) =>
            RecipeRuntime.validateInteractionOutput(interaction, Some(event)) match {

              case None =>
                val petriNet = getCompiledRecipe(index(recipeInstanceId).recipeId).get.petriNet
                val producedMarking = RecipeRuntime.createProducedMarking(petriNet.outMarking(interaction), Some(event))
                val transformedEvent = RecipeRuntime.transformInteractionEvent(interaction, event)

                processActor.tell(OverrideExceptionStrategy(jobId, Continue(producedMarking.marshall, transformedEvent)), originalSender)
              case Some(error) =>
                log.warning("Invalid event given: " + error)
                originalSender ! InvalidEventWhenResolveBlocked(recipeInstanceId, error)
            }
          case Success(_) => originalSender ! akka.actor.Status.Failure(new IllegalArgumentException("Interaction is not blocked"))
          case Failure(exception) => originalSender ! akka.actor.Status.Failure(exception)
        }
      }

    case GetProcessState(recipeInstanceId) =>
      withActiveProcess(recipeInstanceId) { actorRef => actorRef.forward(GetState) }

    case GetCompiledRecipe(recipeInstanceId) =>
      index.get(recipeInstanceId) match {
        case Some(processMetadata) if processMetadata.isDeleted => sender() ! ProcessDeleted(recipeInstanceId)
        case Some(processMetadata) =>
          getRecipeWithTimeStamp(processMetadata.recipeId) match {
            case Some((compiledRecipe, timestamp)) => sender() ! RecipeFound(compiledRecipe, timestamp)
            case None => sender() ! NoSuchProcess(recipeInstanceId)
          }
        case None => sender() ! NoSuchProcess(recipeInstanceId)
      }
    case cmd =>
      log.error(s"Unrecognized command $cmd")
  }

  // This Set holds all the actor ids to be created again after the recovery completed
  private val actorsToBeCreated: mutable.Set[String] = mutable.Set.empty

  override def receiveRecover: Receive = {
    case ActorCreated(recipeId, recipeInstanceId, createdTime) =>
      index += recipeInstanceId -> ActorMetadata(recipeId, recipeInstanceId, createdTime, Active)
      actorsToBeCreated += recipeInstanceId
    case ActorPassivated(recipeInstanceId) =>
      actorsToBeCreated -= recipeInstanceId
    case ActorActivated(recipeInstanceId) =>
      actorsToBeCreated += recipeInstanceId
    case ActorDeleted(recipeInstanceId) =>
      actorsToBeCreated -= recipeInstanceId
      index.get(recipeInstanceId) match {
        case Some(processMeta) =>
          index.update(recipeInstanceId, processMeta.copy(processStatus = Deleted))
        case None =>
          log.error(s"ActorDeleted persisted for non existing RecipeInstanceId: $recipeInstanceId")
      }

    case RecoveryCompleted =>
      actorsToBeCreated.foreach(id => createProcessActor(id))
  }

  override def persistenceId: String = self.path.name
}
