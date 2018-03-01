package com.ing.baker.runtime.actor.process_index

import akka.actor.{ActorLogging, ActorRef, Props, Terminated}
import akka.pattern.ask
import akka.persistence.{PersistentActor, RecoveryCompleted}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.runtime.PetriNetRuntime
import com.ing.baker.runtime.actor._
import com.ing.baker.runtime.actor.process_index.ProcessIndex._
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.actor.process_instance.{ProcessInstance, ProcessInstanceProtocol}
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._
import com.ing.baker.runtime.actor.serialization.Encryption
import com.ing.baker.runtime.core.interations.InteractionManager
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}
import com.ing.baker.runtime.petrinet.RecipeRuntime
import fs2.Strategy

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration._


object ProcessIndex {

  def props(cleanupInterval: FiniteDuration = 1 minute,
            processIdleTimeout: Option[FiniteDuration],
            configuredEncryption: Encryption,
            interactionManager: InteractionManager,
            recipeManager: ActorRef) =
    Props(new ProcessIndex(cleanupInterval, processIdleTimeout, configuredEncryption, interactionManager, recipeManager))

  sealed trait ProcessStatus

  //message
  case object CheckForProcessesToBeDeleted extends InternalBakerMessage

  //The process is created and not deleted
  case object Active extends ProcessStatus

  //The process was deleted
  case object Deleted extends ProcessStatus

  case class ActorMetadata(recipeId: String, processId: String, createdDateTime: Long, processStatus: ProcessStatus)

  // --- Events

  // when an actor is requested again after passivation
  case class ActorActivated(processId: String) extends InternalBakerEvent

  // when an actor is passivated
  case class ActorPassivated(processId: String) extends InternalBakerEvent

  // when an actor is deleted
  case class ActorDeleted(processId: String) extends InternalBakerEvent

  // when an actor is created
  case class ActorCreated(recipeId: String, processId: String, createdDateTime: Long) extends InternalBakerEvent


  def transitionForRuntimeEvent(runtimeEvent: RuntimeEvent, compiledRecipe: CompiledRecipe): Transition[_, _] =
    compiledRecipe.petriNet.transitions.findByLabel(runtimeEvent.name).getOrElse {
      throw new IllegalArgumentException(s"No such event known in recipe: $runtimeEvent")
    }

  def createFireTransitionCmd(recipe: CompiledRecipe, processId: String, runtimeEvent: RuntimeEvent, correlationId: Option[String]): FireTransition = {
    require(runtimeEvent != null, "Event can not be null")
    val t: Transition[_, _] = transitionForRuntimeEvent(runtimeEvent, recipe)

    FireTransition(t.id, runtimeEvent, correlationId)
  }

  private val strategy: Strategy = Strategy.fromCachedDaemonPool("Baker.CachedThreadPool")
}

class ProcessIndex(cleanupInterval: FiniteDuration = 1 minute,
                   processIdleTimeout: Option[FiniteDuration],
                   configuredEncryption: Encryption,
                   interactionManager: InteractionManager,
                   recipeManager: ActorRef) extends PersistentActor with ActorLogging {

  private val index: mutable.Map[String, ActorMetadata] = mutable.Map[String, ActorMetadata]()
  private val recipeCache: mutable.Map[String, CompiledRecipe] = mutable.Map[String, CompiledRecipe]()

  import context.dispatcher

  context.system.scheduler.schedule(cleanupInterval, cleanupInterval, context.self, CheckForProcessesToBeDeleted)

  def updateCache() = {
    // TODO this is a synchronous ask on an actor which is considered bad practice, alternative?
    val futureResult = recipeManager.ask(GetAllRecipes)(5 second).mapTo[AllRecipes]
    val allRecipes = Await.result(futureResult, 5 second)
    recipeCache ++= allRecipes.compiledRecipes
  }

  def getCompiledRecipe(recipeId: String): Option[CompiledRecipe] =
    recipeCache.get(recipeId) match {
      case None => {
        updateCache()
        recipeCache.get(recipeId)
      }
      case Some(compiledRecipe) => Some(compiledRecipe)
    }

  def getOrCreateProcessActor(processId: String): ActorRef =
    context.child(processId).getOrElse(createProcessActor(processId))

  def createProcessActor(processId: String): ActorRef = {
    val compiledRecipe: CompiledRecipe = getCompiledRecipe(index(processId).recipeId).get
    createProcessActor(processId, compiledRecipe)
  }

  def createProcessActor(processId: String, compiledRecipe: CompiledRecipe): ActorRef = {
    val petriNetRuntime: PetriNetRuntime[Place, Transition, ProcessState, RuntimeEvent] =
      new RecipeRuntime(compiledRecipe.name, interactionManager)

    val processActorProps =
      Util.recipePetriNetProps(compiledRecipe.name, compiledRecipe.petriNet, petriNetRuntime,
        ProcessInstance.Settings(
          evaluationStrategy = strategy,
          encryption = configuredEncryption,
          idleTTL = processIdleTimeout))

    val processActor = context.actorOf(processActorProps, name = processId)
    context.watch(processActor)
    processActor
  }

  def shouldDelete(meta: ActorMetadata): Boolean = {
    meta.processStatus != Deleted &&
      getCompiledRecipe(meta.recipeId)
        .flatMap(_.retentionPeriod)
        .exists { p => meta.createdDateTime + p.toMillis < System.currentTimeMillis() }
  }

  def isDeleted(meta: ActorMetadata): Boolean =
    meta.processStatus == Deleted


  def deleteProcess(processId: String): Unit = {
    persist(ActorDeleted(processId)) { _ =>
      val meta = index(processId)
      index.update(processId, index(processId).copy(processStatus = Deleted))
    }
  }

  override def receiveCommand: Receive = {
    case CheckForProcessesToBeDeleted =>
      val toBeDeleted = index.values.filter(shouldDelete)
      if (toBeDeleted.nonEmpty)
        log.debug(s"Deleting processes: {}", toBeDeleted.mkString(","))

      toBeDeleted.foreach(meta => getOrCreateProcessActor(meta.processId) ! Stop(delete = true))

    case Terminated(actorRef) =>
      val processId = actorRef.path.name
      log.debug(s"Actor terminated: $actorRef")

      index.get(processId) match {
        case Some(meta) if shouldDelete(meta) =>
          deleteProcess(processId)
        case Some(meta) if isDeleted(meta) =>
          log.warning(s"Received Terminated message for already deleted process: ${meta.processId}")
        case Some(_) =>
          persist(ActorPassivated(processId)) { _ => }
        case None =>
          log.warning(s"Received Terminated message for non indexed actor: $actorRef")
      }

    case CreateProcess(recipeId, processId) =>
      context.child(processId) match {
        case None if !index.contains(processId) =>
          val created = System.currentTimeMillis()
          persist(ActorCreated(recipeId, processId, created)) { _ =>

            getCompiledRecipe(recipeId) match {
              case Some(compiledRecipe) =>
                val initialize = Initialize(ProcessInstanceProtocol.marshal(compiledRecipe.initialMarking), ProcessState(processId, Map.empty, List.empty))
                createProcessActor(processId, compiledRecipe).forward(initialize)
                val actorMetadata = ActorMetadata(recipeId, processId, created, Active)
                index += processId -> actorMetadata
              case None => sender() ! NoRecipeFound(recipeId)
            }
          }
        case _ if isDeleted(index(processId)) => sender() ! ProcessDeleted(processId)
        case _ => sender() ! ProcessAlreadyInitialized(processId)
      }

    case ProcessEvent(processId: String, eventToFire: RuntimeEvent, correlationId) =>
      //Forwards the event message to the Actor if its in the Receive period for the compiledRecipe
      def forwardEventIfInReceivePeriod(actorRef: ActorRef, compiledRecipe: CompiledRecipe) = {
        val cmd = createFireTransitionCmd(compiledRecipe, processId, eventToFire, correlationId)
        compiledRecipe.eventReceivePeriod match {
          case Some(receivePeriod) =>
            index.get(processId).foreach { p =>
              if (System.currentTimeMillis() - p.createdDateTime > receivePeriod.toMillis) {
                sender() ! ReceivePeriodExpired(processId)
              }
              else
                actorRef.forward(cmd)
            }

          case None =>
            actorRef.forward(cmd)
        }
      }

      //Validates if the event is correct for the given
      //If not return a InvalidEvent message to the sender
      //Otherwise forwardEventIfInReceivePeriod
      def validateEventAvailableForRecipe(actorRef: ActorRef, compiledRecipe: CompiledRecipe) = {
        compiledRecipe.sensoryEvents.find(sensoryEvent => sensoryEvent.name == eventToFire.name) match {
          case None => sender() ! InvalidEvent(processId, s"No event with name '${eventToFire.name}' found in recipe '${compiledRecipe.name}'")
          case Some(sensoryEvent) =>
            //Check If the sensory event is valid for this recipe
            val eventValidationErrors = eventToFire.validateEvent(sensoryEvent)
            if (eventValidationErrors.nonEmpty)
              sender() ! InvalidEvent(processId, s"Invalid event: " + eventValidationErrors.mkString(","))
            else {
              forwardEventIfInReceivePeriod(actorRef, compiledRecipe)
            }
        }
      }

      //Handles the event, assumes the process is created
      def handleEventWithActor(actorRef: ActorRef) = {
        index.get(processId) match {
          case Some(actorMetadata) =>
            val recipeId = actorMetadata.recipeId
            getCompiledRecipe(recipeId).foreach { compiledRecipe: CompiledRecipe =>
              validateEventAvailableForRecipe(actorRef, compiledRecipe)
            }
          case None => sender() ! ProcessUninitialized(processId)
        }
      }

      //Check if the process has a active actor
      //If not check if it is available and start
      //If not return a Uninitialized message
      context.child(processId) match {
        case None if !index.contains(processId) => sender() ! ProcessUninitialized(processId)
        case None if isDeleted(index(processId)) => sender() ! ProcessDeleted(processId)
        case None =>
          persist(ActorActivated(processId)) { _ =>
            handleEventWithActor(createProcessActor(processId))
          }
        case Some(actorRef) => handleEventWithActor(actorRef)
      }

    case GetProcessState(processId) =>
      context.child(processId) match {
        case None if !index.contains(processId) => sender() ! ProcessUninitialized(processId)
        case None if isDeleted(index(processId)) => sender() ! ProcessDeleted(processId)
        case None if index.contains(processId) =>
          persist(ActorActivated(processId)) {
            _ =>
              createProcessActor(processId).forward(ProcessInstanceProtocol.GetState)
          }
        case Some(actorRef) => actorRef.forward(ProcessInstanceProtocol.GetState)
      }

    case GetCompiledRecipe(processId) =>
      index.get(processId) match {
        case Some(processMetadata) if isDeleted(processMetadata) => sender() ! ProcessDeleted(processId)
        case Some(processMetadata) =>
          getCompiledRecipe(processMetadata.recipeId) match {
            case Some(compiledRecipe) => sender() ! RecipeFound(compiledRecipe)
            case None => sender() ! ProcessUninitialized(processId)
          }
        case None => sender() ! ProcessUninitialized(processId)
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
      index.update(processId, index(processId).copy(processStatus = Deleted))
    case RecoveryCompleted =>
      actorsToBeCreated.foreach(id => createProcessActor(id))
  }

  override def persistenceId: String = self.path.name
}
