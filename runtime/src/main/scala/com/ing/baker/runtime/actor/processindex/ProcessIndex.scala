package com.ing.baker.runtime.actor.processindex

import akka.actor.{ActorLogging, ActorRef, Props, Terminated}
import akka.pattern.ask
import akka.persistence.{PersistentActor, RecoveryCompleted}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.{Place, Transition}
import com.ing.baker.petrinet.runtime.PetriNetRuntime
import com.ing.baker.runtime.actor._
import com.ing.baker.runtime.actor.processindex.ProcessIndex._
import com.ing.baker.runtime.actor.processinstance.ProcessInstanceProtocol._
import com.ing.baker.runtime.actor.processinstance.{ProcessInstance, ProcessInstanceProtocol}
import com.ing.baker.runtime.actor.recipemanager.RecipeManager.{AllRecipes, GetAllRecipes, RecipeFound}
import com.ing.baker.runtime.actor.serialization.{AkkaObjectSerializer, Encryption}
import com.ing.baker.runtime.core.interations.InteractionManager
import com.ing.baker.runtime.core.{BakerException, ProcessState, RuntimeEvent}
import com.ing.baker.runtime.petrinet.RecipeRuntime
import fs2.Strategy

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration._


object ProcessIndex {

  def props(processInstanceStore: ProcessInstanceStore,
            cleanupInterval: FiniteDuration = 1 minute,
            processIdleTimeout: Option[FiniteDuration],
            configuredEncryption: Encryption,
            interactionManager: InteractionManager,
            recipeManager: ActorRef) =
    Props(new ProcessIndex(processInstanceStore, cleanupInterval, processIdleTimeout, configuredEncryption, interactionManager, recipeManager))

  case class ActorMetadata(recipeId: String, processId: String, createdDateTime: Long)

  // -- Messages

  sealed trait ProcessIndexMessage extends InternalBakerMessage

  case object CheckForProcessesToBeDeleted extends ProcessIndexMessage

  case class CreateProcess(recipeId: String, processId: String) extends ProcessIndexMessage

  case class HandleEvent(processId: String, event: RuntimeEvent) extends ProcessIndexMessage

  case class GetProcessState(processId: String) extends ProcessIndexMessage

  case class GetCompiledRecipe(processId: String) extends ProcessIndexMessage


  /**
    * Indicates that a process can no longer receive events because the configured period has expired.
    */
  case object ReceivePeriodExpired extends ProcessIndexMessage

  /**
    * @param msg error message for the request
    */
  case class InvalidEvent(msg: String) extends ProcessIndexMessage

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

  def createFireTransitionCmd(recipe: CompiledRecipe, processId: String, runtimeEvent: RuntimeEvent): FireTransition = {
    require(runtimeEvent != null, "Event can not be null")
    val t: Transition[_, _] = transitionForRuntimeEvent(runtimeEvent, recipe)
    FireTransition(t.id, runtimeEvent)
  }
}

class ProcessIndex(processInstanceStore: ProcessInstanceStore,
                   cleanupInterval: FiniteDuration = 1 minute,
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
          evaluationStrategy = Strategy.fromCachedDaemonPool("Baker.CachedThreadPool"),
          serializer = new AkkaObjectSerializer(context.system, configuredEncryption),
          idleTTL = processIdleTimeout))

    val processActor = context.actorOf(processActorProps, name = processId)
    context.watch(processActor)
    processActor
  }

  def shouldDelete(meta: ActorMetadata): Boolean =
    getCompiledRecipe(meta.recipeId).flatMap(_.retentionPeriod)
      .exists { p => meta.createdDateTime + p.toMillis < System.currentTimeMillis() }

  def deleteProcess(processId: String): Unit = {
    persist(ActorDeleted(processId)) { _ =>
      val meta = index(processId)
      processInstanceStore.remove(ProcessMetadata(meta.recipeId, meta.processId, meta.createdDateTime))
      index -= processId
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
                val initialize = Initialize(marshal(compiledRecipe.initialMarking), ProcessState(processId, Map.empty))
                createProcessActor(processId, compiledRecipe).forward(initialize)
                val actorMetadata = ActorMetadata(recipeId, processId, created)
                index += processId -> actorMetadata
                processInstanceStore.add(ProcessMetadata(recipeId, processId, created))
              case None => sender() ! RecipeNotAvailable(recipeId)
            }

          }
        case _ => sender() ! AlreadyInitialized
      }

    case HandleEvent(processId: String, event: RuntimeEvent) =>
      //Forwards the event message to the Actor if its in the Receive period for the compiledRecipe
      def forwardEventIfInReceivePeriod(actorRef: ActorRef, compiledRecipe: CompiledRecipe) = {
        val cmd = createFireTransitionCmd(compiledRecipe, processId, event)
        compiledRecipe.eventReceivePeriod match {
          case Some(receivePeriod) =>
            index.get(processId).foreach { p =>
              if (System.currentTimeMillis() - p.createdDateTime > receivePeriod.toMillis) {
                sender() ! ReceivePeriodExpired
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
        compiledRecipe.sensoryEvents.find(_.name.equals(event.name)) match {
          case None => sender() ! InvalidEvent(s"No event with name '${event.name}' found in recipe '${compiledRecipe.name}'")
          case Some(sensoryEvent) => {
            //Check If the sensory event is valid for this recipe
            val eventValidationErrors = event.validateEvent(sensoryEvent)
            if (eventValidationErrors.nonEmpty)
              sender() ! InvalidEvent(s"Invalid event: " + eventValidationErrors.mkString(","))
            else {
              forwardEventIfInReceivePeriod(actorRef, compiledRecipe)
            }
          }
        }
      }

      //Handles the event, assumes the process is created
      def HandleEventWithActor(actorRef: ActorRef) = {
        val recipeId = index.get(processId) match {
          case Some(actorMetadata) =>
            val recipeId = actorMetadata.recipeId
            getCompiledRecipe(recipeId).foreach { compiledRecipe: CompiledRecipe =>
              validateEventAvailableForRecipe(actorRef, compiledRecipe)
            }
          case None => sender() ! Uninitialized(processId)
        }
      }

      //Check if the process has a active actor
      //If not check if it is available and start
      //If not return a Uninitialized message
      context.child(processId) match {
        case Some(actorRef) => HandleEventWithActor(actorRef)
        case None if index.contains(processId) =>
          persist(ActorActivated(processId)) { _ =>
            HandleEventWithActor(createProcessActor(processId))
          }
        case None => sender() ! Uninitialized(processId)
      }

    case GetProcessState(processId) =>
      context.child(processId) match {
        case Some(actorRef) => actorRef.forward(ProcessInstanceProtocol.GetState)
        case None if index.contains(processId) =>
          persist(ActorActivated(processId)) {
            _ =>
              createProcessActor(processId).forward(ProcessInstanceProtocol.GetState)
          }
        case None => sender() ! Uninitialized(processId)
      }

    case GetCompiledRecipe(processId) =>
      index.get(processId) match {
        case Some(processMetadata) =>
          getCompiledRecipe(processMetadata.recipeId) match {
            case Some(compiledRecipe) => sender() ! RecipeFound(compiledRecipe)
            case None => sender() ! Uninitialized(processId)
          }
        case None => sender() ! Uninitialized(processId)
      }
    case cmd =>
      log.error(s"Unrecognized command $cmd")
  }

  // This Set holds all the actor ids to be created again after the recovery completed
  private val actorsToBeCreated: mutable.Set[String] = mutable.Set.empty

  override def receiveRecover: Receive = {
    case ActorCreated(recipeId, processId, createdTime) =>
      index += processId -> ActorMetadata(recipeId, processId, createdTime)
      actorsToBeCreated += processId
    case ActorPassivated(processId) =>
      actorsToBeCreated -= processId
    case ActorActivated(processId) =>
      actorsToBeCreated += processId
    case ActorDeleted(processId) =>
      actorsToBeCreated -= processId
      index -= processId
    case RecoveryCompleted =>
      actorsToBeCreated.foreach(id => createProcessActor(id))
      index.values.foreach(p => processInstanceStore.add(ProcessMetadata(p.recipeId, p.processId, p.createdDateTime)))
  }

  override def persistenceId: String = self.path.name
}
