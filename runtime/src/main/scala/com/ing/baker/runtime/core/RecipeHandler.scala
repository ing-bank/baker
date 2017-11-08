package com.ing.baker.runtime.core

import java.util.concurrent.TimeoutException

import akka.NotUsed
import akka.actor.{Actor, ActorRef, ActorSystem, Props}
import akka.pattern.ask
import akka.persistence.query.scaladsl.{CurrentEventsByPersistenceIdQuery, CurrentPersistenceIdsQuery, PersistenceIdsQuery}
import akka.stream.ActorMaterializer
import akka.stream.scaladsl.{Sink, Source}
import akka.util.Timeout
import com.ing.baker.il.petrinet.{InteractionTransition, Place, Transition}
import com.ing.baker.il.{CompiledRecipe, EventType, RecipeVisualizer}
import com.ing.baker.petrinet.runtime.EventSourcing.{TransitionFailedEvent, TransitionFiredEvent}
import com.ing.baker.petrinet.runtime.ExceptionStrategy.Continue
import com.ing.baker.petrinet.runtime.PetriNetRuntime
import com.ing.baker.runtime.actor.ProcessInstanceProtocol.{AlreadyInitialized, FireTransition, GetState, Initialize, Initialized, InstanceState, Response, Uninitialized, marshal}
import com.ing.baker.runtime.actor._
import com.ing.baker.runtime.actor.serialization.{AkkaObjectSerializer, Encryption}
import com.ing.baker.runtime.core.Baker.toRuntimeEvent
import com.ing.baker.runtime.core.RecipeHandler._
import com.ing.baker.runtime.core.interations.InteractionManager
import com.ing.baker.runtime.petrinet.RecipeRuntime
import fs2.Strategy

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{Await, Future}

object RecipeHandler {
  def transitionForRuntimeEvent(runtimeEvent: RuntimeEvent, compiledRecipe: CompiledRecipe): Transition[_, _] =
    compiledRecipe.petriNet.transitions.findByLabel(runtimeEvent.name).getOrElse {
      throw new IllegalArgumentException(s"No such event known in recipe: $runtimeEvent")
    }

  def createEventMsg(recipe: CompiledRecipe, processId: String, runtimeEvent: RuntimeEvent) = {
    require(runtimeEvent != null, "Event can not be null")
    val t: Transition[_, _] = transitionForRuntimeEvent(runtimeEvent, recipe)
    BakerActorMessage(processId, FireTransition(t.id, runtimeEvent))
  }

  private def checkIfValidImplementationsProvided(interactionManager: InteractionManager, actions: Set[InteractionTransition[_]]): Set[String] = {
    actions.filterNot(interactionManager.hasInteractionImplementation)
      .map(s => s"No implementation provided for interaction: ${s.originalInteractionName}")
  }
}

class RecipeHandler(val compiledRecipe: CompiledRecipe,
                    interactionManager: InteractionManager,
                    configuredEncryption: Encryption,
                    actorIdleTimeout: Option[FiniteDuration],
                    bakeTimeout: FiniteDuration,
                    readJournal: CurrentEventsByPersistenceIdQuery with PersistenceIdsQuery with CurrentPersistenceIdsQuery,
                    bakerActorProvider: BakerActorProvider)
                   (implicit val actorSystem: ActorSystem,
                    implicit val materializer: ActorMaterializer) {

  private val implementationErrors = checkIfValidImplementationsProvided(interactionManager, compiledRecipe.interactionTransitions)
  if (implementationErrors.nonEmpty)
    throw new BakerException(implementationErrors.mkString(", "))

  if (compiledRecipe.validationErrors.nonEmpty)
    throw new RecipeValidationException(compiledRecipe.validationErrors.mkString(", "))

  val petriNetRuntime: PetriNetRuntime[Place, Transition, ProcessState, RuntimeEvent] =
    new RecipeRuntime(compiledRecipe.name, interactionManager)

  val petriNetInstanceActorProps =
    Util.recipePetriNetProps(compiledRecipe.name, compiledRecipe.petriNet, petriNetRuntime,
      ProcessInstance.Settings(
        evaluationStrategy = Strategy.fromCachedDaemonPool("Baker.CachedThreadPool"),
        serializer = new AkkaObjectSerializer(actorSystem, configuredEncryption),
        idleTTL = actorIdleTimeout))

  val (recipeManagerActor: ActorRef, recipeMetadata: RecipeMetadata) = bakerActorProvider.createRecipeActors(
    compiledRecipe, petriNetInstanceActorProps)

  private val petriNetApi = new ProcessApi(recipeManagerActor)

  /**
    * Creates a process instance of this recipe.
    *
    * @param processId The process identifier
    */
  def bake(processId: String): ProcessState =
    Await.result(bakeAsync(processId), bakeTimeout)

  /**
    * Asynchronously creates an instance of the  process using the recipe.
    *
    * @param processId The process identifier
    * @return A future of the initial process state.
    */
  def bakeAsync(processId: String): Future[ProcessState] = {
    implicit val askTimeout = Timeout(bakeTimeout)

    val msg = Initialize(marshal(compiledRecipe.initialMarking), ProcessState(processId, Map.empty))
    val initializeFuture = (recipeManagerActor ? BakerActorMessage(processId, msg)).mapTo[Response]

    val eventualState = initializeFuture.map {
      case msg: Initialized => msg.state.asInstanceOf[ProcessState]
      case AlreadyInitialized => throw new IllegalArgumentException(s"Process with id '$processId' for recipe '${compiledRecipe.name}' already exists.")
      case msg@_ => throw new BakerException(s"Unexpected message: $msg")
    }

    eventualState
  }

  /**
    * Notifies Baker that an event has happened and waits until all the actions which depend on this event are executed.
    *
    * @param processId The process identifier
    * @param event     The event object
    */
  def handleEvent(processId: String, event: Any)(implicit timeout: FiniteDuration): SensoryEventStatus = {
    handleEventAsync(processId, event).confirmCompleted()
  }

  /**
    * Fires an event to baker for a process.
    *
    * This call is fire and forget: If  nothing is done
    * with the response object you NO guarantee that the event is received the process instance.
    */
  def handleEventAsync(processId: String, event: Any)(implicit timeout: FiniteDuration): BakerResponse = {

    val runtimeEvent: RuntimeEvent = event match {
      case runtimeEvent:  RuntimeEvent => runtimeEvent
      case _ => Baker.eventExtractor.extractEvent(event)
    }

    val sensoryEvent: EventType = compiledRecipe.sensoryEvents
      .find(_.name.equals(runtimeEvent.name))
      .getOrElse(throw new IllegalArgumentException(s"No event with name '${runtimeEvent.name}' found in the recipe"))

    val eventValidationErrors = runtimeEvent.validateEvent(sensoryEvent)

    if (eventValidationErrors.nonEmpty)
      throw new IllegalArgumentException("Invalid event: " + eventValidationErrors.mkString(","))

    val msg = createEventMsg(compiledRecipe, processId, runtimeEvent)
    val source = petriNetApi.askAndCollectAll(msg, waitForRetries = true)(timeout)
    new BakerResponse(processId, source)
  }

  /**
    * Synchronously returns all events that occurred for a process.
    */
  def events(processId: String)(implicit timeout: FiniteDuration): Seq[RuntimeEvent] = {
    val futureEventSeq = eventsAsync(processId).runWith(Sink.seq)
    Await.result(futureEventSeq, timeout)
  }

  /**
    * Returns a Source of baker events for a process.
    *
    * @param processId The process identifier.
    * @return The source of events.
    */
  def eventsAsync(processId: String): Source[RuntimeEvent, NotUsed] = {
    ProcessQuery
      .eventsForInstance[Place, Transition, ProcessState, RuntimeEvent](compiledRecipe.name, processId.toString, compiledRecipe.petriNet, configuredEncryption, readJournal, petriNetRuntime.eventSourceFn)
      .collect {
        case (_, TransitionFiredEvent(_, _, _, _, _, _, runtimeEvent: RuntimeEvent))
          if runtimeEvent != null && compiledRecipe.allEvents.exists(e => e.name equals runtimeEvent.name) => runtimeEvent
      }
  }

  /**
    * Returns the process state.
    *
    * @param processId The process identifier
    * @return The process state.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getProcessState(processId: String)(implicit timeout: FiniteDuration): ProcessState =
  Await.result(getProcessStateAsync(processId), timeout)

  def getProcessStateAsync(processId: String)(implicit timeout: FiniteDuration): Future[ProcessState] = {
    recipeManagerActor
      .ask(BakerActorMessage(processId, GetState))(Timeout.durationToTimeout(timeout))
      .flatMap {
        case instanceState: InstanceState => Future.successful(instanceState.state.asInstanceOf[ProcessState])
        case Uninitialized(id) => Future.failed(new NoSuchProcessException(s"No such process with: $id"))
        case msg => Future.failed(new BakerException(s"Unexpected actor response message: $msg"))
      }
  }

  /**
    * Returns all provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return The provided ingredients.
    */
  @throws[NoSuchProcessException]("When no process exists for the given id")
  @throws[TimeoutException]("When the request does not receive a reply within the given deadline")
  def getIngredients(processId: String)(implicit timeout: FiniteDuration): Map[String, Any] =
  getProcessState(processId).ingredients

  /**
    * Returns a future of all the provided ingredients for a given process id.
    *
    * @param processId The process id.
    * @return A future of the provided ingredients.
    */
  def getIngredientsAsync(processId: String)(implicit timeout: FiniteDuration): Future[Map[String, Any]] = {
    getProcessStateAsync(processId).map(_.ingredients)
  }

  /**
    * Returns the visual state (.dot) for a given process.
    *
    * @param processId The process identifier.
    * @param timeout   How long to wait to retreive the process state.
    * @return A visual (.dot) representation of the process state.
    */
  def getVisualState(processId: String)(implicit timeout: FiniteDuration): String = {
    RecipeVisualizer.visualiseCompiledRecipe(
      compiledRecipe,
      eventNames = this.events(processId).map(_.name).toSet,
      ingredientNames = this.getIngredients(processId).keySet)
  }

  /**
    * Registers a listener to all runtime events.
    *
    * Note that the delivery guarantee is *AT MOST ONCE*. Do not use it for critical functionality
    */
  def registerEventListener(listener: EventListener): Boolean = {
    val subscriber = actorSystem.actorOf(Props(new Actor() {
      override def receive: Receive = {
        case ProcessInstanceEvent(processType, processId, event: TransitionFiredEvent[_, _, _]) if processType == compiledRecipe.name =>
          toRuntimeEvent(event).foreach(e => listener.processEvent(processId, e))
        case ProcessInstanceEvent(processType, processId, event: TransitionFailedEvent[_, _, _]) if processType == compiledRecipe.name =>
          event.exceptionStrategy match {
            case Continue(_, event: RuntimeEvent) =>
              listener.processEvent(processId, event)
            case _ =>
          }
        case _: ProcessInstanceEvent =>  // purposely ignored in order to not have unnecessary unhandled messages logged
      }
    }))
    actorSystem.eventStream.subscribe(subscriber.actorRef, classOf[ProcessInstanceEvent])
  }

  def allProcessMetadata: Set[ProcessMetadata] = recipeMetadata.getAll
}
