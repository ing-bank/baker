package com.ing.baker.runtime.java_api

import java.util.UUID
import java.util.concurrent.TimeUnit

import akka.actor.ActorSystem
import com.ing.baker.runtime.core.Baker
import com.ing.baker.runtime.recipe.CompiledRecipe
import com.ing.baker.runtime.recipe.transitions.InteractionTransition
import com.typesafe.config.ConfigFactory

import scala.collection.JavaConverters._
import scala.concurrent.duration._

object JBaker {
  val defaultConfig =
    ConfigFactory.parseString("""
      |akka {
      |   persistence {
      |    journal.plugin = "inmemory-journal"
      |    snapshot-store.plugin = "inmemory-snapshot-store"
      |  }
      |}
      |
      |baker.actor.provider = "local"
    """.stripMargin)

    //TODO rewrite this to make the link between a description of the interaction instead of between class and implementation
  def mapInteractionToImplementation(
      interactionTransitions: Set[InteractionTransition[_]],
      implementations: java.util.List[Any]): java.util.Map[Class[_], Any] = {
    val interactionClasses: Set[Class[_]] =
      interactionTransitions.map(i => i.interactionClass)
    val implementationsSeq: scala.collection.mutable.Buffer[Any] = implementations.asScala
    val interactionMappings: Set[(Class[_], Any)] = interactionClasses.map {
      c =>
        c -> implementationsSeq.find(e => c.isAssignableFrom(e.getClass)).orNull
    }
    interactionMappings.toMap.filterNot { case (k, v) => v == null }.asJava
  }
}

//TODO do we want to accept the implementations as Any?
//It use to be of the Interaction type but now this is not possible since this is not known here
//Maybe we can create a InteractionImplementation trait and only accept classes of that type
class JBaker private (compiledRecipe: CompiledRecipe,
                      implementations: java.util.Map[Class[_], Any],
                      actorSystem: ActorSystem) {

  val interactionImplementations: Map[Class[_], () => Any] =
    implementations.asScala.toMap.mapValues { implementation => () =>
      implementation
    }

  val baker: Baker =
    new Baker(compiledRecipe = compiledRecipe, interactionImplementations, actorSystem = actorSystem)

  val defaultTimeout = 20 * 1000


  def this (jCompiledRecipe: JCompiledRecipe,
            implementations: java.util.Map[Class[_], Any],
            actorSystem: ActorSystem) =
    this(jCompiledRecipe.compiledRecipe, implementations, actorSystem)

//  TODO Enable this again once we can make the link again between implementation and class
  def this(compiledRecipe: CompiledRecipe,
           implementations: java.util.List[Any],
           actorSystem: ActorSystem) =
    this(compiledRecipe: CompiledRecipe, JBaker.mapInteractionToImplementation(compiledRecipe.interactionTransitions, implementations),
         actorSystem)

  def this(compiledRecipe: CompiledRecipe, implementations: java.util.List[Any]) =
    this(compiledRecipe, implementations, ActorSystem.apply("BakerActorSystem", JBaker.defaultConfig))

  /**
    * Attempts to gracefully shutdown the baker system.
    *
    * @param timeout The time to wait for the shard handover.
    */
  def shutdown(timeout: java.time.Duration) = baker.shutdown(Duration(timeout.toMillis, TimeUnit.MILLISECONDS))

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  def shutdown(): Unit = baker.shutdown()

  /**
    * This Bakes a new instance of the recipe
    * @param processId
    */
  def bake(processId: java.util.UUID): Unit =
    baker.bake(processId)

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This waits with returning until all steps that can be executed are executed by Baker
    *
    * @param processId the identifier of the process
    * @param event The event to fire
    * @return
    */
  def processEvent(processId: java.util.UUID, event: Object): Unit =
    processEventAsync(processId, event).confirmCompleted

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a JBaker response which is a future.
    * @param processId the identifier of the process
    * @param event The event to fire
    * @return
    */
  def processEventAsync(processId: java.util.UUID, event: Object): JBakerResponse = {
    implicit val executionContext = actorSystem.dispatcher

    val response = baker.handleEventAsync(processId, event)
    JBakerResponse(response.receivedFuture, response.completedFuture)
  }

  /**
    * Gets all the ingredients that are created in a given model
    * @param processId the identifier of the process
    * @param waitTimeoutMillis the maximum wait time
    * @return
    */
  def getIngredients(processId: java.util.UUID,
                     waitTimeoutMillis: Long): java.util.Map[String, Object] =
    baker
      .getIngredients(processId)(waitTimeoutMillis milliseconds)
      .asJava
      .asInstanceOf[java.util.Map[String, Object]]

  /**
    * Gets all the ingredients that are created in a given model
    * @param processId the identifier of the process
    * @return
    */
  def getIngredients(processId: java.util.UUID): java.util.Map[String, Object] =
    getIngredients(processId, defaultTimeout)

  /**
    * Get all events that have occurred for a given process
    * @param processId the identifier of the process
    * @param waitTimeoutMillis the maximum wait time
    * @return
    *
    */
  def getEvents(processId: UUID, waitTimeoutMillis: Long): EventList =
    new EventList(baker.events(processId)(waitTimeoutMillis milliseconds))

  /**
    * Get all events that have occurred for a given process
    * @param processId the identifier of the process
    * @return
    */
  def getEvents(processId: UUID): EventList = getEvents(processId, defaultTimeout)

  /**
    * Returns the compiled recipe
    * @return
    */
  def getCompiledRecipe(): JCompiledRecipe = JCompiledRecipe(compiledRecipe)

  /**
    * returns the visual state of the recipe in dot format
    * @param processId
    * @param waitTimeoutMillis
    * @return
    */
  def getVisualState(processId: java.util.UUID, waitTimeoutMillis: Long): String =
    baker.getVisualState(processId)(waitTimeoutMillis milliseconds)

  /**
    * returns the visual state of the recipe in dot format with a default timeout of 20 seconds
    * @param processId
    * @return
    */
  def getVisualState(processId: java.util.UUID): String =
    getVisualState(processId, defaultTimeout)

}
