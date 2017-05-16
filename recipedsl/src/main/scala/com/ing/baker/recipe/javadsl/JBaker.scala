package com.ing.baker.recipe.javadsl

import java.util.UUID
import java.util.concurrent.TimeUnit

import akka.actor.ActorSystem
import com.ing.baker.core._
import com.ing.baker.java_api.JBaker._
import com.ing.baker.recipe.common.{Interaction, InteractionDescriptor}
import com.typesafe.config.ConfigFactory

import scala.collection.JavaConverters._
import scala.collection.mutable
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

  def mapInteractionToImplementation(
      interactions: java.util.List[InteractionDescriptor[_]],
      implementations: java.util.List[Interaction]): java.util.Map[Class[_], Interaction] = {
    val interactionClasses: mutable.Buffer[Class[_]] =
      interactions.asScala.map(i => i.interactionClass)
    val implementationsSeq: mutable.Buffer[Interaction] = implementations.asScala
    val interactionMappings: mutable.Buffer[(Class[_], Interaction)] = interactionClasses.map {
      c =>
        c -> implementationsSeq.find(e => c.isAssignableFrom(e.getClass)).orNull
    }
    interactionMappings.toMap.filterNot { case (k, v) => v == null }.asJava
  }
}

class JBaker private (jRecipe: JRecipe,
                      implementations: java.util.Map[Class[_], Interaction],
                      actorSystem: ActorSystem) {

  val interactionImplementations: Map[Class[_], () => Interaction] =
    implementations.asScala.toMap.mapValues { implementation => () =>
      implementation
    }

  val baker: Baker =
    new Baker(recipe = jRecipe, interactionImplementations, actorSystem = actorSystem)

  val defaultTimeout = 20 * 1000

  def this(jRecipe: JRecipe,
           implementations: java.util.List[Interaction],
           actorSystem: ActorSystem) =
    this(jRecipe,
         mapInteractionToImplementation(jRecipe.getInteractions, implementations),
         actorSystem)

  def this(jRecipe: JRecipe, implementations: java.util.List[Interaction]) =
    this(jRecipe, implementations, ActorSystem.apply("BakerActorSystem", JBaker.defaultConfig))

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
  def getCompiledRecipe(): JCompiledRecipe = jRecipe.compileRecipe

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
