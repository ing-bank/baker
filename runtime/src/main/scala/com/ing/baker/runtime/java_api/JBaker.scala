package com.ing.baker.runtime.java_api

import java.util.UUID
import java.util.concurrent.TimeUnit

import akka.actor.ActorSystem
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.ProcessMetadata
import com.ing.baker.runtime.core.Baker

import scala.collection.JavaConverters._
import scala.concurrent.duration._

//TODO do we want to accept the implementations as Any?
//It use to be of the Interaction type but now this is not possible since this is not known here
//Maybe we can create a InteractionImplementation trait and only accept classes of that type
class JBaker (compiledRecipe: CompiledRecipe,
              implementations: java.util.List[AnyRef],
              actorSystem: ActorSystem) {

  def this(compiledRecipe: CompiledRecipe, implementations: java.util.List[AnyRef]) =
    this(compiledRecipe, implementations, ActorSystem("BakerActorSystem"))

  val interactionImplementations: Map[String, () => AnyRef] = Baker.implementationsToProviderMap(implementations.asScala)
  val baker: Baker = new Baker(compiledRecipe = compiledRecipe, implementations.asScala)(actorSystem = actorSystem)
  val defaultTimeout: Int = 20 * 1000

  /**
    * Attempts to gracefully shutdown the baker system.
    *
    * @param timeout The time to wait for the shard handover.
    */
  def shutdown(timeout: java.time.Duration): Unit = baker.shutdown(Duration(timeout.toMillis, TimeUnit.MILLISECONDS))

  /**
    * Attempts to gracefully shutdown the baker system.
    */
  def shutdown(): Unit = baker.shutdown()

  /**
    * This Bakes a new instance of the recipe
    * @param processId process id
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
  def processEvent(processId: java.util.UUID, event: Any): Unit =
    processEventAsync(processId, event).confirmCompleted

  /**
    * This fires the given event in the recipe for the process with the given processId
    * This returns a JBaker response which is a future.
    * @param processId the identifier of the process
    * @param event The event to fire
    * @return
    */
  def processEventAsync(processId: java.util.UUID, event: Any): JBakerResponse = {
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
  def getCompiledRecipe: CompiledRecipe = compiledRecipe

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

  def getAllProcessMetadata: java.util.Set[ProcessMetadata] =
    baker.allProcessMetadata.asJava
}
