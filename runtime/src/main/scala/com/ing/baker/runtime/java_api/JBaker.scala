package com.ing.baker.runtime.java_api

import java.util.concurrent.TimeUnit

import akka.actor.ActorSystem
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.core._

import scala.concurrent.duration._
import scala.collection.JavaConverters._

class JBaker (
              actorSystem: ActorSystem) {

  def this() = this(ActorSystem("BakerActorSystem"))

  val baker: Baker = new Baker()(actorSystem)

  def addRecipe(compiledRecipe: CompiledRecipe): JRecipeHandler = new JRecipeHandler(baker.addRecipe(compiledRecipe))(actorSystem)

  /**
    * Adds a single interaction implementation to baker.
    *
    * @param implementation The implementation that should be added.
    */
  def addImplementation(implementation: AnyRef): Unit = baker.addInteractionImplementation(implementation)

  /**
    * Adds all the provided interaction implementations to baker.
    *
    * @param implementations An iterable of implementations that should be added.
    */
  def addImplementations(implementations: java.lang.Iterable[AnyRef]) = implementations.asScala.foreach(addImplementation)

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
    * Return the handler for a specific recipe
    *
    * @param name
    * @return
    */
  def getRecipeHandler(name: String): JRecipeHandler = new JRecipeHandler(baker.getRecipeHandler(name))(actorSystem)
}
