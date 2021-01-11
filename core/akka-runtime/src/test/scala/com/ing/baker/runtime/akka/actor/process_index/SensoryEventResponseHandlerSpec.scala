package com.ing.baker.runtime.akka.actor.process_index

import akka.testkit.{TestDuration, TestProbe}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.akka.actor.AkkaTestBase
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.FireSensoryEventReaction.{NotifyBoth, NotifyOnEvent, NotifyWhenCompleted, NotifyWhenReceived}
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol.{FireSensoryEventRejection, ProcessEvent, ProcessEventCompletedResponse, ProcessEventReceivedResponse}
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{EventInstance, SensoryEventResult}
import com.ing.baker.types.{PrimitiveValue, Value}
import org.scalatest.matchers.should.Matchers._

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

class SensoryEventResponseHandlerSpec extends AkkaTestBase("SensoryEventResponseHandlerSpec")  {

  implicit val ec: ExecutionContext = system.dispatcher

  // Using dilated timeout to take into account the akka.test.timefactor config
  implicit val timeout = 2.seconds.dilated

  "The ProcessApi" should {

    import com.ing.baker.recipe.scaladsl._
    import Examples.webshop

    val webShopRecipe = RecipeCompiler.compileRecipe(webshop.webShopRecipe)

    "return a SensoryEventResult when processing the outcome of a sensory event with NotifyWhenCompleted reaction" in {
      val client = TestProbe()
      val sensoryEvent = EventInstance(webshop.orderPlaced.name, Map.empty)
      val cmd = ProcessEvent("", sensoryEvent, None, 1 second, NotifyWhenCompleted(waitForRetries = true))
      val handler = system.actorOf(SensoryEventResponseHandler(client.ref, cmd))
      val event1 = EventInstance("event1", Map("ingredient1" -> PrimitiveValue("value1")))
      val event2 = EventInstance("event2", Map("ingredient2" -> PrimitiveValue("value2")))
      val event3 = EventInstance("event3", Map("ingredient3" -> PrimitiveValue("value3")))
      val events = List(event1, event2, event3)
      val expectedEventNames = events.map(_.name)
      val expectedIngredients = events.foldLeft(Map.empty[String, Value])(_ ++ _.providedIngredients)
      handler ! webShopRecipe
      client.expectNoMessage(100.millis)
      handler ! TransitionFired(1, 1, None, Map.empty, Map.empty, Set(2, 3), event1)
      client.expectNoMessage(100.millis)
      handler ! TransitionFired(2, 2, None, Map.empty, Map.empty, Set.empty, event2)
      client.expectNoMessage(100.millis)
      handler ! TransitionFired(3, 3, None, Map.empty, Map.empty, Set.empty, event3)
      client.expectMsg(ProcessEventCompletedResponse(SensoryEventResult(SensoryEventStatus.Completed, expectedEventNames, expectedIngredients)))
    }

    "return a SensoryEventStatus when processing the outcome of a sensory event with NotifyWhenReceived reaction" in {
      val client = TestProbe()
      val sensoryEvent = EventInstance(webshop.orderPlaced.name, Map.empty)
      val cmd = ProcessEvent("", sensoryEvent, None, 1 second, NotifyWhenReceived)
      val handler = system.actorOf(SensoryEventResponseHandler(client.ref, cmd))
      val event1 = EventInstance("event1", Map("ingredient1" -> PrimitiveValue("value1")))
      val event2 = EventInstance("event2", Map("ingredient2" -> PrimitiveValue("value2")))
      val event3 = EventInstance("event3", Map("ingredient3" -> PrimitiveValue("value3")))
      handler ! webShopRecipe
      client.expectNoMessage(100.millis)
      handler ! TransitionFired(1, 1, None, Map.empty, Map.empty, Set(2, 3), event1)
      client.expectMsg(ProcessEventReceivedResponse(SensoryEventStatus.Received))
      handler ! TransitionFired(2, 2, None, Map.empty, Map.empty, Set.empty, event2)
      client.expectNoMessage(100.millis)
      handler ! TransitionFired(3, 3, None, Map.empty, Map.empty, Set.empty, event3)
      client.expectNoMessage(100.millis)
    }

    "return a SensoryEventResult AND a SensoryEventStatus when processing the outcome of a sensory event with NotifyBoth reaction" in {
      val clientReceived = TestProbe()
      val clientCompleted = TestProbe()
      val sensoryEvent = EventInstance(webshop.orderPlaced.name, Map.empty)
      val cmd = ProcessEvent("", sensoryEvent, None, 1 second, NotifyBoth(waitForRetries = true, clientCompleted.ref))
      val handler = system.actorOf(SensoryEventResponseHandler(clientReceived.ref, cmd))
      val event1 = EventInstance("event1", Map("ingredient1" -> PrimitiveValue("value1")))
      val event2 = EventInstance("event2", Map("ingredient2" -> PrimitiveValue("value2")))
      val event3 = EventInstance("event3", Map("ingredient3" -> PrimitiveValue("value3")))
      val events = List(event1, event2, event3)
      val expectedEventNames = events.map(_.name)
      val expectedIngredients = events.foldLeft(Map.empty[String, Value])(_ ++ _.providedIngredients)
      handler ! webShopRecipe
      clientReceived.expectNoMessage(100.millis)
      clientCompleted.expectNoMessage(100.millis)
      handler ! TransitionFired(1, 1, None, Map.empty, Map.empty, Set(2, 3), event1)
      clientReceived.expectMsg(ProcessEventReceivedResponse(SensoryEventStatus.Received))
      clientCompleted.expectNoMessage(100.millis)
      handler ! TransitionFired(2, 2, None, Map.empty, Map.empty, Set.empty, event2)
      clientReceived.expectNoMessage(100.millis)
      clientCompleted.expectNoMessage(100.millis)
      handler ! TransitionFired(3, 3, None, Map.empty, Map.empty, Set.empty, event3)
      clientReceived.expectNoMessage(100.millis)
      clientCompleted.expectMsg(ProcessEventCompletedResponse(SensoryEventResult(SensoryEventStatus.Completed, expectedEventNames, expectedIngredients)))
    }

    "return a SensoryEventResult when processing the outcome of a sensory event with NotifyOnEvent reaction" in {
      val client = TestProbe()
      val sensoryEvent = EventInstance(webshop.orderPlaced.name, Map.empty)
      val cmd = ProcessEvent("", sensoryEvent, None, 1 second, NotifyOnEvent(waitForRetries = true, "event2"))
      val handler = system.actorOf(SensoryEventResponseHandler(client.ref, cmd))
      val event1 = EventInstance("event1", Map("ingredient1" -> PrimitiveValue("value1")))
      val event2 = EventInstance("event2", Map("ingredient2" -> PrimitiveValue("value2")))
      val event3 = EventInstance("event3", Map("ingredient3" -> PrimitiveValue("value3")))
      val events = List(event1, event2, event3)
      val expectedEventNames = events.map(_.name).filterNot(_ == event3.name)
      val expectedIngredients = events.foldLeft(Map.empty[String, Value]) { case (acc, event) =>
        if(event.name == event3.name) acc
        else acc ++ event.providedIngredients
      }
      handler ! webShopRecipe
      client.expectNoMessage(100.millis)
      handler ! TransitionFired(1, 1, None, Map.empty, Map.empty, Set(2, 3), event1)
      client.expectNoMessage(100.millis)
      handler ! TransitionFired(2, 2, None, Map.empty, Map.empty, Set.empty, event2)
      client.expectMsg(ProcessEventCompletedResponse(SensoryEventResult(SensoryEventStatus.Completed, expectedEventNames, expectedIngredients)))
      handler ! TransitionFired(3, 3, None, Map.empty, Map.empty, Set.empty, event3)
      client.expectNoMessage(100.millis)
    }


    "wait for the completion of all jobs even if one fails with TransitionFailed" in {
      val client = TestProbe()
      val sensoryEvent = EventInstance(webshop.orderPlaced.name, Map.empty)
      val cmd = ProcessEvent("", sensoryEvent, None, 1 second, NotifyWhenCompleted(waitForRetries = true))
      val handler = system.actorOf(SensoryEventResponseHandler(client.ref, cmd))
      val event1 = EventInstance("event1", Map("ingredient1" -> PrimitiveValue("value1")))
      val event2 = EventInstance("event2", Map("ingredient2" -> PrimitiveValue("value2")))
      val event3 = EventInstance("event3", Map("ingredient3" -> PrimitiveValue("value3")))
      val events = List(event1, event2, event3)
      val expectedEventNames = events
        .map(_.name)
        .filterNot(_ == event2.name)
      val expectedIngredients = events
        .foldLeft(Map.empty[String, Value])(_ ++ _.providedIngredients)
        .filterNot(_._1 == "ingredient2")
      handler ! webShopRecipe
      client.expectNoMessage(100.millis)
      handler ! TransitionFired(1, 1, None, Map.empty, Map.empty, Set(2, 3), event1)
      client.expectNoMessage(100.millis)
      handler ! TransitionFailed(2, 2, None, Map.empty, null, "", ProcessInstanceProtocol.ExceptionStrategy.BlockTransition)
      client.expectNoMessage(100.millis)
      handler ! TransitionFired(3, 3, None, Map.empty, Map.empty, Set.empty, event3)
      client.expectMsg(ProcessEventCompletedResponse(SensoryEventResult(SensoryEventStatus.Completed, expectedEventNames, expectedIngredients)))
    }

    "forward rejections" in {

      def checkRejection(rejection: FireSensoryEventRejection): Unit = {
        val clientReceive = TestProbe()
        val clientComplete = TestProbe()
        val sensoryEvent = EventInstance(webshop.orderPlaced.name, Map.empty)
        val cmd = ProcessEvent("", sensoryEvent, None, 1 second, NotifyBoth(waitForRetries = true, clientComplete.ref))
        val handler = system.actorOf(SensoryEventResponseHandler(clientReceive.ref, cmd))
        handler ! webShopRecipe
        clientReceive.expectNoMessage(100.millis)
        handler ! rejection
        clientReceive.expectMsg(rejection)
        clientComplete.expectMsg(rejection)
      }

      checkRejection(FireSensoryEventRejection.RecipeInstanceDeleted(""))
      checkRejection(FireSensoryEventRejection.AlreadyReceived("", ""))
      checkRejection(FireSensoryEventRejection.FiringLimitMet(""))
      checkRejection(FireSensoryEventRejection.RecipeInstanceDeleted(""))
      checkRejection(FireSensoryEventRejection.NoSuchRecipeInstance(""))
      checkRejection(FireSensoryEventRejection.ReceivePeriodExpired(""))
    }
  }

}