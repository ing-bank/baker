package com.ing.baker.runtime.actor.process_index

import akka.NotUsed
import akka.actor.ActorSystem
import akka.stream.ActorMaterializer
import akka.stream.scaladsl.Source
import akka.stream.testkit.TestSubscriber
import akka.stream.testkit.scaladsl.TestSink
import akka.testkit.{TestDuration, TestKit, TestProbe}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol.ProcessEvent
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.core.RuntimeEvent
import com.typesafe.config.{Config, ConfigFactory}
import org.scalatest.Matchers._
import org.scalatest.WordSpecLike

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

object ProcessEventActorSpec {
  val config: Config = ConfigFactory.parseString(
    """
      |akka.persistence.journal.plugin = "inmemory-journal"
      |akka.persistence.snapshot-store.plugin = "inmemory-snapshot-store"
      |akka.test.timefactor = 3.0
    """.stripMargin)
}

class ProcessEventActorSpec extends TestKit(ActorSystem("ProcessApiSpec", ProcessEventActorSpec.config)) with WordSpecLike {

  implicit val materializer = ActorMaterializer()
  implicit val ec: ExecutionContext = system.dispatcher

  // Using dilated timeout to take into account the akka.test.timefactor config
  implicit val timeout = 2.seconds.dilated

  "The ProcessApi" should {

    import com.ing.baker.recipe.scaladsl._
    import Examples.webshop

    val webShopRecipe = RecipeCompiler.compileRecipe(webshop.webShopRecipe)

    "return a source of FireTransition responses resulting from a TransitionFired command" in {

      val processProbe = TestProbe()

      val processEventCmd = ProcessEvent("", RuntimeEvent(webshop.orderPlaced.name, Seq.empty), None, true, 1 second)

      val source: Source[Any, NotUsed] = ProcessEventActor.processEvent(processProbe.ref, webShopRecipe, processEventCmd)

      val runSource: TestSubscriber.Probe[Long] = source.map(_.asInstanceOf[TransitionResponse].transitionId).runWith(TestSink.probe)

      processProbe.expectMsgPF() { case FireTransition(_, _, _) => }

      processProbe.reply(TransitionFired(1, 1, None, Map.empty, Map.empty, null, Set(2, 3), null))
      processProbe.reply(TransitionFired(2, 2, None, Map.empty, Map.empty, null, Set.empty, null))
      processProbe.reply(TransitionFired(3, 3, None, Map.empty, Map.empty, null, Set.empty, null))

      runSource.request(3).expectNext(1, 2, 3)
      runSource.expectComplete()
    }

    "wait for the completion of all jobs even if one fails with TransitionFailed" in {

      val processProbe = TestProbe()

      val processEventCmd = ProcessEvent("", RuntimeEvent(webshop.orderPlaced.name, Seq.empty), None, true, 1 second)

      val source: Source[Any, NotUsed] = ProcessEventActor.processEvent(processProbe.ref, webShopRecipe, processEventCmd)

      val runSource = source.map(_.asInstanceOf[TransitionResponse].transitionId).runWith(TestSink.probe)

      processProbe.expectMsgType[FireTransition]

      processProbe.reply(TransitionFired(1, 1, None, Map.empty, Map.empty, null, Set(2, 3), null))
      processProbe.reply(TransitionFailed(2, 2, None, Map.empty, null, "", ProcessInstanceProtocol.ExceptionStrategy.BlockTransition))
      processProbe.reply(TransitionFired(3, 3, None, Map.empty, Map.empty, null, Set.empty, null))

      runSource.request(3).expectNext(1, 2, 3)
      runSource.expectComplete()
    }

    "return the msg when the petrinet instance responds with the error scenario response messages" in {

      check(ProcessInstanceProtocol.Uninitialized("someId"))
      check(ProcessInstanceProtocol.TransitionNotEnabled(123, "some reason"))

      def check(msg: Any) = {
        val processProbe = TestProbe()
        val processEventCmd = ProcessEvent("", RuntimeEvent(webshop.orderPlaced.name, Seq.empty), None, true, 1 second)

        val source: Source[Any, NotUsed] = ProcessEventActor.processEvent(processProbe.ref, webShopRecipe, processEventCmd)
        val runSource: TestSubscriber.Probe[Any] = source.runWith(TestSink.probe)

        processProbe.expectMsgType[FireTransition]
        processProbe.reply(msg)

        runSource.request(1).expectNext(msg)
      }
    }
  }
}