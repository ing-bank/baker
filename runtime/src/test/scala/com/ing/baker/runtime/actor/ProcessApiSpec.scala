package com.ing.baker.runtime.actor

import akka.NotUsed
import akka.actor.ActorSystem
import akka.stream.ActorMaterializer
import akka.stream.scaladsl.Source
import akka.stream.testkit.scaladsl.TestSink
import akka.testkit.{TestKit, TestProbe}
import akka.util.Timeout
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol._
import com.ing.baker.petrinet.runtime.ExceptionStrategy
import org.scalatest.Matchers._
import org.scalatest.WordSpecLike

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

class ProcessApiSpec extends TestKit(ActorSystem("ProcessApiSpec")) with WordSpecLike {

  implicit def materializer = ActorMaterializer()
  implicit def ec: ExecutionContext = system.dispatcher

  implicit val akkaTimout = Timeout(2 seconds)
  implicit val waitTimeout: FiniteDuration = 2 seconds

  "The ProcessApi" should {

    "Return a source of FireTransition responses resulting from a TransitionFired command" in  {

      val processProbe = TestProbe()

      val api = new ProcessApi(processProbe.ref)

      val fireCmd = FireTransition(1, ())

      val source: Source[Any, NotUsed] = api.askAndCollectAll(fireCmd)

      val runSource = source.map(_.asInstanceOf[TransitionResponse].transitionId).runWith(TestSink.probe)

      processProbe.expectMsg(fireCmd)

      processProbe.reply(TransitionFired(1, 1, Map.empty, Map.empty, null, Set(2, 3)))
      processProbe.reply(TransitionFired(2, 2, Map.empty, Map.empty, null, Set.empty))
      processProbe.reply(TransitionFired(3, 3, Map.empty, Map.empty, null, Set.empty))

      runSource.request(3).expectNext(1, 2, 3)
      runSource.expectComplete()
    }

    "Wait for the completion of all jobs even if one fails with TransitionFailed" in {

      val processProbe = TestProbe()

      val api = new ProcessApi(processProbe.ref)

      val fireCmd = FireTransition(1, ())

      val source: Source[Any, NotUsed] = api.askAndCollectAll(fireCmd)

      val runSource = source.map(_.asInstanceOf[TransitionResponse].transitionId).runWith(TestSink.probe)

      processProbe.expectMsg(fireCmd)

      processProbe.reply(TransitionFired(1, 1, Map.empty, Map.empty, null, Set(2, 3)))
      processProbe.reply(TransitionFailed(2, 2, Map.empty, null, "", ExceptionStrategy.BlockTransition))
      processProbe.reply(TransitionFired(3, 3, Map.empty, Map.empty, null, Set.empty))

      runSource.request(3).expectNext(1, 2, 3)
      runSource.expectComplete()
    }

    "Return an empty source when the petri net instance repsponds with Uninitialized" in {

      val processProbe = TestProbe()
      val api = new ProcessApi(processProbe.ref)
      val fireTransitionCmd = FireTransition(1, ())

      val source: Source[Any, NotUsed] = api.askAndCollectAll(fireTransitionCmd)
      val runSource = source.map(_.asInstanceOf[TransitionFired].transitionId).runWith(TestSink.probe)

      processProbe.expectMsg(fireTransitionCmd)
      processProbe.reply(Uninitialized(""))

      runSource.expectSubscriptionAndComplete()
    }
  }
}