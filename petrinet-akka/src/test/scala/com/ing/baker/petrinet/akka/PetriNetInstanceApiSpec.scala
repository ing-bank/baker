package com.ing.baker.petrinet.akka

import akka.NotUsed
import akka.stream.ActorMaterializer
import akka.stream.scaladsl.Source
import akka.stream.testkit.scaladsl.TestSink
import akka.util.Timeout
import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol._
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.petrinet.dsl.colored._
import org.scalatest.Matchers._

import scala.concurrent.ExecutionContext
import scala.concurrent.duration._

class PetriNetInstanceApiSpec extends AkkaTestBase {

  implicit def materializer = ActorMaterializer()
  implicit def ec: ExecutionContext = system.dispatcher

  implicit val akkaTimout = Timeout(2 seconds)

  "The PetriNetInstanceApi" should {

    "Return a source of events resulting from a TransitionFired command" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ Added(1)),
        transition(automated = true)(_ ⇒ Added(2)),
        transition(automated = true)(_ ⇒ Added(3))
      )

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)

      actor ! Initialize(marshal(initialMarking), Set.empty)
      expectMsgClass(classOf[Initialized])

      val api = new PetriNetInstanceApi[Place, Transition, Set[Int]](petriNet, actor)
      val source: Source[TransitionResponse, NotUsed] = api.askAndCollectAll(FireTransition(1, ()))
      source.map(_.transitionId).runWith(TestSink.probe).request(3).expectNext(1, 2, 3)

    }

    "Return an error response when one transition fails but a later one does not (parallel situation)" in new StateTransitionNet[Unit, Unit] {

      implicit val waitTimeout: FiniteDuration = 2 seconds

      override val eventSourceFunction: Unit ⇒ Unit ⇒ Unit = s ⇒ e ⇒ s

      val p1 = Place[Unit](id = 1)
      val p2 = Place[Unit](id = 2)

      val t1 = nullTransition[Unit](id = 1, automated = false)
      val t2 = stateTransition(id = 2, automated = true)(_ ⇒ throw new RuntimeException("t2 failed!"))
      val t3 = stateTransition(id = 3, automated = true)(_ ⇒ ())

      val petriNet = createPetriNet[Unit](
        t1 ~> p1,
        t1 ~> p2,
        p1 ~> t2,
        p2 ~> t3
      )

      val actor = createPetriNetActor[Unit, Unit](petriNet, runtime)

      actor ! Initialize(marshal(Marking.empty[Place]), ())
      expectMsgClass(classOf[Initialized])

      val api = new PetriNetInstanceApi[Place, Transition, Unit](petriNet, actor)

      val results = api.askAndCollectAllSync(FireTransition(1, ()))

      results.size shouldBe 3
      results.exists(_.transitionId == t2.id) shouldBe true
      results.exists(_.transitionId == t3.id) shouldBe true
    }

    "Return an empty source when the petri net instance is 'uninitialized'" in new TestSequenceNet {

      override val sequence = Seq(
        transition()(_ ⇒ Added(1))
      )

      val actor = createPetriNetActor[Set[Int], Event](petriNet, runtime)
      val api = new PetriNetInstanceApi[Place, Transition, Set[Int]](petriNet, actor)
      val source: Source[TransitionResponse, NotUsed] = api.askAndCollectAll(FireTransition(1, ()))

      source.runWith(TestSink.probe[TransitionResponse]).expectSubscriptionAndComplete()

    }
  }
}