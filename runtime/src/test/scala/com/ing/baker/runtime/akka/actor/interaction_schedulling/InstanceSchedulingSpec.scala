package com.ing.baker.runtime.akka.actor.interaction_schedulling

import akka.actor.{ActorRef, ActorSystem}
import akka.testkit.{ImplicitSender, TestKit}
import akka.util.Timeout
import cats.effect.{IO, Timer}
import com.ing.baker.runtime.akka.actor.interaction_schedulling.ProtocolInteractionExecution.InstanceExecutedSuccessfully
import com.ing.baker.runtime.akka.actor.interaction_schedulling.QuestMandated.Start
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}
import com.ing.baker.types.{CharArray, PrimitiveValue}
import com.typesafe.config.{Config, ConfigFactory}
import org.scalatest.concurrent.Eventually
import org.scalatest.mockito.MockitoSugar
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll, Matchers, WordSpecLike}

import scala.concurrent.duration._

object InstanceSchedulingSpec {

  val config: Config = ConfigFactory.parseString(
    """
      |akka {
      |  actor {
      |    provider = "cluster"
      |  }
      |  remote {
      |    log-remote-lifecycle-events = off
      |    netty.tcp {
      |      hostname = "127.0.0.1"
      |      port = 2551
      |    }
      |  }
      |
      |  cluster {
      |    seed-nodes = ["akka.tcp://InstanceSchedulingSpec@127.0.0.1:2551"]
      |    auto-down-unreachable-after = 10s
      |  }
      |}
    """.stripMargin)
}

class InstanceSchedulingSpec extends TestKit(ActorSystem("InstanceSchedulingSpec", config = InstanceSchedulingSpec.config))
    with ImplicitSender
    with WordSpecLike
    with Matchers
    with BeforeAndAfterAll
    with BeforeAndAfter
    with MockitoSugar
    with Eventually {

  implicit val timer: Timer[IO] = IO.timer(system.dispatcher)

  val recipeName: String = "TestRecipe"

  def work(str: String): IO[String] =
    IO.sleep(1 millis).map(_ => str.toUpperCase())

  val interaction: InteractionInstance =
    InteractionInstance(
      "TestInstance",
      Seq(CharArray),
      ingredients =>
        work(ingredients.head.value.as[String]).map(res => {
          Some(EventInstance("TestDone", Map("upper" -> PrimitiveValue(res))))
        }).unsafeToFuture()
      )

  val jobs: List[String] =
    List.fill(1000)("hello")

  def buildAgents(): List[ActorRef] =
    List(
      system.actorOf(InteractionAgent(interaction)),
      system.actorOf(InteractionAgent(interaction))
    )

  def buildMandated(job: String, manager: ActorRef): ActorRef =
    system.actorOf(QuestMandated(Seq(IngredientInstance("test-ingredient", PrimitiveValue(job))), interaction.name, Timeout.durationToTimeout(10 seconds), Timeout.durationToTimeout(60 seconds)))

  "The Instance scheduling protocol" should {
    "simple run success" in {
      buildAgents()
      jobs.foreach(buildMandated(_, self) ! Start)
      receiveN(jobs.length).foreach { job =>
        job.asInstanceOf[InstanceExecutedSuccessfully] match {
          case InstanceExecutedSuccessfully(Some(EventInstance("TestDone", map))) =>
            map("upper").as[String] shouldBe "HELLO"
          case other =>
            fail(other + " is not a successful execution result")
        }
      }
    }
  }
}
