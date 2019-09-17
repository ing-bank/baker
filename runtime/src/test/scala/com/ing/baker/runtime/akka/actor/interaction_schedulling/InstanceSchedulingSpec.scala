package com.ing.baker.runtime.akka.actor.interaction_schedulling

import akka.actor.{ActorRef, ActorSystem}
import akka.testkit.{ImplicitSender, TestKit}
import com.ing.baker.runtime.akka.actor.interaction_schedulling.ProtocolInteractionExecution.InstanceExecutedSuccessfully
import com.ing.baker.runtime.scaladsl.IngredientInstance
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.baker.types.{CharArray, PrimitiveValue}
import com.typesafe.config.{Config, ConfigFactory}
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll, Matchers, WordSpecLike}
import org.scalatest.concurrent.Eventually
import org.scalatest.mockito.MockitoSugar

import scala.concurrent.Future

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

  import system.dispatcher

  val recipeName: String = "TestRecipe"

  val interaction: InteractionInstance =
    InteractionInstance(
      "TestInstance",
      Seq(CharArray),
      ingredients => Future (Some {
        val computed = PrimitiveValue(ingredients.head.value.as[String].toUpperCase())
        EventInstance("TestDone", Map("upper" -> computed))
      })
    )

  val jobs: List[String] =
    List.fill(10000)("hello")

  def buildAgents(): List[ActorRef] =
    List(
      system.actorOf(InteractionAgent(recipeName, interaction)),
      system.actorOf(InteractionAgent(recipeName, interaction))
    )

  def buildMandated(job: String, manager: ActorRef): ActorRef =
    system.actorOf(QuestMandated(manager, Seq(IngredientInstance("test-ingredient", PrimitiveValue(job))), recipeName, interaction.name))

  "The Instance scheduling protocol" should {
    "simple run success" in {
      buildAgents()
      jobs.foreach(buildMandated(_, self))
      buildAgents()
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
