package com.ing.baker.runtime.model

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import com.ing.baker.runtime.catseffect.AsyncSupport
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.model.FireSensoryEventRejection.AlreadyReceived
import com.ing.baker.runtime.model.recipeinstance.RecipeInstanceConfig
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstanceDescriptor, RecipeInformation, RecipeInstanceMetadata, SensoryEventResult}
import com.ing.baker.types.PrimitiveValue
import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.should.Matchers

import scala.concurrent.duration.FiniteDuration

class RecipeInstanceManagerCallbackSpec extends AnyFunSpec with Matchers {

  private final class CallbackTestManager(
    emitter: (EventInstance => IO[Unit]) => IO[Either[FireSensoryEventRejection, Unit]]
  ) extends RecipeInstanceManager[IO] {

    override protected def store(newRecipeInstance: recipeinstance.RecipeInstance[IO])(implicit components: BakerComponents[IO]): IO[Unit] = IO.unit

    override protected def fetch(recipeInstanceId: String): IO[Option[RecipeInstanceStatus[IO]]] = IO.pure(None)

    override protected def fetchAll: IO[Map[String, RecipeInstanceStatus[IO]]] = IO.pure(Map.empty)

    override def remove(recipeInstanceId: String): IO[Unit] = IO.unit

    override def idleStop(recipeInstanceId: String): IO[Unit] = IO.unit

    override def getAllRecipeInstancesMetadata: IO[Set[RecipeInstanceMetadata]] = IO.pure(Set.empty)

    override def fireEventAndProcess(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])(onEvent: EventInstance => IO[Unit])(implicit components: BakerComponents[IO], async: AsyncSupport[IO]): IO[Either[FireSensoryEventRejection, Unit]] =
      emitter(onEvent)
  }

  private object NoopInteractionManager extends InteractionManager[IO] {
    override def listAll: IO[List[InteractionInstance[IO]]] = IO.pure(Nil)
  }

  private object NoopRecipeManager extends RecipeManager[IO] {
    override protected def store(compiledRecipe: com.ing.baker.il.CompiledRecipe, timestamp: Long): IO[Unit] = IO.unit

    override protected def fetchAll: IO[Map[String, com.ing.baker.runtime.common.RecipeRecord]] = IO.pure(Map.empty)

    override protected def fetch(recipeId: String): IO[Option[com.ing.baker.runtime.common.RecipeRecord]] = IO.pure(None)
  }

  private object NoopEventStream extends EventStream[IO] {
    override protected def fetchListeners: IO[List[com.ing.baker.runtime.scaladsl.BakerEvent => Unit]] = IO.pure(Nil)

    override def subscribe(listenerFunction: com.ing.baker.runtime.scaladsl.BakerEvent => Unit): IO[Unit] = IO.unit
  }

  private implicit val asyncSupport: AsyncSupport[IO] = AsyncSupport.fromIO

  private def componentsFor(manager: RecipeInstanceManager[IO]): BakerComponents[IO] =
    BakerComponents(
      interactions = NoopInteractionManager,
      recipeInstanceManager = manager,
      recipeManager = NoopRecipeManager,
      eventStream = NoopEventStream
    )

  private val inputEvent = EventInstance("Input", Map.empty)

  describe("RecipeInstanceManager callback processing") {

    it("aggregates fireEventAndResolveWhenCompleted from callback emissions") {
      val manager = new CallbackTestManager(onEvent =>
        for {
          _ <- onEvent(EventInstance("first", Map("a" -> PrimitiveValue("1"))))
          _ <- onEvent(EventInstance("second", Map("b" -> PrimitiveValue("2"))))
        } yield Right(())
      )
      implicit val components: BakerComponents[IO] = componentsFor(manager)

      val result = manager.fireEventAndResolveWhenCompleted("recipe-instance-1", inputEvent, None).unsafeRunSync()

      result.sensoryEventStatus shouldBe SensoryEventStatus.Completed
      result.eventNames shouldBe Seq("first", "second")
      result.ingredients.keySet shouldBe Set("a", "b")
    }

    it("returns the first matching snapshot in fireEventAndResolveOnEvent") {
      val manager = new CallbackTestManager(onEvent =>
        for {
          _ <- onEvent(EventInstance("before", Map("a" -> PrimitiveValue("1"))))
          _ <- onEvent(EventInstance("target", Map("b" -> PrimitiveValue("2"))))
          _ <- onEvent(EventInstance("after", Map("c" -> PrimitiveValue("3"))))
        } yield Right(())
      )
      implicit val components: BakerComponents[IO] = componentsFor(manager)

      val result = manager.fireEventAndResolveOnEvent("recipe-instance-2", inputEvent, "target", None).unsafeRunSync()

      result.sensoryEventStatus shouldBe SensoryEventStatus.Completed
      result.eventNames shouldBe Seq("before", "target")
      result.ingredients.keySet shouldBe Set("a", "b")
    }

    it("keeps vector compatibility for fireEventStream via callback wrapper") {
      val manager = new CallbackTestManager(onEvent =>
        for {
          _ <- onEvent(EventInstance("event-1", Map.empty))
          _ <- onEvent(EventInstance("event-2", Map.empty))
        } yield Right(())
      )
      implicit val components: BakerComponents[IO] = componentsFor(manager)

      val result = manager.fireEventStream("recipe-instance-3", inputEvent, None).unsafeRunSync()

      result shouldBe Right(Vector(EventInstance("event-1", Map.empty), EventInstance("event-2", Map.empty)))
    }

    it("maps callback rejection outcomes to sensory event status") {
      val manager = new CallbackTestManager(_ =>
        IO.pure(Left(AlreadyReceived("recipe-instance-4", "corr-1")))
      )
      implicit val components: BakerComponents[IO] = componentsFor(manager)

      val status = manager.fireEventAndResolveWhenReceived("recipe-instance-4", inputEvent, Some("corr-1")).unsafeRunSync()

      status shouldBe SensoryEventStatus.AlreadyReceived
    }
  }
}

