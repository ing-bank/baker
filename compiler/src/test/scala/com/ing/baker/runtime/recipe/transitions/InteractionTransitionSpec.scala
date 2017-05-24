package com.ing.baker.runtime.recipe.transitions

import java.util.UUID

import com.ing.baker.recipe.javadsl.{FiresEvent, ProvidesIngredient}
import com.ing.baker.runtime.recipe.duplicates.RequiresIngredient
import com.ing.baker.runtime.recipe.ingredientExtractors.CompositeIngredientExtractor
import fs2._
import io.kagera.api.colored._
import org.scalatest._

object InteractionTransitionSpec {

  trait SimpleInteraction {
    @ProvidesIngredient("originalIngredient")
    def action1(@RequiresIngredient("overriddenName") arg1: String): Int
  }

  case object SimpleInteractionImpl extends SimpleInteraction {
    override def action1(arg1: String): Int = 10
  }

  case class TestEvent(msg: String)

  case class TransformedEvent(msg: String, s: Int)

  val eventTransformer            = (e: TestEvent) ⇒ TransformedEvent(e.msg, Integer.MAX_VALUE)
  val transformedEventTransformer = (e: TransformedEvent) ⇒ TestEvent(e.msg)

  trait SimpleInteractionThatTriggersEvent {
    @FiresEvent(oneOf = Array(classOf[TestEvent]))
    def aInteraction(@RequiresIngredient("overriddenName") message: String): TestEvent
  }

  case object InteractionThatTriggersAnEvent extends SimpleInteractionThatTriggersEvent {
    override def aInteraction(message: String): TestEvent =
      TestEvent(message)
  }
}

class InteractionTransitionSpec extends WordSpec with ShouldMatchers with GivenWhenThen {

  import InteractionTransitionSpec._

//  "InteractionTransition" should {
//    "succeed when calling apply method with right ingredient " in {
//
//      val interactionTransition: InteractionTransition[SimpleInteraction] =
//        InteractionTransition[SimpleInteraction](interactionClass = classOf[SimpleInteraction],
//                                                 interactionProvider = () => SimpleInteractionImpl,
//                                                 interactionMethod = "action1",
//                                                 interactionName = "action1",
//                                                 predefinedParameters = Map.empty,
//                                                 overriddenIngredientNames = Map.empty,
//                                                 maximumInteractionCount = None,
//                                                 overriddenOutputIngredientName = null,
//                                                 failureStrategy = InteractionFailureStrategy.BlockInteraction,
//                                                 ingredientExtractor = new CompositeIngredientExtractor() )
//
//      val f: (Marking, ProcessState, Unit) => Task[(Marking, AnyRef)] =
//        interactionTransition.apply(Map.empty, Map.empty)
//
//      val processState = ProcessState(UUID.randomUUID(), Map("overriddenName" -> "1"))
//
//      f(null, processState, Unit).unsafeValue().map(_._2) shouldEqual Some(10)
//    }
//
//    "succeed when calling apply method with overridden ingredient " in {
//
//      val ingredientName: String    = "overriddenName"
//      val newIngredientName: String = "overriddenName2"
//
//      val interactionTransition: InteractionTransition[SimpleInteraction] =
//        InteractionTransition[SimpleInteraction](interactionClass = classOf[SimpleInteraction],
//                                                 interactionProvider = () => SimpleInteractionImpl,
//                                                 interactionMethod = "action1",
//                                                 interactionName = "action1",
//                                                 predefinedParameters = Map.empty,
//                                                 overriddenIngredientNames =
//                                                   Map(ingredientName -> newIngredientName),
//                                                 maximumInteractionCount = None,
//                                                 overriddenOutputIngredientName = null,
//                                                 failureStrategy = InteractionFailureStrategy.BlockInteraction,
//                                                 ingredientExtractor = new CompositeIngredientExtractor())
//
//      val f: (Marking, ProcessState, Unit) => Task[(Marking, AnyRef)] =
//        interactionTransition.apply(Map.empty, Map.empty)
//      val processState = ProcessState(UUID.randomUUID(), Map(newIngredientName -> "1"))
//
//      f(null, processState, Unit).unsafeValue().map(_._2) shouldEqual Some(10)
//    }
//
//    "succeed when calling apply method and return the correct ingredient " in {
//
//      Given("a InteractionTransition")
//
//      val interactionTransition: InteractionTransition[SimpleInteraction] =
//        InteractionTransition[SimpleInteraction](interactionClass = classOf[SimpleInteraction],
//                                                 interactionProvider = () => SimpleInteractionImpl,
//                                                 interactionMethod = "action1",
//                                                 interactionName = "aInteraction",
//                                                 predefinedParameters = Map.empty,
//                                                 overriddenIngredientNames = Map.empty,
//                                                 maximumInteractionCount = None,
//                                                 overriddenOutputIngredientName = null,
//                                                 failureStrategy = InteractionFailureStrategy.BlockInteraction,
//                                                 ingredientExtractor = new CompositeIngredientExtractor())
//
//      val callFunction: (Marking, ProcessState, Unit) => Task[(Marking, AnyRef)] =
//        interactionTransition.apply(Map.empty, Map.empty)
//      val processState = ProcessState(UUID.randomUUID(), Map("overriddenName" -> "1"))
//
//      When("the method of the interaction is invoked")
//      val task: Option[(Marking, AnyRef)] = callFunction(null, processState, Unit).unsafeValue()
//
//      Then("Output Ingredient Name should be modified")
//      //TODO add assert on the output ingredient identifier tag
//      // task.map(taskOutput => taskOutput._1.keySet).filter(e => e);
//      task.map(_._2) shouldEqual Some(10)
//    }
//
//    "invoke the InteractionTransition and apply identity transformation since no matching transformation function is found" in {
//
//      Given("An `InteractionTransition` that can fires an Event with ingredient")
//      val ingredientValue = "1"
//      val ingredientName  = "overriddenName"
//
//      val interactionTransition = InteractionTransition[SimpleInteractionThatTriggersEvent](
//        interactionClass = classOf[SimpleInteractionThatTriggersEvent],
//        interactionProvider = () => InteractionThatTriggersAnEvent,
//        interactionMethod = "aInteraction",
//        interactionName = "aInteraction",
//        predefinedParameters = Map.empty,
//        overriddenIngredientNames = Map.empty,
//        maximumInteractionCount = None,
//        overriddenOutputIngredientName = null,
//        failureStrategy = InteractionFailureStrategy.BlockInteraction,
//        ingredientExtractor = new CompositeIngredientExtractor())
//
//      And("Event Transformation function for the configured Event class")
//      val testEventOutputTransformer: Map[Class[_], EventOutputTransformer[_, _]] =
//        Map(transformedEventTransformer.sourceType -> transformedEventTransformer)
//      val interactionTransitionWithEventTransformer =
//        interactionTransition.copy(eventOutputTransformers = testEventOutputTransformer)
//
//      When("the interaction is invoked and the ingredient is available")
//      val f: (Marking, ProcessState, Unit) => Task[(Marking, AnyRef)] =
//        interactionTransitionWithEventTransformer.apply(Map.empty, Map.empty)
//      val processState = ProcessState(UUID.randomUUID(), Map(ingredientName -> ingredientValue))
//      val output       = f(null, processState, Unit).unsafeValue().map(_._2)
//
//      Then(
//        "`InteractionTransition.outputEventClasses` must consist of the configured event class there is no matching transformation function found.")
//      interactionTransitionWithEventTransformer.outputEventClasses should contain theSameElementsAs Seq(
//        classOf[TestEvent])
//
//      And("Output should be same as the result of the interation")
//      output shouldEqual Some(TestEvent(ingredientValue))
//    }
//
//    "invoke the InteractionTransition and apply the matching transformation function" in {
//
//      Given("An `InteractionTransition` that can fires an event with ingredient")
//      val ingredientValue = "1"
//      val ingredientName  = "overriddenName"
//
//      val interactionTransition = InteractionTransition[SimpleInteractionThatTriggersEvent](
//        interactionClass = classOf[SimpleInteractionThatTriggersEvent],
//        interactionProvider = () => InteractionThatTriggersAnEvent,
//        interactionMethod = "aInteraction",
//        interactionName = "aInteraction",
//        predefinedParameters = Map.empty,
//        overriddenIngredientNames = Map.empty,
//        maximumInteractionCount = None,
//        overriddenOutputIngredientName = null,
//        failureStrategy = InteractionFailureStrategy.BlockInteraction,
//        ingredientExtractor = new CompositeIngredientExtractor())
//
//      And("Event Transformation function for the configured Event class")
//      val testEventOutputTransformer: Map[Class[_], EventOutputTransformer[_, _]] =
//        Map(eventTransformer.sourceType -> eventTransformer)
//      val interactionTransitionWithEventTransformer =
//        interactionTransition.copy(eventOutputTransformers = testEventOutputTransformer)
//
//      When("the interaction is invoked and the ingredient is available")
//      val f: (Marking, ProcessState, Unit) => Task[(Marking, AnyRef)] =
//        interactionTransitionWithEventTransformer.apply(Map.empty, Map.empty)
//      val processState = ProcessState(UUID.randomUUID(), Map(ingredientName -> ingredientValue))
//      val output       = f(null, processState, Unit).unsafeValue().map(_._2)
//
//      Then("`InteractionTransition.outputEventClasses` consists of the transformed event class")
//      interactionTransitionWithEventTransformer.outputEventClasses should contain(
//        classOf[TransformedEvent])
//
//      And("Output is also transformed based on the transformation function")
//      output shouldEqual Some(TransformedEvent(ingredientValue, Integer.MAX_VALUE))
//    }
//
//    "fail when calling apply method when ingredient is not provided " in {
//
//      val interactionTransition: InteractionTransition[SimpleInteraction] =
//        InteractionTransition[SimpleInteraction](interactionClass = classOf[SimpleInteraction],
//                                                 interactionProvider = () => SimpleInteractionImpl,
//                                                 interactionMethod = "action1",
//                                                 interactionName = "aInteraction",
//                                                 predefinedParameters = Map.empty,
//                                                 overriddenIngredientNames = Map.empty,
//                                                 maximumInteractionCount = None,
//                                                 overriddenOutputIngredientName = null,
//                                                 failureStrategy = InteractionFailureStrategy.BlockInteraction,
//                                                 ingredientExtractor = new CompositeIngredientExtractor())
//
//      val f: (Marking, ProcessState, Unit) => Task[(Marking, AnyRef)] =
//        interactionTransition.apply(Map.empty, Map.empty)
//      val processState = ProcessState(UUID.randomUUID(), Map.empty)
//
//      intercept[IllegalArgumentException] {
//        f(null, processState, Unit).unsafeValue()
//      }
//    }
//
//    "fail when calling apply method with overridden ingredient in not provided " in {
//
//      val ingredientName: String    = "overriddenName"
//      val newIngredientName: String = "overriddenName2"
//
//      val interactionTransition: InteractionTransition[SimpleInteraction] =
//        InteractionTransition[SimpleInteraction](interactionClass = classOf[SimpleInteraction],
//                                                 interactionProvider = () => SimpleInteractionImpl,
//                                                 interactionMethod = "action1",
//                                                 interactionName = "aInteraction",
//                                                 predefinedParameters = Map.empty,
//                                                 overriddenIngredientNames =
//                                                   Map(ingredientName -> newIngredientName),
//                                                 maximumInteractionCount = None,
//                                                 overriddenOutputIngredientName = null,
//                                                 failureStrategy = InteractionFailureStrategy.BlockInteraction,
//                                                 ingredientExtractor = new CompositeIngredientExtractor())
//
//      val f: (Marking, ProcessState, Unit) => Task[(Marking, AnyRef)] =
//        interactionTransition.apply(Map.empty, Map.empty)
//
//      val processState = ProcessState(UUID.randomUUID(), Map(ingredientName -> "1"))
//
//      intercept[IllegalArgumentException] {
//        f(null, processState, Unit).unsafeValue()
//      }
//    }
//  }
}
