package com.ing.baker.pbt

import java.io.{File, PrintWriter}
import java.util.UUID

import akka.actor.ActorSystem
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.{CompiledRecipe, EventType, IngredientType, ValidationSettings, petrinet}
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{FiresOneOfEvents, InteractionOutput, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, InteractionDescriptor, InteractionDescriptorFactory, Recipe}
import com.ing.baker.runtime.core.{Baker, ProcessState, RuntimeEvent}
import org.scalacheck.Prop.forAll
import org.scalacheck._
import org.scalatest.FunSuite
import org.scalatest.prop.Checkers

import scala.annotation.tailrec
import scala.concurrent.duration.FiniteDuration
import scala.util.Random

class RecipePropertiesSpec extends FunSuite with Checkers {

  import RecipePropertiesSpec._

  test("Baker can compile any valid recipe") {
    val prop = forAll(recipeGen) { recipe =>
//      val validations = ValidationSettings(allowCycles = false, allowNonexecutableInteractions = false)

      val validations = ValidationSettings(allowCycles = false)

      val compiledRecipe = RecipeCompiler.compileRecipe(recipe, validations)

      if (compiledRecipe.validationErrors.nonEmpty) {
        logRecipeStats(recipe)
        logCompiledRecipeStats(compiledRecipe)
        dumpToFile(s"visualRecipe-${compiledRecipe.name}", compiledRecipe.getRecipeVisualization)
        dumpToFile(s"petrinet-${compiledRecipe.name}", compiledRecipe.getPetriNetVisualization)
      }

      // assertion of the result
      compiledRecipe.validationErrors.isEmpty
    }

    check(prop, Test.Parameters.defaultVerbose.withMinSuccessfulTests(100))
  }

  ignore("Baker can execute a compiled recipe") {
    implicit val actorSystem = ActorSystem("pbt-actor-system")
    implicit val duration = FiniteDuration(1, "seconds")

    val prop = forAll(recipeGen) { recipe =>

      val compiledRecipe = RecipeCompiler.compileRecipe(recipe)

      logRecipeStats(recipe)
      logCompiledRecipeStats(compiledRecipe)
      dumpToFile(s"visualRecipe-${compiledRecipe.name}", compiledRecipe.getRecipeVisualization)

      val sensoryEvents: Set[EventType] = compiledRecipe.sensoryEvents
      val petriNetInteractionMock: InteractionTransition[_] => ProcessState => RuntimeEvent = { interaction => _ =>

          val outputEvent = interaction.providesType match {
            case petrinet.FiresOneOfEvents(events, _) =>
              sample(Gen.oneOf(events.map(e => RuntimeEvent(e.name, ingredientValuesFrom[IngredientType](e.providedIngredients, _.name)))))
            case petrinet.ProvidesIngredient(ingredient) =>
              RuntimeEvent(sample(nameGen), ingredientValuesFrom[IngredientType](Seq(ingredient), _.name))
            case petrinet.ProvidesNothing =>
              fail("ProvidesNothing type of interaction should not be hit")
          }
          println(s"Inside interaction: ${interaction.interactionName}. Firing event ${outputEvent.name}")
          outputEvent
      }

      val baker = new Baker(compiledRecipe, petriNetInteractionMock)
      val processId = UUID.randomUUID()
      baker.bake(processId)
      sensoryEvents foreach { event =>
        println(s"Handle sensory event: ${event.name}")
        baker.handleEvent(processId, RuntimeEvent(event.name, ingredientValuesFrom[IngredientType](event.providedIngredients, _.name)))
      }
      dumpToFile(s"visualRecipeState-${compiledRecipe.name}", baker.getVisualState(processId))

      true

    }

    check(prop, Test.Parameters.defaultVerbose.withMinSuccessfulTests(1))
  }

}

object RecipePropertiesSpec {

  val maxNrOfIngredientsPerEvent = 3
  val maxNrOfOutputEventsPerInteraction = 3
  val maxNrOfIngredientsToConsume = 10
  val maxNrOfPreconditionEvents = 3
  val recipeVisualizationOutputPath: String = System.getProperty("java.io.tmpdir")

  val nameGen: Gen[String] = Gen.listOfN(8, Gen.alphaNumChar).map(_.mkString)

  val ingredientGen: Gen[Ingredient[_]] = for {
    name <- nameGen
  } yield Ingredient[String](name)

  val eventGen: Gen[Event] = for {
    name <- nameGen
    nrOfIngredients <- Gen.frequency(
      1 -> Gen.const(0),
      10 -> Gen.choose(1, maxNrOfIngredientsPerEvent)
    )
    providedIngredients <- Gen.listOfN(nrOfIngredients, ingredientGen)
  } yield Event(name, providedIngredients)

  val interactionOutputGen: Gen[InteractionOutput] = for {
    nrOfEvents <- Gen.choose(0, maxNrOfOutputEventsPerInteraction)
    events <- Gen.listOfN(nrOfEvents, eventGen)
    ingredient <- ingredientGen
    output <- Gen.frequency(
      //      1 -> Gen.const(ProvidesNothing),
      5 -> Gen.const(ProvidesIngredient(ingredient)),
      10 -> Gen.const(FiresOneOfEvents(events)))
  } yield output

  val recipeGen: Gen[Recipe] = for {
    name <- nameGen
    sensoryEvents <- Gen.listOf(eventGen) suchThat (_.nonEmpty)
    interactions <- interactionsGen(sensoryEvents) suchThat (_.nonEmpty)
  } yield Recipe(name)
    //turn the lists into var args
    .withSensoryEvents(sensoryEvents: _*)
    .withInteractions(interactions.toList: _*)

  def interactionsGen(events: Iterable[common.Event]): Gen[Set[InteractionDescriptor]] = Gen.const(getInteractions(events))

  def getInteractions(sensoryEvents: Iterable[common.Event]): Set[InteractionDescriptor] = {
    @tailrec def interaction(ingredients: Set[common.Ingredient], events: Set[common.Event], acc: Set[InteractionDescriptor]): Set[InteractionDescriptor] = ingredients match {
      case _ingredients if _ingredients.isEmpty => acc
      case ingredientsLeft =>
        val (andPreconditionEvents, orPreconditionEvents) = getPreconditionEvents(events)

        // Sometimes 0 number of ingredients is possible if this interaction has some precondition events
        val minNrOfIngredients =
          if (andPreconditionEvents.size + orPreconditionEvents.size > 0) 0
          else 1

        val nrOfIngredientsToConsume = ingredientsLeft.size min sample(Gen.choose(minNrOfIngredients, maxNrOfIngredientsToConsume))
        val consumedIngredients = Random.shuffle(ingredientsLeft).take(nrOfIngredientsToConsume)

        // Sometimes ingredients should be reused by multiple interactions, so randomizing this behaviour
        val ingredientsToRemove =
          if (Random.nextInt(3) == 0) sample(Gen.someOf(consumedIngredients)).toSet
          else consumedIngredients

        val remainingIngredients = ingredients.diff(ingredientsToRemove)

        val (interactionDescriptor, outputIngredients, outputEvents) = getInteractionDescriptor(consumedIngredients, andPreconditionEvents, orPreconditionEvents)

        if (remainingIngredients.isEmpty)
        //those are the last ingredients because the diff is an empty list, so nothing left to weave
          acc + interactionDescriptor
        else
          interaction(
            remainingIngredients ++ outputIngredients ++ getIngredientsFrom(outputEvents),
            events ++ outputEvents,
            acc + interactionDescriptor)
    }

    val ingredients = getIngredientsFrom(sensoryEvents)
    interaction(ingredients, sensoryEvents.toSet, Set.empty)
  }

  /**
    * generates an interactionDescriptor using all the given ingredients, with ProvidesIngredient or FiresOneOfEvents outputs.
    * Also uses the given preconditionEvents as AND and OR preconditions.
    *
    * @param ingredients input ingredients set
    * @return Tuple3(interactionDescriptor, outputIngredients, outputEvents)
    */
  def getInteractionDescriptor(ingredients: Set[common.Ingredient], andPreconditionEvents: Set[common.Event], orPreconditionEvents: Set[common.Event]): (InteractionDescriptor, Set[common.Ingredient], Set[common.Event]) = {
    //each interaction fires a single event
    val output = sample(interactionOutputGen)
    val interaction = Interaction(sample(nameGen), ingredients.toSeq, output)

    //return the interaction description and a list of all ingredients that the interaction provides
    val (outputIngredients: Set[common.Ingredient], outputEvents: Set[common.Event]) = output match {
      case ProvidesNothing => (Set.empty, Set.empty)
      case FiresOneOfEvents(_events) => (Set.empty, _events.toSet)
      case ProvidesIngredient(ingredient) => (Set(ingredient), Set.empty)
    }

    val interactionDescriptor = InteractionDescriptorFactory(interaction)
      .withRequiredEvents(andPreconditionEvents.toList: _*)
      .withRequiredOneOfEvents(orPreconditionEvents.toList: _*)

    (interactionDescriptor, outputIngredients, outputEvents)
  }

  /**
    * Randomly produce precondition events as a subset of given events
    *
    * @param events events set
    * @return Tuple2(andPreconditionEvents, orPreconditionEvents)
    */
  def getPreconditionEvents(events: Set[common.Event]): (Set[common.Event], Set[common.Event]) = {
    val nrOfAndPreconditionEvents = sample(Gen.chooseNum(0, maxNrOfPreconditionEvents))
    val nrOfOrPreconditionEvents = sample(Gen.chooseNum(0, maxNrOfPreconditionEvents))

    val andPreconditionEvents: Set[common.Event] = Random.shuffle(events).take(nrOfAndPreconditionEvents)
    val orPreconditionEvents: Set[common.Event] = {
      val pickedEvents = Random.shuffle(events -- andPreconditionEvents).take(nrOfOrPreconditionEvents)
      if (pickedEvents.size < 2) Set.empty
      else pickedEvents
    }

    (andPreconditionEvents, orPreconditionEvents)
  }

  def getIngredientsFrom(events: Iterable[common.Event]): Set[common.Ingredient] = events.flatMap(_.providedIngredients).toSet

  def ingredientValuesFrom[T](ingredients: Seq[T], nameExtractor: T => String): Map[String, Any] = ingredients map (t => nameExtractor(t) -> "") toMap

  /**
    * Recursively check until there's a sample value is returned
    *
    * @return sample value of the generator
    */
  @tailrec def sample[T](gen: Gen[T]): T = gen.sample match {
    case Some(value) => value
    case None => sample(gen)
  }

  def logRecipeStats(recipe: Recipe): Unit = println(s"\n" +
    s"Generated recipe ::: " +
    s"name: ${recipe.name} " +
    s"nrOfSensoryEvents: ${recipe.sensoryEvents.size} " +
    s"nrOfInteractions: ${recipe.interactions.size} " +
    s"")

  def logCompiledRecipeStats(compiledRecipe: CompiledRecipe): Unit = {
    println(s"Compiled recipe ::: " +
      s"name: ${compiledRecipe.name} " +
      s"nrOfAllIngredients: ${compiledRecipe.ingredients.size} " +
      s"nrOfSensoryEvents: ${compiledRecipe.sensoryEvents.size} " +
      s"nrOfInteractionEvents: ${compiledRecipe.interactionEvents.size} " +
      s"nrOfInteractions: ${compiledRecipe.interactionTransitions.size} " +
      s"")
    if (compiledRecipe.validationErrors.nonEmpty) println(s"***VALIDATION ERRORS: ${compiledRecipe.validationErrors.mkString("\n")}")
  }

  def dumpToFile(name: String, data: String): Unit = {
    val fileName =
      if (recipeVisualizationOutputPath endsWith "/") s"$recipeVisualizationOutputPath$name.dot"
      else s"$recipeVisualizationOutputPath/$name.dot"

    val outFile = new File(fileName)
    val writer = new PrintWriter(outFile)

    try {
      writer.write(data)
      println(s"Dumped data with ${data.length} length into $fileName \n")
    } finally {
      writer.close()
    }
  }

}
