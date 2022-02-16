package com.ing.baker.runtime.recipe_manager

import com.ing.baker.il.petrinet.{EventTransition, RecipePetriNet, Transition}
import com.ing.baker.il.{CompiledRecipe, EventDescriptor}
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.runtime.common.RecipeRecord
import org.mockito.Mockito.when
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatestplus.mockito.MockitoSugar

import scala.collection.immutable.Seq

class DefaultRecipeManagerSpec extends AsyncWordSpecLike
  with Matchers
  with MockitoSugar
  with BeforeAndAfter
  with BeforeAndAfterAll {

  "RecipeManagerImpl" should {

    "implement add, get and all" in {
      val impl = new DefaultRecipeManager()

      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, isSensoryEvent = true, None))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      when(petrinetMock.transitions).thenReturn(transitions)

      val recipe1 = CompiledRecipe("name", "1", petrinetMock, Marking.empty, Seq.empty, Option.empty, Option.empty)
      val recipe2 = CompiledRecipe("name", "2", petrinetMock, Marking.empty, Seq.empty, Option.empty, Option.empty)

      for {
        id1 <- impl.put(RecipeRecord.of(recipe1, System.currentTimeMillis()))
        id2 <- impl.put(RecipeRecord.of(recipe2, System.currentTimeMillis()))
        check1 <- impl.get(id1)
        check2 <- impl.get(id2)
        all <- impl.all
      } yield {
        val recipes: Seq[CompiledRecipe] = all.map(_.recipe).toIndexedSeq
        (id1 == "1"
          && id2 == "2"
          && check1.get.recipe == recipe1
          && check2.get.recipe == recipe2
          && recipes.size == 2
          && recipes.contains(recipe1)
          && recipes.contains(recipe2)) shouldBe (true)
      }
    }
  }

}
