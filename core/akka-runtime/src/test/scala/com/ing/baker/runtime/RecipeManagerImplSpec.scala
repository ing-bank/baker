package com.ing.baker.runtime

import com.ing.baker.il.{CompiledRecipe, EventDescriptor}
import com.ing.baker.il.petrinet.{EventTransition, RecipePetriNet, Transition}
import com.ing.baker.petrinet.api.Marking
import org.mockito.Mockito.when
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatestplus.mockito.MockitoSugar

class RecipeManagerImplSpec extends AsyncWordSpecLike
  with Matchers
  with MockitoSugar
  with BeforeAndAfter
  with BeforeAndAfterAll {

  "RecipeManagerImpl" should {

    "implement add, get and all" in {
      val impl = new RecipeManagerImpl()

      val eventType = EventDescriptor("Event", Seq.empty)
      val transitions: Set[Transition] = Set(EventTransition(eventType, isSensoryEvent = true, None))

      val petrinetMock: RecipePetriNet = mock[RecipePetriNet]
      when(petrinetMock.transitions).thenReturn(transitions)

      val recipe1 = CompiledRecipe("name", "1", petrinetMock, Marking.empty, Seq.empty, Option.empty, Option.empty)
      val recipe2 = CompiledRecipe("name", "2", petrinetMock, Marking.empty, Seq.empty, Option.empty, Option.empty)

      for {
        id1 <- impl.add(recipe1)
        id2 <- impl.add(recipe2)
        check1 <- impl.get(id1)
        check2 <- impl.get(id2)
        all <- impl.all()
      } yield {
        val recipes: Seq[CompiledRecipe] = all.map(_._1)
        (id1 == "1"
          && id2 == "id2"
          && check1.get._1 == recipe1
          && check2.get._1 == recipe2
          && recipes.size == 2
          && recipes.contains(recipe1)
          && recipes.contains(recipe2)) shouldBe (true)
      }
    }
  }

}
