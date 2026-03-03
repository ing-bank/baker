package com.ing.baker.runtime.recipe_manager

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.RecipeRecord
import org.mockito.Mockito.when
import org.scalatest.flatspec.AsyncFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.mockito.MockitoSugar

class DefaultRecipeManagerSpec extends AsyncFlatSpec with Matchers with MockitoSugar {

  private val mockCompiledRecipe: CompiledRecipe = mock[CompiledRecipe]
  when(mockCompiledRecipe.recipeId).thenReturn("1")
  when(mockCompiledRecipe.name).thenReturn("test recipe")

  private val mockInactiveCompiledRecipe: CompiledRecipe = mock[CompiledRecipe]
  when(mockInactiveCompiledRecipe.recipeId).thenReturn("2")
  when(mockInactiveCompiledRecipe.name).thenReturn("inactive test recipe")

  private val recipe = RecipeRecord.of(recipe = mockCompiledRecipe)
  private val inactiveRecipe = RecipeRecord.of(recipe = mockInactiveCompiledRecipe, isActive = false)

  "DefaultRecipeManager" should "put and get a active/inactive recipes" in {
    val manager = new DefaultRecipeManager()

    for {
      _ <- manager.put(recipe)
      _ <- manager.put(inactiveRecipe)
      result <- manager.get("1")
      resultInactive <- manager.get("2")
    } yield {
      result shouldBe Some(recipe)
      resultInactive shouldBe Some(inactiveRecipe)
    }
  }

  it should "return None for a non-existent recipe" in {
    val manager = new DefaultRecipeManager()

    manager.get("non-existent").map { result =>
      result shouldBe None
    }
  }

  it should "return all recipes" in {
    val manager = new DefaultRecipeManager()

    for {
      _ <- manager.put(recipe)
      _ <- manager.put(inactiveRecipe)
      result <- manager.all
    } yield {
      result should contain theSameElementsAs Seq(recipe, inactiveRecipe)
    }
  }

  it should "return all active recipes" in {
    val manager = new DefaultRecipeManager()

    for {
      _ <- manager.put(recipe)
      _ <- manager.put(inactiveRecipe)
      result <- manager.allActive
    } yield {
      result should contain theSameElementsAs Seq(recipe)
    }
  }
}