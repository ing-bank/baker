package com.ing.baker.runtime.actor


class DisabledRecipeMetadata(override val recipeName: String) extends RecipeMetadata {
  override val getAll: Set[ProcessMetadata] = Set.empty

  override def add(meta: ProcessMetadata): Unit = {
    // Intentionally left blank
  }

  override def remove(meta: ProcessMetadata): Unit = {
    // Intentionally left blank
  }
}
