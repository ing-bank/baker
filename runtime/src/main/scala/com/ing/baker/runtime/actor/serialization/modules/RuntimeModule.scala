package com.ing.baker.runtime.actor.serialization.modules

import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actor.protobuf.SerializedData
import com.ing.baker.runtime.core
import com.ing.baker.types.Value

class RuntimeModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case e: core.RuntimeEvent =>
      val ingredients = writeIngredients(e.providedIngredients, ctx)
      protobuf.RuntimeEvent(Some(e.name), ingredients)

    case e: core.ProcessState =>
      val ingredients = writeIngredients(e.ingredients.toSeq, ctx)
      protobuf.ProcessState(Some(e.processId), ingredients, e.eventNames)
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {

    case protobuf.RuntimeEvent(Some(name), ingredients) =>
      core.RuntimeEvent(name, readIngredients(ingredients, ctx))

    case protobuf.ProcessState(Some(id), ingredients, events) =>
      core.ProcessState(id, readIngredients(ingredients, ctx).toMap, events.toList)
  }

  private def writeIngredients(ingredients: Seq[(String, Value)], ctx: ProtoEventAdapter): Seq[protobuf.Ingredient] = {
    ingredients.map { case (name, value) =>
      val serializedObject = ctx.toProtoAny(value)
      protobuf.Ingredient(Some(name), Some(serializedObject))
    }
  }

  private def readIngredients(ingredients: Seq[protobuf.Ingredient], ctx: ProtoEventAdapter): Seq[(String, Value)] = {
    ingredients.map {
      case protobuf.Ingredient(Some(name), Some(data)) =>
        val deserializedObject = ctx.toDomain[Value](data)
        name -> deserializedObject
      case _ => throw new IllegalArgumentException("Missing fields in Protobuf data when deserializing ingredients")
    }
  }

}
