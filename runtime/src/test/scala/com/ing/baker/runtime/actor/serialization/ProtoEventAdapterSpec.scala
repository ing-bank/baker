package com.ing.baker.runtime.actor.serialization

import javax.crypto.BadPaddingException
import akka.actor.ActorSystem
import com.ing.baker.AllTypeRecipe
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.serialization.Encryption._
import org.scalatest.{BeforeAndAfterAll, FunSuite, Matchers}

@deprecated("marked deprecated because of -XFatal-Warnings and deprecated sieves", "1.4.0")
class ProtoEventAdapterSpec extends FunSuite with Matchers with BeforeAndAfterAll {

  val actorSystem = ActorSystem()

  test("serialize/deserialize data with encryption") {
    val someEvent = "some event"
    val serializer1 = new ProtoEventAdapterImpl(actorSystem, new AESEncryption("0123456789123456"))
    val serializer2 = new ProtoEventAdapterImpl(actorSystem, new AESEncryption("0123456789123456"))

    val serializedData = serializer1.toProtoAny(someEvent)

    serializer2.toDomain[AnyRef](serializedData) shouldBe someEvent
  }

  test("cannot deserialize data back if another encryption secret is used") {
    val someEvent = "some event"
    val serializer1 = new ProtoEventAdapterImpl(actorSystem, new AESEncryption("0123456789123456"))
    val serializer2 = new ProtoEventAdapterImpl(actorSystem, new AESEncryption("0123456789123459"))

    val serializedData = serializer1.toProtoAny(someEvent)

    // fails during decryption and throws this exception
    intercept[BadPaddingException] {
      serializer2.toDomain[AnyRef](serializedData)
    }
  }

  test("serialize/deserialize data without encryption") {
    val someEvent = "some event"
    val serializer1 = new ProtoEventAdapterImpl(actorSystem, NoEncryption)
    val serializer2 = new ProtoEventAdapterImpl(actorSystem, NoEncryption)

    val serializedData = serializer1.toProtoAny(someEvent)

    serializer2.toDomain[AnyRef](serializedData) shouldBe someEvent
  }


  test("should serialize AllTypeRecipe") {
    val recipe = AllTypeRecipe.recipe
    val compiledRecipe = RecipeCompiler.compileRecipe(recipe)
    val eventAdapter = new ProtoEventAdapterImpl(actorSystem, NoEncryption)

    val domainObject = RecipeAdded("recipeId", compiledRecipe)
    val newDomainObject = eventAdapter.toDomain[RecipeAdded](eventAdapter.toProtoMessage(domainObject))

    domainObject shouldBe newDomainObject
  }

  override def afterAll() = {
    super.afterAll()
    actorSystem.terminate()
  }
}
