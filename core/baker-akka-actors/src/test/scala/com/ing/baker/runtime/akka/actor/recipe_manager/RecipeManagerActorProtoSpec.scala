package com.ing.baker.runtime.akka.actor.recipe_manager

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexSpec
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerActor.RecipeAdded
import com.ing.baker.runtime.akka.actor.serialization.{AkkaSerializerProvider, SerializationSpec}
import com.ing.baker.runtime.serialization.Encryption
import org.scalatest.TryValues._
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike

class RecipeManagerActorProtoSpec extends TestKit(ActorSystem("RecipeManagerActorProtoSpec", ProcessIndexSpec.config)) { this: AsyncWordSpecLike with Matchers =>

  //This test was added to ensure backwards compatibility with V1 of Baker
  "The RecipeAdded message" should {
    "allow for an empty timestamp and default it to 0" in {
      implicit val serializersProvider: AkkaSerializerProvider = AkkaSerializerProvider(system, Encryption.NoEncryption)
      val recipeAddedProto = RecipeManagerProto.recipeAddedProto

      val recipeAddedMessage = recipeAddedProto
        .toProto(RecipeAdded(SerializationSpec.IntermediateLanguage.recipeGen.sample.get, 99L))
        .copy(timeStamp = None)

      val result = recipeAddedProto.fromProto(recipeAddedMessage)
      result.get //This triggers the serialization logic and if it fails it throws a readable exception.
      result.success.value.timeStamp shouldBe 0L
    }
  }
}
