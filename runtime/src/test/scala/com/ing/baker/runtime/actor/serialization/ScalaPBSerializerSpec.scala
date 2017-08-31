package com.ing.baker.runtime.actor.serialization

import akka.actor.ActorSystem
import akka.serialization.SerializationExtension
import akka.testkit.TestKit
import com.google.protobuf.ByteString
import com.ing.baker.runtime.actor.messages
import com.trueaccord.scalapb.GeneratedMessage
import org.scalacheck.{Gen, Prop, Test}
import org.scalatest.prop.Checkers
import org.scalatest.{FunSuiteLike, Matchers}

class ScalaPBSerializerSpec extends TestKit(ActorSystem("ScalaPBSerializerSpec"))
  with Checkers with FunSuiteLike with Matchers {

  import ScalaPBSerializerSpec._

  val serializer: ScalaPBSerializer = SerializationExtension.get(system).serializerByIdentity(102).asInstanceOf[ScalaPBSerializer]

  val messageToSerialize: Gen[GeneratedMessage] = Gen.oneOf(
    initializedMessageGen,
    transitionFiredGen,
    transitionFailedGen)

  test("baker can serialize/deserialize generated protobuf messages") {
    val prop = Prop.forAll(messageToSerialize) { (message) =>
      val bytes = serializer.toBinary(message)
      val deserializedMessage = serializer.fromBinary(bytes, serializer.manifest(message))
      message.equals(deserializedMessage)
    }

    check(prop, Test.Parameters.defaultVerbose.withMinSuccessfulTests(1000))
  }
}

object ScalaPBSerializerSpec {
  val intGen: Gen[Int] = Gen.chooseNum(Int.MinValue, Int.MaxValue)
  val longGen: Gen[Long] = Gen.chooseNum(Long.MinValue, Long.MaxValue)

  val serializedDataGen: Gen[messages.SerializedData] = for {
    serializerId <- Gen.option(intGen)
    manifest <- Gen.option(Gen.alphaNumStr)
    // generate an Option[ByteString] using generated list of chars(bytes)
    byteString <- Gen.option(Gen.listOf(Gen.alphaNumChar).map(_.map(_.toByte).toArray).map(ByteString.copyFrom))
  } yield messages.SerializedData(serializerId, manifest, byteString)

  val consumedTokenGen: Gen[messages.ConsumedToken] = for {
    placeId <- Gen.option(longGen)
    tokenId <- Gen.option(longGen)
    count <- Gen.option(intGen)
  } yield messages.ConsumedToken(placeId, tokenId, count)

  val producedTokenGen: Gen[messages.ProducedToken] = for {
    placeId <- Gen.option(longGen)
    tokenId <- Gen.option(longGen)
    count <- Gen.option(intGen)
    tokenData <- Gen.option(serializedDataGen)
  } yield messages.ProducedToken(placeId, tokenId, count, tokenData)

  val initializedMessageGen: Gen[messages.Initialized] = for {
    initialMarking <- Gen.listOf(producedTokenGen)
    initialState <- Gen.option(serializedDataGen)
  } yield messages.Initialized(initialMarking, initialState)

  val transitionFiredGen: Gen[messages.TransitionFired] = for {
    jobId <- Gen.option(longGen)
    correlationId <- Gen.option(longGen)
    transitionId <- Gen.option(longGen)
    timeStarted <- Gen.option(longGen)
    timeCompleted <- Gen.option(longGen)
    consumed <- Gen.listOf(consumedTokenGen)
    produced <- Gen.listOf(producedTokenGen)
    data <- Gen.option(serializedDataGen)
  } yield messages.TransitionFired(jobId, correlationId, transitionId, timeStarted, timeCompleted, consumed, produced, data)

  val transitionFailedGen: Gen[messages.TransitionFailed] = for {
    jobId <- Gen.option(longGen)
    correlationId <- Gen.option(longGen)
    transitionId <- Gen.option(longGen)
    timeStarted <- Gen.option(longGen)
    timeCompleted <- Gen.option(longGen)
    inputData <- Gen.option(serializedDataGen)
    failureReason <- Gen.option(Gen.alphaNumStr)
  } yield messages.TransitionFailed(jobId, correlationId, transitionId, timeStarted, timeCompleted, inputData, failureReason)

}
