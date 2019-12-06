package com.ing.baker.runtime.akka.actor.serialization

import org.scalacheck.Gen._
import org.scalacheck.Prop.forAll
import org.scalacheck._
import org.scalatest.FunSuite
import com.ing.baker.runtime.akka.actor.serialization.Encryption._
import org.scalatestplus.scalacheck.Checkers

class EncryptionPropertiesSpec extends FunSuite with Checkers {

  val desEncryptionGen: Gen[DESEncryption] = for {
    keyChars ← Gen.listOfN(8, alphaChar)
  } yield new DESEncryption(keyChars.mkString)

  val aesEncryptionGen: Gen[AESEncryption] = for {
    keyChars ← Gen.listOfN(16, alphaChar)
  } yield new AESEncryption(keyChars.mkString)

  val keyAndTextGen: Gen[(JavaCryptoEncryption, String)] = for {
    algorithm ← Gen.oneOf(aesEncryptionGen, desEncryptionGen)
    text ← Gen.alphaStr
  } yield (algorithm, text)

  test("(AES|DES)Encryption: decrypt(encrypt(plaintext)) should be plaintext") {
    val property = forAll(keyAndTextGen) {
      case (encryption: JavaCryptoEncryption, plainText: String) ⇒
        val encryptedBytes = encryption.encrypt(plainText.getBytes)
        val decryptedPlainText = new String(encryption.decrypt(encryptedBytes))

        plainText == decryptedPlainText
    }

    check(property, Test.Parameters.defaultVerbose.withMinSuccessfulTests(10))
  }
}
