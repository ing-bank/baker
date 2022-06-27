package com.ing.baker

import com.ing.baker.il.CompiledRecipe.RecipeIdVariant
import com.ing.baker.il.petrinet.HasCustomToStringForRecipeId

import java.security.MessageDigest
import scala.annotation.nowarn
import scala.collection.immutable.Seq

package object il {

  val recipeInstanceIdName = "recipeInstanceId"
  val processIdName = "$ProcessID$" //needed for backwards compatibility with V1 and V2
  val exhaustedEventAppend = "RetryExhausted"

  def sha256HashCode(str: String): Long = {
    val sha256Digest: MessageDigest = MessageDigest.getInstance("SHA-256")
    BigInt(1, sha256Digest.digest(str.getBytes("UTF-8"))).toLong
  }

  def zeroPaddedSHA256(text: String): String = {

    import java.math.BigInteger
    import java.security.MessageDigest

    val sha256Digest: MessageDigest = MessageDigest.getInstance("SHA-256")
    val digest = sha256Digest.digest(text.getBytes("UTF-8"))

    val bigInt = new BigInteger(1, digest)

    // hex = 1...16 = 4 bits, this makes 256 / 4 = 64 characters
    val hex = bigInt.toString(16)

    // add zero padding
    List.fill(64 - hex.length)("0").mkString + hex
  }

  implicit class ToRecipeIdStringHelper[A](s : Seq[A]) {
    def mapRecipeIdStrings(variant: RecipeIdVariant) : Seq[String] =
      s.map{
        case o : HasCustomToStringForRecipeId => o.toStringForRecipeId(variant)
        case o => o.toString
      }

    def mkStringForRecipeId(dataStructureName: String, variant: RecipeIdVariant): String =
      mapRecipeIdStrings(variant).mkString(
              start = s"$dataStructureName(",
              sep = ", ",
              end = ")"
      )

    @nowarn
    private def toRecipeType(variant: RecipeIdVariant,
                     emptyNameJava : String, nonEmptyNameJava: String,
                     emptyNameScala: String, nonEmptyNameScala: String) : String =
      variant match {
        case CompiledRecipe.Improved | _ if s.isInstanceOf[List[A]] =>
          s.mkStringForRecipeId("List", variant)
        case CompiledRecipe.Scala212CompatibleJava =>
          if (s.isEmpty) s"$emptyNameJava()"
          else s.mkStringForRecipeId(nonEmptyNameJava, variant)
        case CompiledRecipe.Scala212CompatibleScala =>
          if (s.isEmpty) s"$emptyNameScala()"
          else s.mkStringForRecipeId(nonEmptyNameScala, variant)
      }

    def toRecipeIdStringTypeA(variant: RecipeIdVariant) : String =
      toRecipeType(variant,
        emptyNameJava = "ArraySeq", nonEmptyNameJava = "ArrayBuffer",
        emptyNameScala = "ArraySeq", nonEmptyNameScala = "ArrayBuffer")

    def toRecipeIdStringTypeB(variant: RecipeIdVariant) : String =
      toRecipeType(variant,
        emptyNameJava = "ArraySeq", nonEmptyNameJava = "ArraySeq",
        emptyNameScala = "ArrayBuffer", nonEmptyNameScala = "ArraySeq")
  }

}
