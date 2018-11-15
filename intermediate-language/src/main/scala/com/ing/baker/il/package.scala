package com.ing.baker

import java.security.MessageDigest

package object il {

  val processIdName = "$ProcessID$"
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
    (List.fill(64 - hex.length)("0")).mkString + hex
  }
}
