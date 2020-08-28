package com.ing.baker.runtime.serialization

import java.security.MessageDigest

object TokenIdentifier  {

  /**
    * TODO:
    *
    * This approach is fragile, the identifier function cannot change ever or recovery breaks
    * a more robust alternative is to generate the ids and persist them
    */
  def apply(tokenValue: Any): Long = tokenValue match {
    case null        => -1
    case str: String => sha256(str)
    case obj         => obj.hashCode()
  }

  def sha256(str: String) = {
    val sha256Digest: MessageDigest = MessageDigest.getInstance("SHA-256")
    BigInt(1, sha256Digest.digest(str.getBytes("UTF-8"))).toLong
  }
}
