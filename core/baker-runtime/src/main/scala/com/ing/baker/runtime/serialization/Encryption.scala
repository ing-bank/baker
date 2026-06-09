package com.ing.baker.runtime.serialization

import com.typesafe.config.Config
import javax.crypto.Cipher
import javax.crypto.spec.SecretKeySpec

// Taken from: https://gist.github.com/mumoshu/1587327
object Encryption {

  def from(config: Config): Encryption = {
    if(config.hasPath("encryption")) {
      val encryptionEnabled = config.getBoolean("encryption.enabled")
      if (encryptionEnabled) new Encryption.AESEncryption(config.getString("encryption.secret"))
      else NoEncryption
    } else NoEncryption
  }

  object NoEncryption extends Encryption {

    def encrypt(dataBytes: Array[Byte]): Array[Byte] = dataBytes

    def decrypt(dataBytes: Array[Byte]): Array[Byte] = dataBytes
  }

  class JavaCryptoEncryption(algorithmName: String, secret: String) extends Encryption {

    def encrypt(bytes: Array[Byte]): Array[Byte] = {
      val secretKey = new SecretKeySpec(secret.getBytes("UTF-8"), algorithmName)
      val encipher = Cipher.getInstance(s"$algorithmName/ECB/PKCS5Padding")
      encipher.init(Cipher.ENCRYPT_MODE, secretKey)
      encipher.doFinal(bytes)
    }

    def decrypt(bytes: Array[Byte]): Array[Byte] = {
      val secretKey = new SecretKeySpec(secret.getBytes("UTF-8"), algorithmName)
      val encipher = Cipher.getInstance(s"$algorithmName/ECB/PKCS5Padding")
      encipher.init(Cipher.DECRYPT_MODE, secretKey)
      encipher.doFinal(bytes)
    }
  }

  class AESEncryption(secret: String) extends JavaCryptoEncryption("AES", secret)

  class DESEncryption(secret: String) extends JavaCryptoEncryption("DES", secret)
}

trait Encryption {

  def encrypt(dataBytes: Array[Byte]): Array[Byte]

  def decrypt(codeBytes: Array[Byte]): Array[Byte]
}

