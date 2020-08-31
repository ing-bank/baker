package com.ing.bakery.interaction

import java.io.{File, FileInputStream, InputStream}
import java.security.{KeyStore, SecureRandom}

import cats.data.EitherT
import cats.effect.IO
import com.ing.baker.runtime.serialization.ProtoMap
import javax.net.ssl.{KeyManagerFactory, SSLContext, TrustManagerFactory}
import org.http4s.EntityDecoder.collectBinary
import org.http4s._
import org.http4s.util.CaseInsensitiveString

import scala.util.{Failure, Success, Try}

object BakeryHttp {

  case class TLSConfig(password: String, keystorePath: String, keystoreType: String)

  def loadSSLContext(config: TLSConfig): SSLContext = {
    // Try resource directory as root first
    val keystoreResource: InputStream = getClass.getClassLoader.getResourceAsStream(config.keystorePath)
    // Otherwise try absolute path
    val keystore: InputStream =
      if(keystoreResource == null) new FileInputStream(new File(config.keystorePath))
      else keystoreResource
    require(keystore != null, s"Keystore of type '${config.keystoreType}' not found on path '${config.keystorePath}', tried classpath resources and then absolute path")
    loadSSLContextFromInputStream(keystore, config.password, config.keystoreType)
  }

  def loadSSLContextFromInputStream(keystore: InputStream, password: String, keystoreType: String): SSLContext = {
    val ks: KeyStore = KeyStore.getInstance(keystoreType)
    val passwordArray: Array[Char] = password.toCharArray
    ks.load(keystore, passwordArray)
    val keyManagerFactory: KeyManagerFactory = KeyManagerFactory.getInstance("SunX509")
    keyManagerFactory.init(ks, passwordArray)
    val tmf: TrustManagerFactory = TrustManagerFactory.getInstance("SunX509")
    tmf.init(ks)
    val sslContext: SSLContext = SSLContext.getInstance("TLS")
    sslContext.init(keyManagerFactory.getKeyManagers, tmf.getTrustManagers, new SecureRandom)
    sslContext
  }

  object ProtoEntityEncoders {

    type ProtoMessage[A] = scalapb.GeneratedMessage

    implicit def protoDecoder[A, P <: ProtoMessage[P]](implicit protoMap: ProtoMap[A, P]): EntityDecoder[IO, A] =
      EntityDecoder.decodeBy(MediaType.application.`octet-stream`)(collectBinary[IO]).map(_.toArray)
        .flatMapR { bytes =>
          protoMap.fromByteArray(bytes) match {
            case Success(a) =>
              EitherT.fromEither[IO](Right(a))
            case Failure(exception) =>
              EitherT.fromEither[IO](Left(MalformedMessageBodyFailure(exception.getMessage, Some(exception))))
          }
        }

    implicit def protoEncoder[A, P <: ProtoMessage[P]](implicit protoMap: ProtoMap[A, P]): EntityEncoder[IO, A] =
      EntityEncoder.byteArrayEncoder[IO].contramap(protoMap.toByteArray)

    implicit def protoEitherDecoder[A, P0 <: ProtoMessage[P0], B, P1 <: ProtoMessage[P1]](implicit p1: ProtoMap[A, P0], p2: ProtoMap[B, P1]): EntityDecoder[IO, Either[A, B]] =
      EntityDecoder.decodeBy(MediaType.application.`octet-stream`)(collectBinary[IO]).map(_.toArray)
        .flatMapR { bytes =>
          val eitherTry: Try[Either[A, B]] =
            p1.fromByteArray(bytes).map[Either[A, B]](Left(_))
              .orElse(p2.fromByteArray(bytes).map[Either[A, B]](Right(_)))
          eitherTry match {
            case Success(a) =>
              EitherT.fromEither[IO](Right(a))
            case Failure(exception) =>
              EitherT.fromEither[IO](Left(MalformedMessageBodyFailure(exception.getMessage, Some(exception))))
          }
        }
  }

  object Headers {

    def `X-Bakery-Intent`(intent: Intent, hostname: Uri): Header = {
      Header.Raw(CaseInsensitiveString("X-Bakery-Intent"), intent.render(hostname))
    }

    sealed abstract class Intent(rawIntent: String) {

      def render(hostname: Uri): String = {
        val intendedHost = hostname.authority.map(_.host.value).getOrElse("unknown")
        s"$rawIntent:$intendedHost"
      }
    }

    object Intent {

      case object `Remote-Interaction` extends Intent("Remote-Interaction")
    }
  }
}
