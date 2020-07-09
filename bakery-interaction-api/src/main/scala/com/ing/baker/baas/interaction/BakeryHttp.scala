package com.ing.baker.baas.interaction

import cats.data.EitherT
import cats.effect.IO
import com.ing.baker.runtime.serialization.ProtoMap
import org.http4s.EntityDecoder.collectBinary
import org.http4s.util.CaseInsensitiveString
import org.http4s._

import scala.util.{Failure, Success, Try}

object BakeryHttp {

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
