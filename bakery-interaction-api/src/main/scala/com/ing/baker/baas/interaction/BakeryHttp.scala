package com.ing.baker.baas.interaction

import org.http4s._
import org.http4s.util.CaseInsensitiveString

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
