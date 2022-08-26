package webshop.webservice

import cats.effect.IO
import org.scalatest.flatspec.AsyncFlatSpec
import org.scalatest.matchers.should

class WebserviceSpec extends AsyncFlatSpec with should.Matchers {

  "Main" should "work" in {
    val s = Main.system.use(a => IO(a)).unsafeToFuture()
    try {
      s.flatMap(_.baker.getAllInteractions).map(interactions => interactions.length shouldBe 3)
    } finally {
      s.flatMap(_.shuttingDown.get.unsafeToFuture() shouldEqual true)
    }

  }
}
