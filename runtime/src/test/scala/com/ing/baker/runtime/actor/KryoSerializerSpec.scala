package com.ing.baker.runtime.actor

import com.twitter.chill.{KryoPool, ScalaKryoInstantiator}
import org.scalatest.{FunSuite, Matchers}


case class Test1(a: Int, b: String)

case class Test2(a: Int, b: String)

case class Test3(a: Int, b: String, c: String)

class KryoSerializerSpec extends FunSuite with Matchers {

  test("kryo can serialize/deserialize case classes") {
    withKryo { kryo =>
      val obj = Test1(5, "test")

      kryo.fromBytes(kryo.toBytesWithClass(obj)) shouldBe obj
    }
  }

  test("kryo can serialize/deserialize case classes inside collection types") {
    withKryo { kryo =>
      val obj = List(Test1(5, "test"))

      kryo.fromBytes(kryo.toBytesWithClass(obj)) shouldBe obj
    }
  }

  test("kryo can serialize/deserialize scala collection types") {
    withKryo { kryo =>
      val obj = List(1, 2, 3, 4, 5)

      kryo.fromBytes(kryo.toBytesWithClass(obj)) shouldBe obj
    }
  }

  private def withKryo(f: KryoPool => Unit): Unit = {
    val kryoPool = KryoPool.withByteArrayOutputStream(1, new ScalaKryoInstantiator)
    f(kryoPool)
  }

}
