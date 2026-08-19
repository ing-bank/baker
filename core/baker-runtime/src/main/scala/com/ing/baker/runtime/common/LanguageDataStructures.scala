package com.ing.baker.runtime.common

sealed trait LanguageDataStructures {

  type Map[A, B]

  type Seq[A]

  type Set[A]

  type Option[A]

  type ConsumerFunction[A]

  type BiConsumerFunction[A, B]
}

object LanguageDataStructures {

  object Scala extends LanguageDataStructures {

    type Map[A, B] = scala.collection.immutable.Map[A, B]

    type Seq[A] = scala.collection.immutable.Seq[A]

    type Set[A] = scala.collection.immutable.Set[A]

    type Option[A] = scala.Option[A]

    type ConsumerFunction[A] = A => Unit

    type BiConsumerFunction[A, B] = (A, B) => Unit
  }

  object Java extends LanguageDataStructures {

    type Map[A, B] = java.util.Map[A, B]

    type Seq[A] = java.util.List[A]

    type Set[A] = java.util.Set[A]

    type Option[A] = java.util.Optional[A]

    type ConsumerFunction[A] = java.util.function.Consumer[A]

    type BiConsumerFunction[A, B] = java.util.function.BiConsumer[A, B]
  }

  trait LanguageApi {

    type Language <: LanguageDataStructures

    val language: Language
  }

  trait ScalaApi extends LanguageApi {

    type Language = Scala.type

    val language: Language = Scala
  }

  trait JavaApi extends LanguageApi {

    type Language = Java.type

    val language: Language = Java
  }
}


