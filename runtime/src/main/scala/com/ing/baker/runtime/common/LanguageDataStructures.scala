package com.ing.baker.runtime.common

sealed trait LanguageDataStructures {

  type Map[A, B]

  type Seq[A]

  type Set[A]

  type Option[A]
}

object LanguageDataStructures {

  object Scala extends LanguageDataStructures {

    type Map[A, B] = scala.collection.immutable.Map[A, B]

    type Seq[A] = scala.collection.Seq[A]

    type Set[A] = scala.collection.immutable.Set[A]

    type Option[A] = scala.Option[A]
  }

  object Java extends LanguageDataStructures {

    type Map[A, B] = java.util.Map[A, B]

    type Seq[A] = java.util.List[A]

    type Set[A] = java.util.Set[A]

    type Option[A] = java.util.Optional[A]
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


