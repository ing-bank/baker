package com.ing.baker.compiler

import scala.`$less$colon$less`
import scala.Predef
import scala.Tuple2
import scala.collection.immutable.Seq
import scala.jdk.CollectionConverters.*

object ScalaConversions {
    val <T> Array<T>.asScala get(): scala.collection.immutable.Seq<T> = ListHasAsScala(this.toList()).asScala().toSeq()
    val <T> List<T>.asScala get(): scala.collection.immutable.Seq<T> = ListHasAsScala(this).asScala().toSeq()
    val <T> Set<T>.asScala get(): scala.collection.immutable.Set<T> = SetHasAsScala(this).asScala().toSet()
    val <K, V> Map<K, V>.asScala get(): scala.collection.immutable.Map<K, V> = MapHasAsScala(this).asScala().toMap(
        Predef.`$conforms`<Tuple2<K, V>>() as `$less$colon$less`<Tuple2<K, V>, Tuple2<K, V>>?)

    val <T> Seq<T>.asJava get(): List<T> = SeqHasAsJava(this).asJava()
    val <T> scala.collection.immutable.Set<T>.asJava get(): Set<T> = SetHasAsJava(this).asJava()
    val <K,V> scala.collection.immutable.Map<K,V>.asJava get(): Map<K,V> = MapHasAsJava(this).asJava()
}

