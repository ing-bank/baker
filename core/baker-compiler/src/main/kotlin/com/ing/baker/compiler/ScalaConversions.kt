package com.ing.baker.compiler

import scala.`$less$colon$less`
import scala.`None$`
import scala.Option
import scala.Predef
import scala.Some
import scala.Tuple2
import scala.collection.immutable.ArraySeq
import scala.collection.immutable.Seq
import scala.collection.immutable.Vector
import scala.concurrent.duration.FiniteDuration
import scala.jdk.CollectionConverters.ListHasAsScala
import scala.jdk.CollectionConverters.MapHasAsJava
import scala.jdk.CollectionConverters.MapHasAsScala
import scala.jdk.CollectionConverters.SeqHasAsJava
import scala.jdk.CollectionConverters.SetHasAsJava
import scala.jdk.CollectionConverters.SetHasAsScala
import kotlin.time.Duration

object ScalaConversions {

    inline val <reified T> List<T>.asScala get(): ArraySeq<T> = ArraySeq.unsafeWrapArray(toTypedArray())
    inline val <reified T> Sequence<T>.asScala get(): Vector<T> = Vector<T>.from(this.toList().asScala)

    val <T> Array<T>.asScala get(): Seq<T> = ListHasAsScala(this.toList()).asScala().toSeq()
    val <T> Set<T>.asScala get(): scala.collection.immutable.Set<T> = SetHasAsScala(this).asScala().toSet()
    val <K, V> Map<K, V>.asScala get(): scala.collection.immutable.Map<K, V> = MapHasAsScala(this).asScala().toMap(
        Predef.`$conforms`<Tuple2<K, V>>() as `$less$colon$less`<Tuple2<K, V>, Tuple2<K, V>>?)

    val <T> Seq<T>.asJava get(): List<T> = SeqHasAsJava(this).asJava()
    val <T> scala.collection.immutable.Set<T>.asJava get(): Set<T> = SetHasAsJava(this).asJava()
    val <K,V> scala.collection.immutable.Map<K,V>.asJava get(): Map<K,V> = MapHasAsJava(this).asJava()

    val Duration?.asScala get(): Option<FiniteDuration> =
        when (this) {
            null -> `None$`.`MODULE$` as Option<FiniteDuration>
            else -> Some(FiniteDuration(this.inWholeNanoseconds, java.util.concurrent.TimeUnit.NANOSECONDS))
        }

    val Int?.asScala get(): Option<Any> =
        when (this) {
            null -> `None$`.`MODULE$` as Option<Any>
            else -> Some(this)
        }

}
