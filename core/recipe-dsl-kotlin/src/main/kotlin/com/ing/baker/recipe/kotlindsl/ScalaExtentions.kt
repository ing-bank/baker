package com.example.demo

import scala.collection.JavaConverters


object ScalaExtensions {

    fun <A> Iterable<A>.toScalaSeq(): scala.collection.immutable.Seq<A> =
        JavaConverters.asScalaIteratorConverter(this.iterator()).asScala().toSeq()

    fun <A> Iterable<A>.toScalaSet(): scala.collection.immutable.Set<A> =
        JavaConverters.asScalaIteratorConverter(this.iterator()).asScala().toSet()

    fun <K, V> Map<K, V>.toScalaMap(): scala.collection.immutable.Map<K, V> =
        scala.collection.immutable.Map.from(JavaConverters.asScala(this))


    fun <A> scala.collection.immutable.Seq<A>.toJavaIterable(): Iterable<A> =
        JavaConverters.asJava(this)

    fun <A> scala.collection.immutable.List<A>.toJavaIterable(): Iterable<A> =
        JavaConverters.asJava(this)
    fun <A> scala.collection.immutable.Set<A>.toJavaIterable(): Iterable<A> =
        JavaConverters.asJava(this)
}