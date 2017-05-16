package com.ing.baker.runtime.actor

import akka.actor.ExtendedActorSystem
import com.esotericsoftware.kryo.Kryo
import com.twitter.chill.akka.AkkaSerializer
import com.twitter.chill.{IKryoRegistrar, KryoInstantiator}
import de.javakaffee.kryoserializers.guava._
import de.javakaffee.kryoserializers.jodatime.{JodaDateTimeSerializer, JodaLocalDateSerializer, JodaLocalDateTimeSerializer}
import org.joda.time._

class KryoSerializer(system: ExtendedActorSystem) extends AkkaSerializer(system) {
  override def kryoInstantiator: KryoInstantiator = {
    super.kryoInstantiator
      .withRegistrar(new ExtraKryoSerializersRegistrar)
  }

}

// these extra serializers are taken from the example here: https://github.com/magro/kryo-serializers
class ExtraKryoSerializersRegistrar extends IKryoRegistrar {
  override def apply(kryo: Kryo): Unit = {
    // joda DateTime, LocalDate and LocalDateTime
    kryo.register(classOf[DateTime], new JodaDateTimeSerializer())
    kryo.register(classOf[LocalDate], new JodaLocalDateSerializer())
    kryo.register(classOf[LocalDateTime], new JodaLocalDateTimeSerializer())

    // guava ImmutableList, ImmutableSet, ImmutableMap, ImmutableMultimap, ReverseList, UnmodifiableNavigableSet
    ImmutableListSerializer.registerSerializers(kryo)
    ImmutableSetSerializer.registerSerializers(kryo)
    ImmutableMapSerializer.registerSerializers(kryo)
    ImmutableMultimapSerializer.registerSerializers(kryo)
    ReverseListSerializer.registerSerializers(kryo)
    UnmodifiableNavigableSetSerializer.registerSerializers(kryo)

    // guava ArrayListMultimap, HashMultimap, LinkedHashMultimap, LinkedListMultimap, TreeMultimap
    ArrayListMultimapSerializer.registerSerializers(kryo)
    HashMultimapSerializer.registerSerializers(kryo)
    LinkedHashMultimapSerializer.registerSerializers(kryo)
    LinkedListMultimapSerializer.registerSerializers(kryo)
    TreeMultimapSerializer.registerSerializers(kryo)
  }
}