package com.ing.baker.runtime.actor.serialization

import akka.actor.ExtendedActorSystem
import com.esotericsoftware.kryo.Kryo
import com.ing.baker.petrinet.api.PetriNet
import com.twitter.chill.akka.AkkaSerializer
import com.twitter.chill.{IKryoRegistrar, KryoInstantiator}
import de.javakaffee.kryoserializers.guava._
import de.javakaffee.kryoserializers.jodatime.{JodaDateTimeSerializer, JodaLocalDateSerializer, JodaLocalDateTimeSerializer}

/**
  * This serializer was used in Baker 1.3.x for to serialize ingredient data.
  *
  * It is kept for backwards compatibility.
  */
@deprecated("Should not be actively used, kept for backwards compatibility", "2.0.0")
class KryoSerializer(system: ExtendedActorSystem) extends AkkaSerializer(system) {

  override def kryoInstantiator: KryoInstantiator = {
    super.kryoInstantiator.withRegistrar(new IKryoRegistrar {
      override def apply(kryo: Kryo): Unit = {
        // joda DateTime, LocalDate and LocalDateTime
        kryo.register(classOf[org.joda.time.DateTime], new JodaDateTimeSerializer())
        kryo.register(classOf[org.joda.time.LocalDate], new JodaLocalDateSerializer())
        kryo.register(classOf[org.joda.time.LocalDateTime], new JodaLocalDateTimeSerializer())

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
    })
  }
}