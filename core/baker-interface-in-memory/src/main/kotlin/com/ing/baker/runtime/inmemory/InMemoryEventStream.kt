package com.ing.baker.runtime.inmemory

import cats.effect.IO
import com.ing.baker.runtime.model.EventStream
import com.ing.baker.runtime.scaladsl.BakerEvent
import scala.Function1
import scala.jdk.CollectionConverters.CollectionHasAsScala
import scala.runtime.BoxedUnit
import java.util.concurrent.ConcurrentLinkedQueue
import scala.collection.immutable.List as ScalaList

class InMemoryEventStream : EventStream<IO<*>> {

    private val store: ConcurrentLinkedQueue<Function1<BakerEvent, BoxedUnit>> = ConcurrentLinkedQueue()

    override fun fetchListeners(): IO<ScalaList<Function1<BakerEvent, BoxedUnit>>> =
        IO.pure(
            ScalaList.from(CollectionHasAsScala(store).asScala()) as ScalaList<Function1<BakerEvent, BoxedUnit>>
        )

    override fun subscribe(listenerFunction: Function1<BakerEvent, BoxedUnit>): IO<BoxedUnit> =
        IO.pure(store.add(listenerFunction)).map { BoxedUnit.UNIT }
}
