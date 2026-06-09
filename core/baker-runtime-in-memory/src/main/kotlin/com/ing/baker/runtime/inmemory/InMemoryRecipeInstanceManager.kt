package com.ing.baker.runtime.inmemory

import cats.effect.IO
import cats.effect.kernel.Async
import cats.effect.unsafe.IORuntime
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.RecipeInstanceManager
import com.ing.baker.runtime.model.RecipeInstanceStatus
import com.ing.baker.runtime.model.RecipeInstanceStatus.Active
import com.ing.baker.runtime.model.RecipeInstanceStatus.Deleted
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.model.recipeinstance.RecipeInstanceState
import com.ing.baker.runtime.scaladsl.RecipeInstanceMetadata
import org.slf4j.LoggerFactory
import scala.Option
import scala.jdk.CollectionConverters.MapHasAsScala
import scala.jdk.javaapi.DurationConverters.toScala
import scala.runtime.BoxedUnit
import java.time.Duration
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.Executors
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.TimeUnit
import scala.collection.immutable.Map as ScalaMap
import scala.collection.immutable.`Map$`.`MODULE$` as ScalaMapObject
import scala.collection.immutable.Set as ScalaSet

/**
 * Kotlin implementation of InMemoryRecipeInstanceManager.
 *
 * This class manages recipe instances in memory using a ConcurrentHashMap for thread-safe storage.
 * It periodically cleans up idle recipe instances based on the configured idle timeout.
 */
class InMemoryRecipeInstanceManager(
    retentionPeriodCheckInterval: Duration,
    private val idleTimeOut: Duration
) : RecipeInstanceManager<IO<*>>, AutoCloseable {

    private val logger = LoggerFactory.getLogger(javaClass.name)

    private val store = ConcurrentHashMap<String, RecipeInstanceStatus<IO<*>>>()
    private val scheduler: ScheduledExecutorService = Executors.newSingleThreadScheduledExecutor()

    init {
        // Start periodic cleanup task
        scheduler.scheduleAtFixedRate(
            {
                try {
                    @Suppress("UNCHECKED_CAST")
                    cleanupRecipeInstances(
                        toScala(idleTimeOut),
                        IO.asyncForIO() as Async<IO<*>>
                    ).unsafeRunSync(IORuntime.global())
                } catch (e: Exception) {
                    // Log error but don't stop the scheduler
                    // Errors are expected and handled silently to avoid stopping the cleanup task
                    logger.warn("Error during cleanup of idle recipe instances: $e")
                }
            },
            retentionPeriodCheckInterval.toMillis(),
            retentionPeriodCheckInterval.toMillis(),
            TimeUnit.MILLISECONDS
        )
    }

    @Suppress("UNCHECKED_CAST")
    override fun fetch(recipeInstanceId: String): IO<Option<RecipeInstanceStatus<IO<*>>>> =
        IO.delay {
            Option.apply(
                store.compute(recipeInstanceId) { _, status ->
                    when (status) {
                        is Active<*> -> {
                            Active(
                                status.recipeInstance() as RecipeInstance<IO<*>>,
                                System.currentTimeMillis()
                            )
                        }

                        else -> status
                    }
                }
            )
        } as IO<Option<RecipeInstanceStatus<IO<*>>>>

    override fun store(recipeInstance: RecipeInstance<IO<*>>, components: BakerComponents<IO<*>>): IO<BoxedUnit> =
        IO.delay {
            val status = Active(
                recipeInstance,
                System.currentTimeMillis()
            ) as RecipeInstanceStatus<IO<*>>
            store[recipeInstance.recipeInstanceId()] = status
        }.map { BoxedUnit.UNIT }

    override fun idleStop(recipeInstanceId: String): IO<BoxedUnit> = IO.unit()

    @Suppress("UNCHECKED_CAST")
    override fun getAllRecipeInstancesMetadata(): IO<ScalaSet<RecipeInstanceMetadata>> =
        IO.defer {
            store.entries.map { (recipeInstanceId, status) ->
                when (status) {
                    is Active<*> -> {
                        val recipeInstance = status.recipeInstance() as RecipeInstance<IO<*>>
                        recipeInstance.state().get().map { currentState ->
                            RecipeInstanceMetadata(
                                (currentState as RecipeInstanceState<*>).recipe().recipeId(),
                                recipeInstanceId,
                                currentState.createdOn()
                            )
                        }
                    }

                    is Deleted<*> -> {
                        IO.pure(
                            RecipeInstanceMetadata(
                                status.recipeId(),
                                recipeInstanceId,
                                status.createdOn()
                            )
                        )
                    }
                }
            }.fold(IO.pure(emptyList<RecipeInstanceMetadata>())) { acc, io ->
                // Sequence all IO operations and convert to Set
                acc.flatMap { list ->
                    (io as IO<RecipeInstanceMetadata>).map { metadata: RecipeInstanceMetadata -> list + metadata }
                }
            }.map { list: List<RecipeInstanceMetadata> ->
                scala.collection.immutable.`Set$`.`MODULE$`.from(
                    scala.jdk.CollectionConverters.IterableHasAsScala(list).asScala()
                ) as ScalaSet<RecipeInstanceMetadata>
            }
        } as IO<ScalaSet<RecipeInstanceMetadata>>

    override fun fetchAll(): IO<ScalaMap<String, RecipeInstanceStatus<IO<*>>>> =
        IO.delay {
            ScalaMapObject.from(MapHasAsScala(store).asScala())
                    as ScalaMap<String, RecipeInstanceStatus<IO<*>>>
        } as IO<ScalaMap<String, RecipeInstanceStatus<IO<*>>>>

    override fun remove(recipeInstanceId: String): IO<BoxedUnit> =
        idleStop(recipeInstanceId).flatMap {
            IO.delay {
                store.remove(recipeInstanceId)
            }
        }.map { BoxedUnit.UNIT }

    /**
     * Gracefully shutdown the cleanup scheduler.
     * Call this method when the instance manager is no longer needed to release resources.
     */
    override fun close() {
        scheduler.shutdown()
        try {
            if (!scheduler.awaitTermination(5, TimeUnit.SECONDS)) {
                scheduler.shutdownNow()
            }
        } catch (_: InterruptedException) {
            scheduler.shutdownNow()
        }
    }
}
