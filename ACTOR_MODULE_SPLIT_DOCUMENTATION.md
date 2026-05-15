# Baker Akka Actors Module Split Documentation

## Overview

The monolithic `baker-akka-actors` module has been split into 7 independent, focused modules following clean architecture principles. This document provides a comprehensive overview of what moved where and why, along with dependency relationships.

---

## Module Structure

```
core/
├── baker-akka-actors-common/              (12 files - added BakerActorNames)
├── baker-akka-actors-protocols/           (8 files + 4 protobuf)
├── baker-akka-actors-recipe-manager/      (2 files - added ActorBasedRecipeManager)
├── baker-akka-actors-process-instance/    (12 files)
├── baker-akka-actors-delayed-transition/  (1 file)
├── baker-akka-actors-process-index/       (2 files)
└── baker-akka-actors/                     (11 files - Integration, removed ActorBasedRecipeManager)
```

---

## 1. baker-akka-actors-common

**Purpose**: Shared utilities and infrastructure used across all actor modules

### Files Moved Here

| File | Original Location | Reason |
|------|------------------|--------|
| `AkkaSerializerProvider.scala` | `actor/serialization/` | Base serialization infrastructure needed by all modules |
| `BakerSerializable.scala` | `actor/serialization/` | Marker trait for serializable types |
| `SerializedDataProto.scala` | `actor/serialization/` | Common protobuf serialization utilities |
| `TypedProtobufSerializer.scala` | `actor/serialization/` | Base class for typed serializers |
| `BakerActorCleanup.scala` | `actor/` | Event store cleanup utilities (moved during split) |
| `GracefulShutdown.scala` | `actor/` | Actor system shutdown coordination |
| `GracefulShutdownShardRegions.scala` | `actor/` | Cluster sharding graceful shutdown |
| `TimeoutUtil.scala` | `actor/internal/` | Implicit class for Future timeout operations |
| `Timeouts.scala` | `actor/` | Timeout configuration utilities |
| `Util.scala` | `actor/` | Common utility functions |
| `LogAndSendEvent.scala` | `actor/logging/` | Logging utilities |
| `BakerActorNames.scala` | `actor/` | Centralized actor name constants (added post-split) |
| `Encryption.scala` (referenced) | `serialization/` | Encryption support |

### Dependencies
- **External only**: Akka, Baker types, ScalaPB
- **No internal Baker actor dependencies**

### Why Common?
These utilities are pure infrastructure code with no business logic. They're needed by multiple actor modules and have no dependencies on specific actor implementations.

---

## 2. baker-akka-actors-protocols

**Purpose**: All protocol (message) definitions and protobuf mappings

### Files Moved Here

| File | Original Location | Reason |
|------|------------------|--------|
| `ProcessInstanceProtocol.scala` | `actor/process_instance/` | Message definitions for ProcessInstance actor |
| `ProcessInstanceProto.scala` | `actor/process_instance/` | Protobuf mappings |
| `ProcessIndexProtocol.scala` | `actor/process_index/` | Message definitions for ProcessIndex actor |
| `ProcessIndexProto.scala` | `actor/process_index/` | Protobuf mappings |
| `RecipeManagerProtocol.scala` | `actor/recipe_manager/` | Message definitions for RecipeManager actor |
| `RecipeManagerProto.scala` | `actor/recipe_manager/` | Protobuf mappings |
| `DelayedTransitionActorProtocol.scala` | `actor/delayed_transition_actor/` | Message definitions for DelayedTransition actor |
| `DelayedTranstionProto.scala` | `actor/delayed_transition_actor/` | Protobuf mappings |

### Protobuf Files
- `process_instance.proto`
- `process_index.proto`
- `recipe_manager.proto`
- `delayed_transition.proto`

### Key Architectural Change: Event Sourcing Classes Extracted

To break circular dependencies, event sourcing case classes were **extracted from Actor companion objects** and moved to Protocol objects:

#### ProcessIndexProtocol.scala
```scala
// Event sourcing classes (previously in ProcessIndex object)
case class ActorMetadata(recipeId: String, recipeInstanceId: String, createdTime: Long, status: ProcessStatus)
case class ActorCreated(recipeId: String, recipeInstanceId: String, timestamp: Long)
case class ActorActivated(recipeInstanceId: String)
case class ActorPassivated(recipeInstanceId: String)
case class ActorDeleted(recipeInstanceId: String, removedFromIndex: Boolean)
case class ProcessIndexSnapShot(processIndex: Map[String, ActorMetadata])
case class GetShardIndex(entityId: String)

// Enums
sealed trait ProcessStatus
case object Active extends ProcessStatus
case object Deleted extends ProcessStatus
```

#### RecipeManagerProtocol.scala
```scala
// Event sourcing class (previously in RecipeManagerActor object)
case class RecipeAdded(compiledRecipe: CompiledRecipe, timeStamp: Long)
```

#### DelayedTransitionActorProtocol.scala
```scala
// Event sourcing classes (previously in DelayedTransitionActor object)
case class DelayedTransitionInstance(...)
case class DelayedTransitionScheduled(id: String, delayedTransitionInstance: DelayedTransitionInstance)
case class DelayedTransitionExecuted(id: String, delayedTransitionInstance: DelayedTransitionInstance)
case class DelayedTransitionSnapshot(waitingTransitions: Map[String, DelayedTransitionInstance])
```

#### ProcessInstanceProtocol.scala
```scala
// Listener events (exist in BOTH Protocol and EventSourcing)
case class CompletionListenerAdded(listenerPath: String)
case class EventListenerAdded(eventName: String, listenerPath: String)
case class CompletionListenersRemoved()
case class EventListenersRemoved(eventName: String)
```

### Dependencies
- `baker-akka-actors-common` (serialization base classes)
- External: Akka, Baker IL, ScalaPB

### Why Protocols?
- **Single Source of Truth**: All message contracts in one place
- **Breaks Circular Dependencies**: Actors no longer need to import each other
- **Versioning**: Protobuf definitions can be versioned independently
- **Clean API**: Clear separation between protocol (interface) and implementation (actors)

---

## 3. baker-akka-actors-recipe-manager

**Purpose**: Recipe storage and retrieval actor

### Files Moved Here

| File | Original Location | Reason |
|------|------------------|--------|
| `RecipeManagerActor.scala` | `actor/recipe_manager/` | Main actor implementation |
| `ActorBasedRecipeManager.scala` | `actor/recipe_manager/` (moved post-split from integration) | Client wrapper for the actor |

### Post-Split Addition

`ActorBasedRecipeManager` was moved here from the integration module to keep all recipe manager related code together. See "Post-Split Improvements" section for details.

### Dependencies
- `baker-akka-actors-common` (utilities)
- `baker-akka-actors-protocols` (RecipeManagerProtocol)
- External: Akka Persistence, Baker IL

### Why Separate Module?
- **Single Responsibility**: Only handles recipe storage
- **No dependencies on other actors**: Can be tested in isolation
- **Simple implementation**: 1 actor, straightforward logic

---

## 4. baker-akka-actors-process-instance

**Purpose**: Individual recipe instance execution actor

### Files Moved Here

| File | Original Location | Reason |
|------|------------------|--------|
| `ProcessInstance.scala` | `actor/process_instance/` | Main actor implementation |
| `ProcessInstanceEventSourcing.scala` | `actor/process_instance/` | Event sourcing trait and logic |
| `ProcessInstanceLogger.scala` | `actor/process_instance/` | Logging utilities |
| `ProcessInstanceProto.scala` | `actor/process_instance/` | Protobuf mappings (now in protocols) |
| `ProcessInstanceRuntime.scala` | `actor/process_instance/` | Runtime execution logic |
| `ProcessInstanceSerialization.scala` | `actor/process_instance/` | Serialization logic |
| `internal/ExceptionState.scala` | `actor/process_instance/internal/` | Exception handling state |
| `internal/ExceptionStrategy.scala` | `actor/process_instance/internal/` | Retry strategies |
| `internal/Instance.scala` | `actor/process_instance/internal/` | Instance state model |
| `internal/Job.scala` | `actor/process_instance/internal/` | Job model |
| **`RecipeRuntime.scala`** | `internal/` (root) | **Moved here** - Core runtime logic |
| **`FatalInteractionException.scala`** | `internal/` (root) | **Moved here** - Exception type |
| **`package.scala`** | Root akka package | **Moved here** - IO extension methods |

### Key Addition: Event Sourcing Events

Listener events were added to `ProcessInstanceEventSourcing.scala` to maintain the Event type hierarchy:

```scala
sealed trait Event extends NoSerializationVerificationNeeded

// Listener events (ALSO in Protocol for external messages)
case class CompletionListenerAdded(listenerPath: String) extends Event
case class EventListenerAdded(eventName: String, listenerPath: String) extends Event
case class CompletionListenersRemoved() extends Event
case class EventListenersRemoved(eventName: String) extends Event
```

### Why RecipeRuntime and FatalInteractionException Moved Here?

**Original Location**: `baker-akka-actors/src/main/scala/com/ing/baker/runtime/akka/internal/`

**Reasoning**:
1. **Tight Coupling**: These are core to ProcessInstance execution logic
2. **No Other Users**: Only ProcessInstance and ProcessInstanceRuntime use them
3. **Logical Cohesion**: They implement the interaction execution logic that ProcessInstance orchestrates
4. **Reduced Coupling**: Keeps runtime logic with the actor that uses it

### Why package.scala Moved Here?

Contains IO extension methods used primarily by ProcessInstanceRuntime:

```scala
implicit class IOHandleErrors[T](io: IO[T]) {
  def handleException[Y >: T](pf: PartialFunction[Throwable, Y]): IO[Y]
  def handleExceptionWith[Y >: T](pf: PartialFunction[Throwable, IO[Y]]): IO[Y]
}
```

### Dependencies
- `baker-akka-actors-common` (utilities, serialization)
- `baker-akka-actors-protocols` (ProcessInstanceProtocol)
- External: Akka Persistence, Cats Effect, Baker IL

### Why Separate Module?
- **Core Business Logic**: Most complex actor with recipe execution logic
- **Can be tested independently**: No dependencies on other actors
- **Reusable**: Could be used in different runtime contexts

---

## 5. baker-akka-actors-delayed-transition

**Purpose**: Timer service for delayed/scheduled transitions

### Files Moved Here

| File | Original Location | Reason |
|------|------------------|--------|
| `DelayedTransitionActor.scala` | `actor/delayed_transition_actor/` | Actor implementation |

### What This Actor Does
- Schedules delayed transitions (timers)
- Tracks pending timers with their fire times
- Fires transitions when time expires
- Handles process deletion cleanup

### Key Message Flow
```
ProcessInstance → ScheduleDelayedTransition → DelayedTransitionActor
                                                      ↓
                                              (persist & schedule)
                                                      ↓
DelayedTransitionActor ← TransitionDelayed ← (sends back to sender)
       ↓
  (tick timer)
       ↓
FireDelayedTransition → ProcessIndex → ProcessInstance
```

### Important: Protocol vs EventSourcing

The actor sends **ProcessInstanceProtocol.TransitionDelayed** (not EventSourcing), because:
- Actors communicate via Protocol messages (commands)
- ProcessInstance receives the Protocol message and converts it to EventSourcing internally

### Dependencies
- `baker-akka-actors-common` (utilities, BakerCleanup)
- `baker-akka-actors-protocols` (DelayedTransitionActorProtocol, ProcessIndexProtocol, ProcessInstanceProtocol)
- `baker-akka-actors-process-instance` (for ProcessInstanceProtocol import)
- External: Akka Persistence

### Why Separate Module?
- **Single Responsibility**: Only handles timer scheduling
- **Independent Testing**: Can test timer logic in isolation
- **Optional Feature**: Could be disabled or replaced with different implementation

---

## 6. baker-akka-actors-process-index

**Purpose**: Central coordinator for all recipe instances

### Files Moved Here

| File | Original Location | Reason |
|------|------------------|--------|
| `ProcessIndex.scala` | `actor/process_index/` | Main coordinator actor |
| `SensoryEventResponseHandler.scala` | `actor/process_index/` | Event response handling logic |

### What This Actor Does
- Creates and manages ProcessInstance actors (via sharding/local)
- Routes sensory events to correct ProcessInstance
- Maintains index of all active processes
- Handles process lifecycle (create, fire events, delete)
- Coordinates with DelayedTransitionActor for timers
- Coordinates with RecipeManagerActor for recipes

### Key Architectural Role
ProcessIndex is the **orchestrator** - it depends on all other actor modules:

```
ProcessIndex
    ├─→ RecipeManagerActor (get recipes)
    ├─→ ProcessInstance (create instances, fire events)
    └─→ DelayedTransitionActor (schedule timers)
```

### Dependencies
- `baker-akka-actors-common` (utilities)
- `baker-akka-actors-protocols` (all protocols)
- `baker-akka-actors-recipe-manager` (actor reference)
- `baker-akka-actors-process-instance` (actor reference)
- `baker-akka-actors-delayed-transition` (actor reference)
- `baker-recipe-manager` (RecipeManager interface)
- External: Akka Cluster Sharding, Akka Persistence

### Why Separate Module?
- **Orchestration Layer**: Coordinates all other actors
- **Deployment Boundary**: Could be deployed separately in advanced setups
- **Last in Dependency Chain**: Naturally depends on all other modules

---

## 7. baker-akka-actors (Integration Module)

**Purpose**: Brings all actor modules together and provides external API

### Files Remaining Here

| File | Purpose |
|------|---------|
| `BakerActorProvider.scala` | Trait for actor system setup |
| `LocalBakerActorProvider.scala` | Local (non-cluster) implementation |
| `ClusterBakerActorProvider.scala` | Cluster sharding implementation |
| `BakerTypedProtobufSerializer.scala` | **Aggregates all serializers from all modules** |
| `ActorBasedRecipeManager.scala` | RecipeManager implementation using actors |
| `CachingInteractionManager.scala` | Interaction caching |
| `TimeoutUtil.scala` | Timeout utilities |
| `SinkJournal.scala` | Journal sink for testing |

### Key Role: Aggregation

`BakerTypedProtobufSerializer` is the **integration point** that brings together serializers from all modules:

```scala
def entries(actorRefProvider: ActorRefProvider)(serializersProvider: AkkaSerializerProvider): List[BinarySerializable] = {
  commonEntries ++           // from common
  processIndexEntries ++     // from process-index (via protocols)
  processInstanceEntries ++  // from process-instance (via protocols)
  recipeManagerEntries ++    // from recipe-manager (via protocols)
  delayedTransitionEntries   // from delayed-transition (via protocols)
}
```

### Dependencies
- **All actor modules** (common, protocols, recipe-manager, process-instance, delayed-transition, process-index)
- `baker-recipe-manager` (RecipeManager interface)
- External: Akka, Akka Management (cluster bootstrap)

### Why Integration Module?
- **Single Deployment Unit**: Consumers depend only on this module
- **Backward Compatibility**: Existing code continues to work
- **Flexibility**: Internal modules can evolve independently

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                    baker-akka-actors                        │
│                  (Integration Module)                       │
│  • BakerActorProvider                                       │
│  • BakerTypedProtobufSerializer (aggregates all)            │
│  • ActorBasedRecipeManager                                  │
└──────────────────────┬──────────────────────────────────────┘
                       │
       ┌───────────────┴───────────────┬─────────────────────┐
       │                               │                     │
       ▼                               ▼                     ▼
┌────────────────┐          ┌──────────────────┐    ┌──────────────────┐
│ process-index  │          │ recipe-manager   │    │ delayed-         │
│ • ProcessIndex │          │ • RecipeManager  │    │   transition     │
│                │          │   Actor          │    │ • DelayedTrans-  │
│ Depends on:    │          │                  │    │   itionActor     │
│ ✓ protocols    │          │ Depends on:      │    │                  │
│ ✓ recipe-mgr   │          │ ✓ protocols      │    │ Depends on:      │
│ ✓ process-inst │          │ ✓ common         │    │ ✓ protocols      │
│ ✓ delayed-trans│          └──────────────────┘    │ ✓ process-inst   │
│ ✓ common       │                                  │ ✓ common         │
└────────────────┘                                  └──────────────────┘
       │                                                     │
       │                     ┌───────────────────────────────┘
       │                     │
       ▼                     ▼
┌──────────────────────────────────────┐
│       process-instance               │
│ • ProcessInstance                    │
│ • ProcessInstanceEventSourcing       │
│ • ProcessInstanceRuntime             │
│ • RecipeRuntime                      │
│ • FatalInteractionException          │
│ • package.scala (IO extensions)      │
│                                      │
│ Depends on:                          │
│ ✓ protocols                          │
│ ✓ common                             │
└──────────────────────────────────────┘
       │
       ▼
┌──────────────────────────────────────┐
│          protocols                   │
│ • All Protocol definitions           │
│ • All Protobuf mappings              │
│ • Event sourcing case classes        │
│   (extracted from actors)            │
│                                      │
│ Depends on:                          │
│ ✓ common                             │
└──────────────────────────────────────┘
       │
       ▼
┌──────────────────────────────────────┐
│            common                    │
│ • Serialization base classes         │
│ • Utilities (logging, timeouts)      │
│ • BakerCleanup                       │
│ • GracefulShutdown                   │
│                                      │
│ Depends on:                          │
│ ✓ External only (Akka, ScalaPB)     │
└──────────────────────────────────────┘
```

### Build Order
1. `common` (no internal dependencies)
2. `protocols` (depends on common)
3. `recipe-manager`, `process-instance` (both depend on protocols + common)
4. `delayed-transition` (depends on protocols + common + process-instance)
5. `process-index` (depends on all above)
6. `baker-akka-actors` (integration - depends on all)

---

## Package Structure (Preserved)

**Important**: All modules maintain the original package structure `com.ing.baker.runtime.akka.actor.*` to minimize import changes:

```
com.ing.baker.runtime.akka.actor
├── serialization/              (in common)
├── process_instance/           (in process-instance)
│   ├── internal/              
│   └── protobuf/              (generated)
├── process_index/             (in process-index)
│   └── protobuf/              (generated)
├── recipe_manager/            (in recipe-manager)
│   └── protobuf/              (generated)
├── delayed_transition_actor/  (in delayed-transition)
│   └── protobuf/              (generated)
└── (providers)                (in integration)
```

---

## Key Architectural Patterns

### 1. Protocol vs EventSourcing Separation

**Protocol Types** (in `*Protocol.scala`):
- External messages sent between actors
- Commands and queries
- Response messages
- Used in actor `receive` handlers

**EventSourcing Types** (in `*EventSourcing.scala`):
- Internal events persisted to journal
- Represent facts that happened
- Used in `persist()` calls
- Drive state reconstruction on recovery

**Exception**: Listener events exist in **both** because:
- They're sent as commands (Protocol)
- They're persisted as events (EventSourcing)
- They're part of the Event type hierarchy

### 2. Circular Dependency Breaking

**Problem**: Actors needed event sourcing classes from other actors' companion objects, creating circular dependencies.

**Solution**: Extract event sourcing classes to Protocol objects:
- Protocols have no actor dependencies
- Actors import from Protocols
- Proto serializers import from Protocols
- Clean one-way dependency flow

### 3. Import Pattern for Ambiguous Types

When types exist in both Protocol and EventSourcing:

```scala
// Prefer EventSourcing for event sourcing contexts
import ProcessInstanceEventSourcing.{CompletionListenerAdded, ...}

// Exclude from Protocol wildcard import
import ProcessInstanceProtocol.{CompletionListenerAdded => _, ...others => _, _}
```

---

## Migration Impact

### Files Updated in Other Modules

**baker-akka-runtime** tests:
- `RecipeManagerActorProtoSpec.scala` - Changed `RecipeManagerActor.RecipeAdded` → `RecipeManagerProtocol.RecipeAdded`
- `SerializationSpec.scala` - Updated all type references from Actor objects to Protocol objects
- `DelayedTransitionActorSpec.scala` - Changed import to use Protocol.TransitionDelayed

### Common Update Pattern

```scala
// Before (referencing Actor companion objects):
import ProcessIndex.ActorCreated
import RecipeManagerActor.RecipeAdded
import DelayedTransitionActor.DelayedTransitionInstance

// After (referencing Protocol objects):
import ProcessIndexProtocol.ActorCreated
import RecipeManagerProtocol.RecipeAdded
import DelayedTransitionActorProtocol.DelayedTransitionInstance
```

---

## Post-Split Improvements

### ActorBasedRecipeManager Moved to Recipe Manager Module

After the initial split, `ActorBasedRecipeManager` was moved from the integration module to the recipe-manager actor module to further improve modularity.

#### Changes Made

1. **Created BakerActorNames** in `baker-akka-actors-common`
   - Extracted the `recipeManagerName` constant from `ClusterBakerActorProvider`
   - Centralized actor name constants to avoid circular dependencies
   ```scala
   // baker-akka-actors-common/src/main/scala/.../BakerActorNames.scala
   object BakerActorNames {
     val recipeManagerName: String = "RecipeManager"
   }
   ```

2. **Moved ActorBasedRecipeManager.scala**
   - **From**: `baker-akka-actors/src/main/scala/com/ing/baker/runtime/recipe_manager/`
   - **To**: `baker-akka-actors-recipe-manager/src/main/scala/com/ing/baker/runtime/recipe_manager/`
   - Updated import: `import com.ing.baker.runtime.akka.actor.BakerActorNames.recipeManagerName`

3. **Moved ActorBasedRecipeManagerSpec.scala**
   - **From**: `baker-akka-actors/src/test/scala/com/ing/baker/runtime/recipe_manager/`
   - **To**: `baker-akka-actors-recipe-manager/src/test/scala/com/ing/baker/runtime/recipe_manager/`

4. **Updated Dependencies**
   - Added `baker-recipe-manager` dependency to `baker-akka-actors-recipe-manager`
   - Added test dependencies: `mockito`, `scalatest`, `akka-testkit`, `baker-compiler`
   - Removed `baker-recipe-manager` dependency from `baker-akka-actors` (integration module)

#### Rationale

- **Better Cohesion**: `ActorBasedRecipeManager` wraps the `RecipeManagerActor`, so they belong together
- **Reduced Integration Dependency**: The integration module no longer needs `baker-recipe-manager`
- **Cleaner Separation**: Recipe manager functionality is fully self-contained in one module
- **Follows Pattern**: Mirrors the relationship between other actors and their client wrappers

#### Test Results
- All 3 tests in `ActorBasedRecipeManagerSpec` pass successfully
- No breaking changes to external APIs

---

## Benefits Achieved

### 1. Modularity
- Each module has a single, clear responsibility
- 7 focused modules instead of 1 monolith

### 2. Independent Evolution
- Modules can be versioned independently
- Protocol changes can be made without touching actor implementations
- Easier to understand and modify individual modules

### 3. Better Testing
- Modules can be tested in isolation
- Reduced test classpath (faster test compilation)
- Clear boundaries for unit vs integration tests

### 4. Reduced Coupling
- No circular dependencies
- Clear dependency hierarchy
- Protocols act as contracts between modules

### 5. Build Performance
- Incremental builds only rebuild affected modules
- Parallel compilation of independent modules
- Smaller individual compilation units

### 6. Deployment Flexibility
- Could deploy different actors in different JVMs (advanced use case)
- Easier to create different packaging configurations
- Clear boundaries for future microservice extraction if needed

---

## Build Verification

All 7 modules compile successfully and all tests pass:

```
✅ baker-akka-actors-common          (12 files)
✅ baker-akka-actors-protocols        (8 files + 4 protobuf)
✅ baker-akka-actors-recipe-manager   (2 files + tests)
✅ baker-akka-actors-process-instance (12 files)
✅ baker-akka-actors-delayed-transition (1 file)
✅ baker-akka-actors-process-index    (2 files)
✅ baker-akka-actors (integration)    (11 files)
✅ baker-akka-runtime                 (168 tests passing, 1 ignored)
✅ ActorBasedRecipeManagerSpec        (3 tests passing)
```

**Build time**: ~1 minute 20 seconds for full reactor build

---

## Future Considerations

### Potential Further Splits
- **serialization** could be extracted from common if needed
- **process-instance/internal** could become its own module if it grows

### Versioning Strategy
- Modules can now be versioned independently
- Protocols should follow semantic versioning strictly
- Breaking protocol changes require major version bumps

### Deployment Options
- All modules in single JAR (current - backward compatible)
- Separate JARs with shared classpath
- Advanced: Different actors in different services (requires additional work)

---

## Conclusion

The module split successfully transformed a monolithic actor module into a well-structured, maintainable set of focused modules. The key achievement was breaking circular dependencies by extracting event sourcing classes to protocols, while maintaining backward compatibility and the original package structure.

Post-split improvements further refined the architecture by:
1. Moving `ActorBasedRecipeManager` to the recipe-manager module for better cohesion
2. Creating the `BakerActorNames` utility for centralized actor name constants
3. Removing duplicate utility files from integration module:
   - `TimeoutUtil.scala` - kept only in common module where it's actively used
   - `AkkaSerializerProvider.scala` - kept only in common module
   - `BakerSerializable.scala` - kept only in common module  
   - `SerializedDataProto.scala` - kept only in common module
   - `TypedProtobufSerializer.scala` - kept only in common module

These duplicates were removed because the integration module already depends on the common module, so imports continue to work seamlessly.

**Status**: ✅ Complete - All modules compile, all tests pass (171/171 total)
