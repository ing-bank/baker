# Event Stores and Cluster Configuration

Baker keeps the state of your `RecipeInstances` using a technique called event sourcing, such technique still requires
you to save data into a data store if you want to restore state or move it around. Baker's event sourcing uses 
[Akka's Persistence](https://doc.akka.io/docs/akka/current/persistence.html), and even though you don't need to know how
it works, we recommend understanding the implications of it, specially when it comes to configuring and choosing the underlying 
data store. 

The two main categories you have is local vs distributed, the former being used mainly for testing which require no extra 
configuration, and the latter for production grade clusters, more specifically if you are going to use Baker on cluster 
mode, you NEED a distributed data store for Baker to work as expected. We recommend the usage of Cassandra, since it is 
the store the team has tested and used on production, for such you need to use a 
[plugin like this one.](https://doc.akka.io/docs/akka-persistence-cassandra/current/index.html)

## Configuration examples

`application.conf`

```config tab="Local non-cluster"
include "baker.conf"

akka.cluster.sharding.state-store-mode = persistence
akka.actor.allow-java-serialization = off
```

```config tab="Cluster with distributed store"
include "baker.conf"

service {

  actorSystemName = "CheckoutService"
  actorSystemName = ${?ACTOR_SYSTEM_NAME}

  clusterHost = "127.0.0.1"
  clusterHost = ${?CLUSTER_HOST}

  clusterPort = 2551
  clusterPort = ${?CLUSTER_PORT}

  seedHost = "127.0.0.1"
  seedHost = ${?CLUSTER_SEED_HOST}

  seedPort = 2551
  seedPort = ${?CLUSTER_SEED_PORT}

}

baker {
  actor {
    provider = "cluster-sharded"
  }

  cluster {
    nr-of-shards = 52
    seed-nodes = [
      "akka.tcp://"${service.actorSystemName}"@"${service.seedHost}":"${service.seedPort}]
  }
}

akka {

  actor {
    provider = "cluster"
  }

  persistence {
    # See https://doc.akka.io/docs/akka-persistence-cassandra/current/journal.html#configuration
    journal.plugin = "cassandra-journal"
    # See https://doc.akka.io/docs/akka-persistence-cassandra/current/snapshots.html#configuration
    snapshot-store.plugin = "cassandra-snapshot-store"
  }

  remote {
    log-remote-lifecycle-events = off
    netty.tcp {
      hostname = ${service.clusterHost}
      port = ${service.clusterPort}
    }
  }

  cluster {

    seed-nodes = [
      "akka.tcp://"${service.actorSystemName}"@"${service.seedHost}":"${service.seedPort}]

    # auto downing is NOT safe for production deployments.
    # you may want to use it during development, read more about it in the akka docs.
    auto-down-unreachable-after = 10s
  }
}
```
