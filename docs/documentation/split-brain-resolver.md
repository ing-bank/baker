# Split Brain Resolver

## Description
Note: This feature is applicable to clustered baker configuration. If
your Baker application is using local actors, thus not using akka
cluster, a Split Brain Resolver is not needed.

Baker library, when configured to be a cluster, runs in an akka cluster
to distribute the baker processes over multiple nodes. Running a
cluster with multiple nodes with shared state has some difficulties to
tackle in some network failure scenarios, like network partitions.

When there's a network partition in a cluster, the nodes at the
different sides of the partition cannot receive messages from each
other and eventually diverge their states unless it is a network
hick-up. When this happens, you need a mechanism to prevent state
inconsistency, i.e. by stopping nodes at one side of the partition, so
the nodes at the surviving side still run with consistent states.

A Split Brain Resolver algorithm for Akka prevents inconsistent states
during network partitions, or huge network delays, or non-responding
cluster members.

Baker Split Brain Resolver is a general purpose implementation for Akka
which could be configured for a baker cluster as well as for another
akka cluster without baker.

## Strategies
The current version of the Split Brain Resolver algorithm supports only
the `Majority` strategy which makes the majority of the nodes survive
and downs (terminates) the nodes at the minority side of the network
partition. In case of the number of nodes on each side of the network
partition are equal, the side with the oldest akka node survives. By
deciding to down one side, you do not end up with 2 akka clusters
during the network partition.

There could be other strategies implemented later, for now the
`Majority` strategy works for most of the use cases. You can read about
other possible strategies supported by the commercial Lightbend Split
Brain Resolver [here](https://developer.lightbend.com/docs/akka-commercial-addons/current/split-brain-resolver.html#strategies).

`Majority` strategy is configured by default, so you do not need extra
configuration for this.

## How to use
In order to use Baker `SplitBrainResolver`, first of all, you need to add
baker-split-brain-resolver dependency to your project. See example
below:

``` scala tab="Sbt"
libraryDependencies += "com.ing.baker" %% "baker-split-brain-resolver" % "2.0.2"
```

``` xml tab="Maven"
<dependency>
  <groupId>com.ing.baker</groupId>
  <artifactId>baker-split-brain-resolver_2.12</artifactId>
  <version>2.0.2</version>
</dependency>
```

Then the algorithm needs to be configured as the akka downing provider
and the `stable-after` config needs to set to some duration depending
on your cluster size.

`stable-after` config is needed to decide on how quickly to react on
the akka cluster state changes. Very short durations may allow quicker
'downing' decisions for unreachable nodes, but may also cause to down
some nodes unnecessarily too early. Please see the suggested values for
this in the [documentation](https://developer.lightbend.com/docs/akka-commercial-addons/current/split-brain-resolver.html#stable-after)
of the commercial Lightbend Split Brain Resolver.

One other akka cluster configuration suggested keep in sync with
`stable-after` is the `akka.cluster.down-removal-margin` config.
The suggested values and more information on this config can be found
in the [Cluster Singleton and Cluster Sharding](https://developer.lightbend.com/docs/akka-commercial-addons/current/split-brain-resolver.html#cluster-singleton-and-cluster-sharding)
section of the commercial Lightbend Split Brain Resolver.

Example config for a baker cluster having less than 10 nodes is the
following:
```
akka.cluster.down-removal-margin = 7 seconds
akka.cluster.downing-provider-class = com.ing.baker.runtime.actor.downing.SplitBrainResolver

baker-split-brain-resolver {
  stable-after = 7 seconds
}
```

