Split Brain Resolver design journey:
====================================

### SplitBrainResolverV1 spec
Started with an initial version of SBR (SplitBrainResolver) algorithm
from the perspective of one of the nodes (like node A, or the first
node). This node observes others' state as unreachable or up, and then
decides if it is part of the majority or not. Then decides to leave
cluster if it is in minority. Does not have the knowledge of the global
real cluster state. Model_1 is testing the specification for all
cluster sizes from 2 to 6 (test cluster size can be increased later)

### Cluster/Node spec
Refactored the V1 spec into the spec of a Node which could be reusable
in the Cluster spec which describes the behaviour of a Cluster.
The algorithm of the Node is actually should be the real Split Brain
Resolver algorithm, and we should be able to define some safety and
liveliness properties of the Cluster formed by those Nodes.

### ClusterV2 spec
Started to use PlusCal language which translates into TLA+ language but
easier to model the whole cluster.
Starting N number of nodes each one reacting to some certain cluster
events (like MemberUp, MemberUnreachable, etc).

### ClusterV3 spec
Starting 6 processes for 3 node setup to simulate one node can receive
unreachable/up messages of other 2 nodes concurrently, so it makes 6
concurrent processes. First node starts as the leader and never changes
in this version. Availability (At least one node is up) invariant is
tested but due to huge state space being generated, the algorithm needs
a refinement.

### ClusterV4 spec
There is exactly N number of processes simulating N number of nodes
forming Cluster. LeaderUp/Down messages also implemented. But tests for
more than 3 nodes still create too many states which makes simulations
difficult to run locally.
