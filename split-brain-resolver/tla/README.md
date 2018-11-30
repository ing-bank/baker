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
The algorithm of the Node should actually be the real Split Brain
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
There is N number of processes simulating N number of nodes
forming Cluster (model variables). LeaderUp/Down messages also
implemented together with oldestNode election if it is not a member 
anymore. ConsistentLeader and NoSplitBrain invariants fail quickly 
because the leader and oldestNode variables are process local and they 
see a different state with random state transitions. Maybe these 
variables should be defined as global truths for simplicity. 

### ClusterV5 Spec
Moved the variables out from the process scope so that we can also
update the state of other nodes/processes when we receive some certain
messages. i.e. Receiving MemberRemoved(node1) message means removing
node1 from my state, but also assuming that node1 is already left the
cluster  or terminated, so we also update its members set as an empty
set. Fixed lots of unrealistic corner cases found by the TLA model
checker in the algorithm so that it does not randomly generate states
but knows about how the system behaves. This generates less number of
states and we are able to improve the algorithm step by step.

### ClusterV6 Spec
Added the deadNodes:Set variable to keep track of the nodes going down,
so they do not come up again. This is the assumption for this version
of the algorithm. They start as a healthy cluster and do not come back
after they are down.
* A temporal property is also introduced: After a split brain state we
are able to recover eventually and go to consistent state later.
SplitBrainRecovery == SplitBrain ~> (~SplitBrain /\ ConsistentLeader)
* Result: TLA Model Checker finds a Split Brain situation which does
not eventually recover to a consistent state which should be
investigated further to see whether an improvement in the algorithm is
possible or not.
