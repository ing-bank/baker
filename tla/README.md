Split Brain Resolver design journey:
====================================

### Version 1 (SplitBrainResolverV1 spec)
Started with an initial version of SBR (SplitBrainResolver) algorithm from the perspective of one of the nodes (like node A, or the first node).
This node observes others' state as unreachable or up, and then decides if it is part of the majority or not. 
Then decides to leave cluster if it is in minority. Does not have the knowledge of the global real cluster state.
Model_1 is testing the specification for all cluster sizes from 2 to 6 (test cluster size can be increased later)
