Phases of SBR design:
=====================

* 2018-08-21: Started with an initial version of SBR from the perspective of one of the nodes (like node A). This node marks others' state as unreachable or up, and then decides if it is part of the majority or not. Then decides to leave cluster if it is in minority. Does not have the knowledge of the global real cluster state.
