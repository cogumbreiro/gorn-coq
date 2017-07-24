# Known-Joins formalization in Coq

Run once:

    ./configure

To run the proofs use `make`.

* [`src/SafeJoins.v`](src/SafeJoins.v) corresponds to Section 3, where
Theorem 3.2 is called `deadlock_avoidance`.

* [`src/CG.v`](src/CG.v) defines computation graph from traces (Section 4.1).

* [`src/AccessHistory.v`](src/AccessHistory.v) defines shared memory, data-races,
  memory accesses and so on.

* [`src/SJ_CG.v`](src/SJ_CG.v) formalizes maps Safe-Joins in a computation
  graph (since the former operates on a trace); in short, this file formalizes
  known-sets at the node level (of a computation graph).

* [`src/LocalInfo.v`](src/LocalInfo.v) formalizes the local memory in
  a computation graph. The file also includes the connection between
  shared memory and local information. The main result is `wf_reduces_alt`.

