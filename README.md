# SIF formalization in Coq

Run once:

    ./configure

To run the proofs use `make`.

* [`src/SafeJoins.v`](src/SafeJoins.v) corresponds to Section 3, where
Theorem 3.2 is called `deadlock_avoidance`.

* [`src/CG.v`](src/CG.v) corresponds to Section 4.2.

* [`src/AccessHistory.v`](src/AccessHistory.v) corresponds to Section 4.3,
where Lemma 4.1 is called `wf_reduces`.

* [`src/SJ_CG.v`](src/SJ_CG.v) correspnds to Section 4.4, where Lemma 4.2
is called `sj_spec`.

* [`src/LocalInfo.v`](src/LocalInfo.v) corresponds to Section 4.5, where Theorem 4.3
corresponds to `wf_reduces_alt`.

