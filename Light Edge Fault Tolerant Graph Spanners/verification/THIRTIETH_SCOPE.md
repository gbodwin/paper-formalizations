## Actual empirical-voting correctness (174-module packet)

The deterministic good-event implication of corrected Lemma 31 is now joined to
a literal finite empirical estimator and threshold-voting recursion. Each tape
entry is an actual list of finite sampled edge sets at the current state,
candidate and host. Samples are clipped to current non-seed edges and the
actual host is retained. The estimate is the fraction of failed weighted-distance
tests, with explicit total-division value zero on an empty list.

For p=1/(2f), the finite Bernoulli law itself gives probability at least 1/2
of avoiding any at most f faults, including f=1. An actual fault witness and
fault-disjoint host imply failure of the sampled distance test. With error at
most 1/8 on the actual reached states, this forces a vote at threshold 3/8.
The output recursion then proves the full all-fault walk-spanner guarantee.

The forest/component hosts are internally constructed from an actual q-fault
connectivity preserver. There is no supplied packing, congestion/count oracle,
or assumed acceptance behavior in the final theorems. They cover Algorithm 2's
one-vote insertion predicate at q=2f, and Algorithm 3's exact integer parameters
q=floor((2+eta)f), h=floor(eta*f)+1 for every eta>0. The common recursion scans
all eligible hosts; only its insertion predicate, not short-circuit runtime,
is identified with Algorithm 2. Finite simple graphs, f>0, stretch>=1 and globally
nonnegative weights are explicit.

These are classical finite mathematical graph-test recursions, not an executable
shortest-path implementation or a paid runtime model. Accuracy is an explicit
simultaneous event on the actual visited states. The probability law for the tape,
adaptive concentration (Lemma 30), accepted-output lightness (Lemmas 32–33), and
polynomial-time preserver/packing construction and distance testing remain open.
The sampled output is not identified with the older exhaustive-fault greedy
output whose corrected exact-extremal lightness bounds are already proved.

All eight strict production builds, root/index, allowed-axiom audit and eight
independent official kernel replays pass, with reciprocal exact-source review.
The 166 parent is now fully green: run38194242847, completed2026-10-12 02:42:48 UTC,
1,093 paper declarations and304 complete-repository replays. Fresh174 full CI
is a separate pending gate. All166 inherited proof bodies are unchanged.

The weighted multigraph main extension, Theorem34 replacement lower certificate,
literal uniform finite Theorem10 lower coverage, cited-background reconciliation
and fresh skeptical whole-paper audit remain open. The established printed exact-
lambda counterfamily and separate proof-certificate defect are not conflated.
