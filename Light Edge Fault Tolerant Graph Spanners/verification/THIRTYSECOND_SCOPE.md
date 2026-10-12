# Fresh adaptive concentration and actual randomized-output guarantees (198)

Exact parent188: 89ccd0ebfdd1752ff57864578efc4087b87034a1.
Ten new sources, 754 lines; all isolated exact sources passed strict compilation.
All 199 source/root entries are frozen in THIRTYSECOND_ENTIRE_SOURCE_HASHES.json.
All 188 inherited proof bodies are unchanged. Production/root/audit/replays are
separate gates and are not implied by this source review.

## Actual construction and scope

FiniteHoeffding obtains a two-sided accuracy-1/8 bound 2 exp(-m/32) from
Mathlib's bounded sub-Gaussian/Hoeffding theorem. FiniteLaw defines explicit
normalized nonnegative real finite masses and proves the actual map/bind,
finite-union and finite-measure translations. ProductSampleConcentration uses
literal product measures, proving independent coordinates and their exact
marginals. There is no supplied statistical concentration premise.

BernoulliTestConcentration samples every original unordered identity with
p=1/(2f), independently, and uses the already proved exact finite restriction
law to show clipping to the actual reached non-seed edges has exactly
AlgorithmSampleProbability.testProbability. Its List.ofFn estimator is the
same literal list-failure fraction used by the existing empirical algorithm.
Every host gets a fresh independent m-sample batch; unused coordinates are
harmless. All spaces are finite.

FreshVotingTapes proves that changing the current candidate's assignment
cannot change any earlier reached state or estimator on a nonrepeating input.
AdaptiveFiniteLaw proves the finite conditional fresh-step union bound.
AdaptiveVotingConcentration defines the actual tail-first random assignment
law by recursive bind and fresh batch update, then proves the probability of
NOT AccurateTrace is at most the actual sum of eligible-host query counts
times 2 exp(-m/32). No union over hypothetical graph states and no assumed
AccurateTrace occurs in that theorem.

VotingQueryCount bounds actual query count by n^4 uniformly in q. In the large
q case the preserver is the graph and the input is empty; otherwise q+1 <= n,
there are at most n connected components per forest, and at most n^2 candidate
identities. LogarithmicVotingSamples sets m=ceil(32(s+5)log n)+1 and proves
failure at most n^(-s), including n=0,1 by the exact empty-input case. The
natural parameter s may be chosen arbitrarily large; s=0 is also valid.

RandomizedVotingGuarantees joins this constructed random execution law to the
same actual output already certified in188. For all finite simple inputs,
f,k>0, eps>0 and globally nonnegative weights positive on actual graph edges,
it internally obtains optimum seed and forest hosts and proves simultaneous
EFT correctness and competitive lightness with failure at most n^(-s).
Algorithm2 has bound 1+64f*lambda(n,t+1). Algorithm3 has
1+64*lambda(n,t+1)/eta, q=floor((2+eta)f), h=floor(eta f)+1, eta>0.
These are the same output graph and same random tape, not separate existential
correctness and lightness outputs. Baseline1, zero-total-denominator convention
and the corrected exact lambda argument remain explicit.

## Remaining whole-paper obligations

The probability/high-probability part of the corrected simple-graph sampled
Algorithms2/3 is now the intended claim of this packet. It is a noncomputable
finite mathematical probability construction. Exact weighted-distance tests,
efficient approximate seed construction, packing implementation, random-bit
model and paid polynomial runtime are still unproved. The theorem uses an
internally chosen actual minimum seed; this does not establish efficient
optimization of that seed. No polynomial-time Theorem13 conclusion is claimed.
Weighted-multigraph upper extensions, repaired Theorem34 lower scaling,
Theorem10 literal finite/uniform qualifications, background reconciliation and
a fresh skeptical whole-paper audit remain separate. No new paper defect is
asserted by this concentration milestone.

## Requested reciprocal review

Read all ten exact new sources in the preparation JSON order. Check product
normalization, exact actual-test marginal, finite fresh update order, the
no-repeated-edge preservation lemma, reached-state union bound, n^4 saturation
case and logarithmic rounding. Check the final output has no supplied accuracy
or independence premise. Bind all199 hashes and188 exact parent proof blobs.
Save review/thirtysecond-independent-minor-audit.json; no compiler is needed.
