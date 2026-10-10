# Explicit source corrections

Source: [arXiv:2502.10890v2](https://arxiv.org/abs/2502.10890v2). Printed page p is physical PDF page p+1. The independent source review is in `verification/SOURCE_CORRECTION_AUDIT.md`. This log distinguishes mathematical repairs from proof typos. The main results remain work in progress.

## Substantive repairs

0. **Exact main lambda upper comparisons (Theorems 11–13, pp.4–6,13 repeated p.15).** The displayed argument `lambda(n,(1+epsilon)2k)` is false for the stated full parameter range. Unit-weight `K_(m,m)`, `f=k=1`, `epsilon=3/2` forces every edge in every eligible spanner. A three-hub-per-side two-fault connectivity preserver has `6m−9` edges, giving competitive lightness at least `m/6`, while `lambda(2m,5)=O(sqrt(m))`. Four hubs, eta=1 give the analogous contradiction at competition 3 and cover both algorithmic alternatives. The precise parameter correction supported by the stretch-s arguments is `lambda(n,(1+epsilon)(2k−1)+1)`. The coarse polynomial tradeoffs survive via `delta=epsilon(2k−1)/(2k) >= epsilon/2`. This counterfamily does not refute the main 2f threshold conclusion or the lower lambda comparisons. The complete independently source-checked uniform proof is in `verification/LAMBDA_COUNTERFAMILY_AUDIT.md`; the actual finite counterfamily, genuine denominators and square-root-growth contradiction are Lean-checked. The extremal lambda supremum itself is not encoded.

1. **Sampling at f=1 (Lemma 27, p.12; Theorem 29, pp.14–15).** The positive-integer quantifiers include 1. Sampling with probability 1/f makes the claimed blocker-avoidance probability `(1−1/f)^f ≥ 1/4` false there. Use `1/(2f)` for the warmup and Q-light edges. A finite union bound gives avoidance at least 1/2 and survival at least `1/(4f)`. For Q-heavy edges with at most sqrt(f) non-Q blockers, use `1/(2 sqrt(f))` and obtain survival at least `1/(4 sqrt(f))`. This changes constants, not the advertised asymptotic dependence.
2. **Polynomial algorithm thresholds (Algorithms 2–3, pp.15–19).** Algorithm 2 prints threshold 1/8 but Lemma 32 relies on 3/8. Algorithm 3 prints 3/8 while the old correctness calculation yields only 1/8 after estimation error. Use sampling `1/(2f)` consistently and threshold 3/8 in both algorithms. Actual probability at least 1/2 minus error 1/8 ensures necessary edges are accepted; acceptance plus error 1/8 ensures actual probability at least 1/4. Conditional survival therefore gives `1/(8f)`. This changes the displayed algorithms. The randomized graph guarantees and runtime are not yet formally established.
3. **Real eta and integer votes (Theorems 12–13, Algorithm 3).** For eta>0, put `t = 2f + floor(eta*f)` and `h = floor(eta*f)+1`. At most t faults is the meaning of the real competition budget. Use t+1 host trees and h votes. The literal vote threshold eta*f+1 can demand one too many votes for a noninteger eta*f.
4. **Preserve the seed baseline (Theorem 28, pp.13–14).** Only edges of H outside Q have the higher host multiplicity. Keep `w(H)=w(Q)+w(H\Q)`. The corrected finite bound obtained from the repaired sampling analysis is `ell_t(H|G) ≤ 1 + 8f*lambda/h ≤ 1 + 8*lambda/eta`. The unrestricted uniform statement `O(lambda/eta)` omits the baseline; a nonempty tree has lightness 1 for every eta. Restricting eta to a bounded interval also repairs it. The main theorem's `O_eta(lambda)` statement is unaffected by this issue.

## Lower-bound proof certificate: confirmed gap

**Theorem 34, printed pp.20–21.** The stated MST-cloud subgraph is not generally a `cf`-fault connectivity preserver. At `c=2`, `f=k=1`, the source chooses two vertices per cloud. Blow up a triangle and one of its actual path MSTs. Deleting the two certificate edges incident to one leaf-copy vertex isolates it in the certificate, while the original graph retains an edge to the other leaf cloud. These are actual input faults allowed by Definition 7 (p.3).

`BlowupCertificateObstruction` formalizes this six-vertex graph, weighted-girth premise, actual MST, exact faults and failure. `GenericBlowupFailure` proves failure for every spanning-tree choice on any complete base with at least three vertices whenever cloud size is within the fault budget, including the exact source rounding `ceil(sqrt(q+1))` for every integer `q>=2`.

Independent source review also checks the infinite near-extremal complete weighted bases `w(i,j)=|i-j|+1`: weighted girth is greater than 2, lightness is `N(N+4)/12`, and this is at least `lambda(N,2)/6`. Thus the source's near-extremal base condition does not rescue the certificate, even with fixed `f=1`. This last near-extremality comparison is reviewed mathematics, not a claim of full Lean formalization of lambda.

**Impact:** the written denominator witness is invalid. Theorem 34 itself has not been disproved, and another certificate or construction might repair it. Increasing cloud size to `cf+1` fixes connectivity but the unchanged weight argument has coefficient `(f+1)/(cf+1)^2` and base size `n/(cf+1)`, so it does not recover the advertised lower bound. The general lower theorem remains open. See `verification/FOURTH_SOURCE_AND_COMPONENT_AUDIT.md`.

### Exact high-fault boundary; asymptotic interpretation qualified

`FaultBudgetSaturation` proves that on any simple n-node graph, `q>=n-2` forces every q-fault connectivity preserver to equal the input. The input itself is an eligible spanner at stretch at least one and has competitive ratio at most one against the genuine minimum denominator.

This constrains any jointly uniform all-n interpretation of the lower statements. It is not an unconditional asymptotic refutation: Theorem 34 supplies an infinite family, and the source does not specify whether its sufficiently-large-n threshold may depend on f. Fixing f before n grows can exclude the saturation regime even with an f-independent Omega coefficient. A diagonal with f proportional to n cannot refute that quantifier order. This domain note is separate from the confirmed fixed-f certificate defect.

## Proof details and typographical cleanup

- **Theorem 18, p.10:** the sufficient edge condition is `≤`, not `>`; later edges are added to H, not the fixed fault set F. The formal construction proves the corrected conclusion from the actual decision test.
- **Lemma 20, p.10:** select the last processed maximum-weight cycle edge outside Q. This deals with ties without a distinct-weight assumption.
- **Lemma 30, p.16:** use an additive concentration proof (for m independent tests, failure probability at most `2 exp(−m/32)` at error 1/8) instead of the displayed multiplicative-Chernoff calculation that drops a mean factor. Conditioning on prior history and the adaptive union bound remain obligations.
- **Lemma 32, pp.17–18:** retain the additive tree-weight term when rearranging expected weights; its absorption into the asymptotic bound uses lambda≥1. Its last-deletion label should read H'' to H'''.

These repairs have independent source review. Only statements named in a compiled and audited checkpoint are Lean-certified. No implication that all remaining paper arguments have been validated is intended.
