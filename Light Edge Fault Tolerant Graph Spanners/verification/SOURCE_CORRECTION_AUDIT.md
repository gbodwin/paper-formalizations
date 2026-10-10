# Bounded source-correction audit

Paper: Greg Bodwin, Michael Dinitz, Ama Koranteng, and Lily Wang, *Light Edge Fault Tolerant Graph Spanners*, arXiv:2502.10890v2 (25 April 2025).

Scope: independent inspection of the supplied v2 PDF, extracted text, and HTML around the greedy correctness proof, blocking-set proof, sampling lemma, and their downstream uses. This is a mathematical source audit, not a complete verification of the paper or a compiler check. No source, project, or implementation files were changed.

Sources inspected:

- https://arxiv.org/pdf/2502.10890v2
- PDF text extracted from the version-pinned source
- https://arxiv.org/html/2502.10890v2

The PDF has an unnumbered title page. Thus printed page p is physical PDF page p+1. The HTML uses anchors such as `Thmtheorem18`, `Thmtheorem20`, and `Thmtheorem27`.

## Result

The proposed corrections to Theorem 18, Lemma 20, and Lemma 27 are justified. Sampling with probability 1/(2f) repairs the f=1 endpoint without changing the stated asymptotic existential bounds. The corresponding Q-heavy-edge sampling rate should be 1/(2 sqrt(f)). Extending the repair to the polynomial-time section requires correcting its acceptance thresholds as well; a sampling-rate substitution alone does not fix every displayed step. The main bounds in Theorems 10-13 need no change on account of these repairs, but that conclusion is about these local issues, not certification of all other arguments.

## 1. f=1 is explicitly within scope

Theorems 10 and 11 on printed p.4, Theorem 12 on p.5, and Theorem 13 on p.6 all quantify over positive integers f, k, n. Consequently f=1 cannot be discarded as an unstated parameter convention. Theorem 13 is repeated with the same quantification on p.15. The post-Theorem-18 discussion on p.10 also discusses f=0 separately; that observation does not make division by f meaningful in later sampling arguments. The proposed probability repair applies to f>=1.

## 2. Theorem 18: two literal typos

Location: printed p.10 / physical PDF page 11; HTML `Thmtheorem18` and proof paragraph `S3.SS2.p3`.

- The sufficient condition for an omitted, surviving original edge is displayed as dist_(H\\F)(u,v) > k w(u,v). It must be **<=**. The surrounding argument immediately uses <= after the edge is rejected by the greedy algorithm.
- The final sentence says that later iterations add edges to F. It must say **H**. The fault set stays fixed, and adding spanner edges can only decrease the relevant distance.

For a precise proof, fix a final fault set F. At the instant the omitted edge was considered, apply the rejection condition to F intersected with the edges of the then-current H. This is an allowed fault set of size at most f. The resulting path survives in the final H\\F. Chaining these edgewise bounds along an original shortest path proves the desired spanner inequality. Both corrections preserve the algorithm and theorem statement.

## 3. Lemma 20: a benign tie-choice omission

Location: printed p.10 / physical PDF page 11; HTML `Thmtheorem20`.

The proof chooses a heaviest cycle edge outside Q and asserts that all other cycle edges were already present when it was added. An arbitrary choice among equal-weight edges does not justify that assertion.

Repair: choose the **last processed edge among the maximum-weight edges of C outside Q**, using the actual fixed greedy order. Every other non-Q edge of C is lighter, or is an earlier equal-weight edge; every Q edge was present initially. The rest of the blocking proof is then unchanged. No distinct-weight assumption, weight perturbation, or modification of the lemma statement is needed. The analogous proof in Lemma 32 on p.17 already explicitly chooses the last such edge.

## 4. Lemma 27: uniform sampling repair and constants

Location: construction and Lemmas 26-27 on printed p.12 / physical PDF page 13; HTML `Thmtheorem27`, especially `S3.I2.i2.p1`.

The construction samples non-tree edges with probability 1/f. Its lower bound for avoiding all blockers relies on (1-1/f)^f >= 1/4. This is valid for integer f>=2, but its left side is zero at f=1. More concretely, with f=1, a hosted edge that has one other hosted blocker is always deleted under this sampling rule. Thus the claimed uniform per-edge survival argument fails at an explicitly allowed endpoint. The wording also confuses the events of selecting and omitting blockers; the relevant event is that **all blockers are omitted**.

Use p=1/(2f), and sample only the hosted non-tree edges H[T]\\T. For a hosted edge e, let d be the number of its blockers that actually lie in H[T]\\T. The hosting rule excludes blockers in T, and d<=f. Therefore

    Pr(all relevant blockers absent) = (1-p)^d >= 1-dp >= 1/2,
    Pr(e survives in H''[T]) >= p/2 = 1/(4f).

Independence of e's sampling from its blockers follows because the blocking witness predates e, so e is never paired with itself. Tree edges survive H'' deterministically. The final step deletes only tree edges, so it preserves every surviving hosted non-tree edge. In particular,

    E[w(H'''[T])] >= w(H[T]\\T)/(4f)
                      >= w(H[T])/(4f) - w(T).

This proves the stated asymptotic form of Lemma 27 uniformly for f>=1. It also gives a convenient stronger estimate on the hosted-edge weight.

Since H''' retains a spanning tree and has weighted girth greater than k+1, the standard MST comparison used in the paper gives w(H'''[T]) <= lambda(n,k+1) w(T). Thus

    w(H[T]\\T) <= 4f lambda(n,k+1) w(T).

Summing with tree congestion at most two gives the warmup bound 1+8f lambda, hence O(f lambda), without any change of exponent or competition parameter.

### Downstream existential uses

- Theorem 21 / p.13: the O(f lambda) warmup bound survives with adjusted absolute constants.
- Theorem 28 / pp.13-14: the same bound applies per host tree; the gain from multiple hosts is unchanged.
- Theorem 29 / pp.14-15: replace its heavy-edge probability 1/sqrt(f) by 1/(2 sqrt(f)). There are at most sqrt(f) relevant non-Q blockers, so the same union-bound argument gives survival at least 1/(4 sqrt(f)). This preserves the O(sqrt(f) lambda) heavy-edge bound and repairs its f=1 degeneration. The light-edge part continues to use p=1/(2f), with at least sqrt(f) eligible hosts, giving O(sqrt(f) lambda).
- Consequently the corresponding upper bounds in Theorems 10-12 retain their stated asymptotic dependence.

## 5. Polynomial-time section: probability and threshold must be aligned

Verified PDF locations:

- Algorithm 2, printed p.15 / PDF page 16: sampling probability 1/f; acceptance threshold 1/8.
- Definitions of H'_e^T on p.15: probability 1/f.
- Lemmas 30-31, p.16 / PDF page 17: estimator error 1/8; avoiding faults is claimed to have probability at least 1/4.
- Lemma 32, p.17 / PDF page 18: analysis samples with probability 1/f, but says that being hosted implies estimated probability at least 3/8, contradicting Algorithm 2's displayed threshold.
- Algorithm 3, p.19 / PDF page 20: probability 1/f; vote threshold 3/8. The p.18 correctness argument invokes Lemma 31, whose old 1/4 lower bound and 1/8 error only yield 1/8, not 3/8.

A consistent repair, preserving all asymptotic bounds, is:

1. Use p=1/(2f) in Algorithms 2 and 3, in the definitions of the random test graphs, and in Lemma 32's comparison sampling.
2. Use estimated acceptance probability >=3/8 in **both** algorithms.
3. Keep the additive estimation tolerance 1/8.

Then, for a tree avoiding the fault set, all at-most-f relevant faulty edges are omitted with probability at least 1/2. Any necessary edge therefore has true test probability at least 1/2 and estimated probability at least 3/8, so it is added or gets the requisite votes. Conversely, a hosted edge has true test probability at least 3/8-1/8=1/4. Its survival probability in the Lemma 32 analysis is therefore at least (1/(2f))(1/4)=1/(8f). This retains the O(f lambda) per-host bound and both forms of Theorem 13. It changes the displayed randomized algorithms, rather than merely rephrasing their proofs.

Two neighboring proof cleanups are also necessary for a literal verification:

- Lemma 30's displayed multiplicative Chernoff calculation omits the mean probability factor. An additive Hoeffding bound proves the stated lemma directly: for m independent tests, Pr(|P_hat-P|>1/8) <= 2 exp(-m/32). Condition on the prior algorithm history and union-bound over the polynomial-size family of tests. Choosing a sufficiently large constant in m=c log n retains the stated high-probability guarantee.
- At the start of p.18, Lemma 32's rearrangement drops an additive tree-weight term. From E[w(H''')] >= a w(H[T])/f-w(T), retain w(H[T]) <= (f/a)(E[w(H''')]+w(T)). Since lambda>=1, the same O(f lambda w(T)) bound follows. Alternatively use the surviving non-tree-edge estimate above. The line on p.17 saying the last deletion moves H'' to H'' should refer to H'' to H'''.

## 6. Parameter and counting caveats in the downstream multiple-host argument

These are separate from the f=1 sampling correction, but matter when tracing the repair literally through every displayed inequality.

**Real eta and integer counts.** Theorems 12-13 allow any eta>0, while the proofs write (2+eta)f+1 trees and Algorithm 3 tests votes>=eta f+1 without stating rounding. For a real fault budget the actual number of faults is its floor. Put t=floor((2+eta)f)=2f+floor(eta f). Use t+1 tree-connectivity and a vote requirement t+1-2f=floor(eta f)+1. At least that many trees avoid the at-most-f faults. The literal unrounded vote threshold can demand one too many votes when eta f is nonintegral. This integer repair preserves the gain Omega(eta f), since floor(eta f)+1>eta f.

**Count Q separately.** Multiple-host multiplicity is guaranteed for edges in H\\Q, not for Q edges, which appear in at most two trees. Thus the labels claiming that every edge of H appears in Theta(eta f) graphs are not literally valid. Write w(H)=w(Q)+w(H\\Q), apply multiplicity only to the latter, and retain the base term. With h=floor(eta f)+1 hosts, the corrected existential calculation gives

    ell_t(H|G) <= 1 + 8f lambda/h <= 1 + 8 lambda/eta.

The polynomial-time calculation similarly retains the constant-factor preserver's base term. These bounds agree with the main Theorems 12-13, which state O_eta(lambda). However, Theorem 28's literal uniform O(eta^(-1) lambda) for all eta>0 should have an added O(1) term, or should restrict eta to a bounded range. For example, on a nonempty tree H=Q and competitive lightness is 1 regardless of eta, so a universal bound tending to zero as eta grows cannot hold. This issue is independent of changing p.

## Conclusion for a formalization

Record the Theorem 18 typo fixes, Lemma 20's last-in-order tie choice, and the p=1/(2f) / p=1/(2 sqrt(f)) changes as explicit source repairs. If formalizing Theorem 13, also record the 3/8 acceptance-threshold alignment, concentration proof replacement, integer vote convention, and retained tree-weight terms. The advertised main asymptotic tradeoffs survive these local repairs. Do not label the unmodified printed proofs or Algorithms 2-3 as verified by this audit.
