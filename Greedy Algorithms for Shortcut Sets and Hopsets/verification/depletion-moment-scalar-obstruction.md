# Strict demand depletion does not close the moment-method gap

2026-10-11. Ordinary symbolic calculation, prepared for independent component review. This is a finite monotone array of integer demand excesses. It is not a graph realization, an actual greedy run, or a counterexample to the paper's nearlinear theorem or additive-volume conjecture.

## Exact array

Fix an integer k >= 2. Set n=2k^9, I=k^6, D=k^3, A=k^9, B=k^6, M=AB=k^15 and T=Ak^2=k^11. There are M moderate demands in A blocks of B demands, T reservoir demands, and one distinguished demand. Give every demand a bookkeeping endpoint floor of 2, so its distance is 2 plus its excess.

Initially each moderate demand has excess k^2+1, each reservoir demand has excess 1, and the distinguished demand has excess k^3-1. For steps i=0,...,T-1, decrease by one each of the B moderate demands in block i mod A, and retire reservoir demand i by setting its excess to zero. Every moderate block is visited exactly k^2 times. Thus all moderate demands still have excess 1 after these T steps. The distinguished demand is unchanged. At the final step T, set every remaining excess to zero. Subsequently the array is constant.

This description constructs an actual finite coordinatewise antitone integer array. Before the final step no moderate demand vanishes; exactly one reservoir demand vanishes per step. There are T+1 active steps under the separate stopping test max distance <= D, because the distinguished distance is D+1 through time T. After the final step every distance is 2 <= D.

At integer times 0 <= i <= T its unsaturated count and total excess are exactly

    U_i = M + T - i + 1,
    E_i = M + (T-i)(B+1) + k^3 - 1.

Consequently Delta_i = E_i-E_(i+1) is B+1 for i<T and M+k^3-1 for i=T. In particular Delta_i >= B throughout the active run.

## The numerical graph-shaped premises all hold

1. Demand count: U_0=M+T+1 <= 2M=nI, since k^11+1 <= k^15 for k>=2. Each coordinate's distance is at most I: k^2+3 <= k^6 and k^3+1 <= k^6. Also I=D^2 exactly.

2. Strict actual-set depletion: the positive-excess set is nested and loses exactly one demand per step i<T, then all remaining demands at step T. Hence i+U_i=U_0 for i<=T, and (T+1)+U_(T+1)<=U_0. This is stronger than just the new cardinality invariant. Every ordinary finite cutoff/layer identity and depletion telescope holds literally for this array.

3. Active quadratic floor: D^2=B<=Delta_i. Even the stronger maximum-distance bound L_i^2 <= 4Delta_i holds: L_i=k^3+1<=2k^3 and Delta_i>=k^6.

4. Exact tail-cubic moment: for every active time i,

    sum_p (distance_i(p)-3)_+^3 <= U_i Delta_i.

Indeed each of the M moderate terms is at most (k^2)^3=B; reservoir terms are zero; the distinguished term is (k^3-2)^3<=k^9. The sum is at most MB+k^9. For i<T, U_i Delta_i >= (M+1)(B+1) >= MB+k^9, since M>=k^9. At i=T the moderate terms are zero and the distinguished term is at most k^9 <= U_T Delta_T. Thus even coefficient 1 suffices, stronger than the proved coefficient 32.

5. Excess-cubic recurrence: E_i^3 <= 8 U_i^3 Delta_i at every active time, stronger than coefficient 256. Each moderate or reservoir coordinate has excess at most k^2+1, and the one distinguished coordinate has excess at most k^3. Since U_i>=M>=k^3, summing gives E_i <= (k^2+2)U_i <= 2k^2 U_i. Cubing and Delta_i>=k^6 prove the assertion.

The inequalities continue trivially after stopping, with U=E=Delta=0 and a zero tail-cubic moment.

## Consequence and precise limitation

The active count is k^11+1, while n=2k^9, so (T+1)/n grows like k^2/2. Equivalently it has the same n^(11/9) exponent as the existing moment-method boundary. Strict one-demand retirement, the exact first-layer identity, all fixed-cutoff telescopes, the active quadratic floor, the exact cubic-tail moment, and the excess-cubic recurrence therefore do not, by themselves, force a linear number of active steps.

This conclusion is about this explicitly listed collection of numerical premises. The construction does not supply original vertices/edges, chain first-entry selectors, a potential function on all shortcut sets, actual marginal maximization, or the tail-target support theorem's graph structure. It neither proves nor refutes a long greedy history on a graph. A further graph-specific relation, beyond these scalar and layer accounts, remains necessary to obtain a better general bound by this route. No theorem about all possible proof methods is asserted.
