# Sequential mathematical/source argument (unelaborated)

1. **State and digits.** For 0<q and r:Fin q, next remainder is 2r mod q and
   digit is 1 exactly when q<=2r. Since 2r<2q, the next remainder is either 2r
   or 2r-q. Thus x(r)=r/q satisfies x(r)=d(r)/2+x(r')/2 and 0<=x(r)<1.
   Starting with r=1,q=2f gives x=1/(2f). Modulo, comparison and register
   updates are concrete natural-number operations, with no uniform-draw oracle.

2. **Bit consumption.** The finite-input runner reads one head bit, halts if
   it mismatches the digit and otherwise recurses on the tail at r'. Its
   canonical terminating word is t matching digits followed by the complement
   of the next digit. Induction proves its length is t+1 and execution returns
   the appropriate output, exactly t+1 reads and an arbitrary untouched suffix.

3. **Explicit probabilistic semantics.** The primitive fairCoin has two masses
   1/2. fuelLaw is defined from that primitive by fresh bind at EACH step; it
   does not take a biased or independent supplied response as input. A matching
   branch continues and a mismatching branch halts. Consequently W_(t+1)=W_t/2
   and A_(t+1)(r)=d(r)/2+A_t(r')/2 for waiting and true-output masses.
   This is the declared finite-prefix operational model. The finite List runner
   supplies a deterministic consumption witness, not a separate claimed theorem
   transporting a measure on arbitrary supplied infinite streams.

4. **Termination and exact bias.** Induction yields W_t=2^-t and
   A_t(r)=x(r)-2^-t*x(r_t). The remainder factor is in [0,1), so squeezing by
   2^-t proves A_t tends to x(r). Waiting mass tends to zero. The unique
   halting-depth mass W_t-W_(t+1) is 2^-(t+1). Geometric summation gives total
   finite halting mass one, the almost-sure contract in this prefix semantics.
   No claim that all bit streams terminate, or that a separate infinite-stream
   measure/refinement has been constructed, is used.

5. **Terminal output and cost.** Expanding the finite true-output recurrence
   gives the sum of 2^-(k+1) over depths whose output digit is true. Nonnegative
   series convergence and the preceding limit give total true mass x(r); total
   halting mass minus that series gives false mass 1-x(r). outputLaw is packaged
   only after deriving these masses. It is not an assumed primitive. The
   geometric first-moment identity proves sum_t (t+1)2^-(t+1)=2, exactly the
   expected fair-bit/read count attached to the canonical halting words. It
   does not charge integer arithmetic or give a deterministic bit budget.

6. **Fresh independent repetition.** independentCalls is recursive monadic
   composition: at each consecutive output position, bind a newly invoked
   scalar sampler, then map Fin.cons over the recursively generated tail.
   Its event probabilities equal productLaw by induction and the reviewed
   fin_cons_probability lemma; the Fin 0 case is the unique empty vector.
   Scalar mass equals the explicit Bernoulli factor at 1/(2f), so this product
   is exactly the reviewed idealTapeLaw. Applying the reviewed flat-tape law
   then gives the accepted supplied-response assignment event probability.
   This proves the fresh-call output interface. It is not an assertion that an
   arbitrary supplied tensor has that law, or a completed one-stream renewal,
   state/cost refinement or charged batch implementation.

The author checked r=0 (zero digits forever; halts at the first true fair bit),
f=1, zero output count and all empty tape dimensions. Even at dyadic bias the
algorithm intentionally does not special-case remainder zero, so its expected
read count stays exactly two; this is a constant-factor inefficiency, not a
hidden bias error. Distinct/repeated candidate positions are handled by the
unchanged flat-tape equivalence. No enumeration or key deduplication changes.

Primary statements for modulo subtraction, squeezing, geometric sums and their
first moments, nonnegative HasSum/partial-sum convergence and the shifted range
sum were read in pinned sources. In particular, sum_range_succ' places the
initial term on the RIGHT; the source explicitly commutes the other side before
comparing the tail sums. All new proofs remain unelaborated and require fresh
sequential independent source review before any execution plan.
