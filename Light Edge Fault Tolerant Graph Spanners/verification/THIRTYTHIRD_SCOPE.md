# Executable rational distance and sampled-voting core (204)

Parent: e4e8a59d094db5a586134aa06b9ad7ba5129c76d (198 full CI passed).
Six frozen sources; THIRTYTHIRD_ENTIRE_SOURCE_HASHES.json binds all205 root/module
entries. All198 inherited proof bodies are unchanged. All six isolated strict
checks passed; production gates, fixture execution and official replays are separate.

## Actual computation and semantic link

- RationalDistanceValues: computable Option-rational distances, with none for
  unreachable. The minimum fold has its actual existential bound semantics.
- RationalDistanceTable: materialized core Vector tables, not recursively
  recomputed function closures. The n rounds scan n neighbors per row. The
  actual result iff a native graph walk of at most k edges costs at most budget
  is proved by induction, with no assumed shortest-path or oracle answer.
- RationalDistanceTest: loop erasure of nonnegative walks gives completeness
  after n rounds. Rational sums cast exactly to existing real walk weights.
  The executable Boolean is exactly the existing Covered predicate. Sym2.lift
  respects orientation without choosing an arbitrary quotient representative.
- RationalDistanceWork: the same row/table algorithm has a literal padded work
  counter, 6*n^3+2*n^2+n+2 per test. It counts adjacency-oracle calls, table reads,
  rational additions/comparisons and loop/write operations in an explicitly
  stated abstract unit-cost model. It does not bound the implementation cost
  of arbitrary supplied adjacency/weight functions, compiler output, rational
  bit arithmetic, memory allocation or arbitrary finite-set primitives.
- ExecutableVoting: executable rational sample graphs, fractions, 3/8 votes and
  tail-first output recursion. Cast equality proves exactly the same estimate,
  vote set and output as the198 real semantics for every input tape, including
  empty sample lists and zero vote thresholds.
- ExecutableVotingWork: literal sample/host/edge loops execute the measured
  test and preserve the same output. Host IDs are Fin j, scanned without
  classical enumeration. With at most m draws per query, work is at most
  1 + |l|*(j*(m*(6*n^3+2*n^2+n+4)+5)+4).
  Actual assignment tapes automatically satisfy the length bound, with no
  accuracy, independence or statistical premise required for refinement.

## Boundaries

This discharges the finite rational weighted-distance oracle and executable
edge-selection core. Seeds, hosts, eligible lists, ordered candidates and finite
tapes remain inputs. The exact optimum seed and packing constructed in198 are
still noncomputable. A finite distribution is not a random-bit generator.

The work counter is a polynomial high-level operation count, not an end-to-end
polynomial bit-runtime theorem. In particular, arbitrary supplied graph/weight/
tape functions and finite-set operations are not proved constant-time. Efficient
seed approximation, packing, random generation, representation costs and the
full source runtime still need a joined implementation. Rational weights and
stretch are an implementation domain; no claim covers executable arbitrary
real comparisons. The real-weight mathematical198 theorem is unchanged.

No new mathematical paper correction is asserted by this checkpoint. The
weighted-multigraph, stronger lower-certificate, finite/uniform lower-bound and
whole-paper audit gaps remain separate. No whole-paper completion claim.

The proved numeric measure is precisely the padded instrumentation counter
returned by this program. List length (including repeated tape.length), list
and vector enumeration, vector projection and counter summation are not each
instrumented as separate Lean evaluation steps. They belong to the chosen
abstract primitive boundary. No theorem bounds every evaluation step, allocator
operation or bit operation by this counter. A representation-aware operational
semantics and its cost simulation remain a separate runtime obligation.
