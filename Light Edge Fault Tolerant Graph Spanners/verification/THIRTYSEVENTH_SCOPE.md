# Stored host and candidate execution scope

## Actual computation

`StoredHosts.transition` iterates literal host records, invokes every transition
of the stored-draw voting submachine, counts its returned Booleans and compares
the count with the supplied admission threshold. A host record contains its
literal endpoint list and literal list of draw endpoint lists. Distinct host
identifiers can have equal-valued records; only their identifier list must be
without repetitions for the finite-set cardinality theorem.

`StoredCandidates.transition` iterates literal candidate records. Each invokes
the actual host loop using the current selected edge list. Acceptance conses
the candidate onto that list; rejection retains it. Later candidates consume
this changed list. The complete interpreter returns the exact original rational
and cast-real empirical-voting recursion, in the reverse of record traversal
order because the original definition processes its tail first.

## Original fixed assignment

The original `FreshVotingTapes.assignmentTape` ignores its selected-state
argument. `StoredAssignmentSchedule` uses that exact contract to derive the
whole `ValidSchedule` uniformly from static eligible-host and finite assignment
record representations, at every actual reached selected set.
`StoredAssignmentExecutable.execute_assignment` then returns the literal old
real-weight graph without an adaptive tape lookup or a per-state input premise.
Creating the stored record bank or its list encoding remains input preparation,
and sampling it from a distribution is not performed by the interpreter.

## Same-run original-input bound

For each host, the stored-draw bound charges every draw and every actual edge
list cell, including duplicates. The host wrapper adds two transitions per host
and one terminal transition. The candidate wrapper adds two transitions per
candidate and one terminal transition. Its fixed fuel bounds all intermediate
selected-list lengths by the initial selected length plus the number of input
candidate records; this cap uses no computed admission result.

The cost model remains the inherited rational/natural/list-cell atom model.
Evaluating the fuel expression and the numeric width/bit costs of arithmetic
are outside this transition count.

## Representation and remaining work

`ValidSchedule` binds each supplied candidate's budget, distinct eligible host
identifiers, host endpoint lists and actual tape draws to the original data at
that record's preceding selected set. These are data-representation premises,
not supplied votes, paths, distances, admissions or transition proofs. The
machine consumes a finite stored schedule. Constructing that schedule or
adaptively looking up a tape keyed by the evolving selected set remains open.

Raw graph/weight encoding, random generation, eligibility construction,
efficient seed and packing algorithms, rational bit complexity and the full
paper runtime are not proved here. The previously documented weighted
multigraph extension, Theorem34 repair and literal Theorem10 qualifications
remain. This checkpoint asserts no new mathematical correction.

## Verification

The fifteen new sources have strict local checks, fifteen official exact-source
kernel replays, twenty-three actual interpreter fixtures, and three independent scoped
source reviews. New defining-module safety and full type/body closures are
checked separately from the full244 reference aggregate. Their exact counts and
hash-bound evidence are in `stored-candidate-local-gates.json`. Exact successor
publication and terminal CI are separate gates; local evidence is not a
whole-paper completion claim.
