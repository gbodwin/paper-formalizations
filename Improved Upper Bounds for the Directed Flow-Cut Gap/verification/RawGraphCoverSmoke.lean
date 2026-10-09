import DirectedFlowCutGap.FractionalCoverRawGuesses
import DirectedFlowCutGap.FractionalCoverRawOracleEncoding
open DirectedFlowCutGap
open IntegralNetworkFlow FractionalCover RawNonnegativeRational
namespace FractionalCoverDispatchRawSmoke

def rawInput : FractionalCoverRawGraph.Input 4 where
  adjacency := #v[#v[false,true,true,false],#v[false,false,false,true],
    #v[false,false,false,true],#v[false,false,false,false]]
  demands := [(0,3)]
  costs := #v[Code.ofNat 1,Code.ofNat 1,Code.ofNat 4,Code.ofNat 1]

def rawCycle : Digraph (Fin 4) where
  Adj u v := (u,v) ∈ ([(0,1),(1,1),(1,2),(2,1),(2,3),(0,3)] : List (Fin 4 × Fin 4))
instance : DecidableRel rawCycle.Adj := fun u v => inferInstanceAs
  (Decidable ((u,v) ∈ ([(0,1),(1,1),(1,2),(2,1),(2,3),(0,3)] : List (Fin 4 × Fin 4))))

def rawEdgeCost (e : Fin 4 × Fin 4) : Code :=
  Code.ofNat (if e=(0,1) then 5 else if e=(2,3) then 1 else if e=(0,3) then 10 else 0)

#eval do
  let E := ResidualSearch.Enumeration.fin 4
  match (FractionalCoverRawOracle.shortest E rawCycle rawEdgeCost 0 3).1 with
  | none => throw (IO.userError "raw minimum witness omitted")
  | some p =>
    if p.edges != [(0,1),(1,2),(2,3)] then throw (IO.userError "raw retained minimum edges wrong")
    if p.cost.num != 6*p.cost.den then throw (IO.userError "raw retained minimum cost wrong")
  if (FractionalCoverRawOracle.shortest E rawCycle rawEdgeCost 3 0).1.isSome then
    throw (IO.userError "raw unreachable case returned a path")
  let out := rawInput.solve (by decide)
  if out.events.length != 11 then throw (IO.userError "raw cover trace length differs")
  let cost := FractionalCoverRawCore.objectiveCode rawInput.costs out.best
  if cost.num*729 != cost.den*4292 then throw (IO.userError "raw cover cost differs from exact checked rational recurrence")
  let b1 := FractionalCoverRawCore.get out.best 1
  let b2 := FractionalCoverRawCore.get out.best 2
  if !(Code.one.le b1 && Code.one.le b2) then throw (IO.userError "raw cover is infeasible")
  IO.println s!"PASS: actual raw minimum-path witness and eleven-update raw graph cover; unreduced objective numerator bits={cost.num.size}, denominator bits={cost.den.size}"

def rawMixedInput : FractionalCoverRawGraph.Input 4 where
  adjacency := rawInput.adjacency
  demands := [(0,3)]
  costs := #v[Code.ofNat 1,Code.zero,Code.ofNat 4,Code.ofNat 1]

#eval do
  match FractionalCoverRawGuesses.solveInput rawMixedInput with
  | .covers states =>
    if states.length != 15 then throw (IO.userError "raw lambda grid length differs")
    if !(states.all fun s => Code.one.le (FractionalCoverRawCore.get s.best 1) &&
        Code.one.le (FractionalCoverRawCore.get s.best 2)) then
      throw (IO.userError "raw lambda output infeasible")
    if !(states.any fun s =>
      let cost := FractionalCoverRawCore.objectiveCode rawMixedInput.costs s.best
      let mass := FractionalCoverRawCore.sumCodes (List.ofFn (FractionalCoverRawCore.get s.best))
      cost.le (Code.ofNat 24) && mass.le (Code.ofNat 24)) then
      throw (IO.userError "raw lambda family lacks joint guarantees")
    IO.println s!"PASS: complete raw zero-aware dispatch and {states.length} c+lambda solves with a jointly bounded actual cover"
  | _ => throw (IO.userError "raw mixed-cost dispatch failed")

end FractionalCoverDispatchRawSmoke
