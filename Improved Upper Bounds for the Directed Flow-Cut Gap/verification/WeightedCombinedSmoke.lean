import DirectedFlowCutGap.IntegerWeightedChoice
import DirectedFlowCutGap.RawWeightedMasses
import DirectedFlowCutGap.BinaryWeightedChoice
import DirectedFlowCutGap.ApproximatePackingTrace

#eval do
  IO.eprintln "WEIGHTED_COMBINED_PROGRESS imports-complete"
  (← IO.getStderr).flush

#eval do
  IO.eprintln "WEIGHTED_COMBINED_PROGRESS begin-integer"
  (← IO.getStderr).flush

namespace WeightedCombinedSmoke.Integer

open DirectedFlowCutGap.IntegerWeightedChoice

/-- The reference expands each mass into its literal consecutive tickets. -/
private def tickets (xs : List (Nat × Nat)) : List Nat :=
  xs.flatMap fun x => List.replicate x.2 x.1

#eval do
  let mut cases : Nat := 0
  for a in List.range 5 do
    for b in List.range 5 do
      for c in List.range 5 do
        let xs := [(2,a),(7,b),(2,c),(9,0)]
        let expected := tickets xs
        unless total xs == expected.length do
          throw (IO.userError "Recorded total differs from ticket count")
        for u in List.range (total xs + 2) do
          let r := chooseCharged xs u
          unless r.1 == expected[u]? && r.1 == choose xs u do
            throw (IO.userError "Selection differs from its consecutive ticket interval")
          unless r.2 ≤ 6 * xs.length + 1 do
            throw (IO.userError "Natural-operation annotation exceeded its list bound")
        for p in [fun x => x == 2, fun x => x == 7, fun _ => true, fun _ => false] do
          let actual := ((List.range (total xs)).filter fun u => (choose xs u).any p).length
          unless actual == selectedMass xs p do
            throw (IO.userError "Selected ticket count differs from recorded mass")
        cases := cases + 1
  unless choose ([] : List (Nat × Nat)) 0 == none do
    throw (IO.userError "Empty input unexpectedly selected an entry")
  IO.println s!"PASS {cases} integer-mass lists: zero masses, duplicate outputs, exact tickets, predicate counts, out-of-range draws and natural-operation annotations"

end WeightedCombinedSmoke.Integer

#eval do
  IO.eprintln "WEIGHTED_COMBINED_PROGRESS end-integer"
  (← IO.getStderr).flush


#eval do
  IO.eprintln "WEIGHTED_COMBINED_PROGRESS begin-mass-binary"
  (← IO.getStderr).flush

namespace WeightedCombinedSmoke.MassBinary

open DirectedFlowCutGap
open BinaryArithmetic

private def raw (a d : Nat) : RawNonnegativeRational.Code :=
  ⟨a,d+1,Nat.succ_pos d⟩

private def padded (n k : Nat) : Bits := n.bits ++ List.replicate k false

private def checkBinary (xs : List (Nat × Nat)) (ticket pad : Nat) : IO Unit := do
  let bs := xs.map fun x => (padded x.1 pad,padded x.2 (pad+1))
  let t := padded ticket (pad+2)
  let r := BinaryWeightedChoice.choose bs t
  let ref := IntegerWeightedChoice.choose xs ticket
  unless r.1.map value == ref do
    throw (IO.userError "Binary prefix selection disagrees with the natural interval selector")
  unless r.1 == ref.map (fun label => padded label pad) do
    throw (IO.userError "Binary selection failed to preserve the selected padded label bytes")
  let B := max t.length ((bs.map fun x => x.2.length).foldl max 0)
  let C := (bs.map fun x => x.1.length).foldl max 0
  unless r.2 ≤ xs.length*(160*(B+1)+4*C+16)+1 do
    throw (IO.userError "Binary selection exceeded its stored-width charge")

#eval do
  let codes := [raw 0 0,raw 0 1,raw 1 0,raw 1 1]
  let mut lists : Nat := 0
  let mut draws : Nat := 0
  for a in codes do
    for b in codes do
      for c in codes do
        let input := [(2,a),(7,b),(2,c)]
        let result := RawWeightedMasses.encode input
        let den := a.den*b.den*c.den
        let reference := [(2,a.num*b.den*c.den),
          (7,b.num*a.den*c.den),(2,c.num*a.den*b.den)]
        unless result.1 == den && result.2 == reference do
          throw (IO.userError "Literal mass construction differs from independent three-term formula")
        for pred in ([fun x => x == 2,fun x => x == 7,fun _ => true,fun _ => false] : List (Nat → Bool)) do
          let p : Nat → Bool := pred
          let expected := (reference.filter fun x => p x.1).map Prod.snd |>.sum
          unless IntegerWeightedChoice.selectedMass result.2 p == expected do
            throw (IO.userError "Predicate mass mismatch after rational encoding")
        for pad in List.range 3 do
          for ticket in List.range (IntegerWeightedChoice.total reference+2) do
            checkBinary result.2 ticket pad
            draws := draws+1
        lists := lists+1
  let empty := RawWeightedMasses.encode ([] : List (Nat × RawNonnegativeRational.Code))
  unless empty.1 == 1 && empty.2 == [] do
    throw (IO.userError "Empty mass encoding changed")
  checkBinary [] 0 5
  for ticket in [0,2^80-1,2^80,2^80+6,2^80+7] do
    checkBinary [(0,0),(2,2^80),(7,7),(2,0)] ticket 129
  IO.println s!"PASS {lists} rational mass lists and {draws} padded binary draws; empty, zero, duplicate-label, out-of-range and 80-bit/129-padding cases"

end WeightedCombinedSmoke.MassBinary

#eval do
  IO.eprintln "WEIGHTED_COMBINED_PROGRESS end-mass-binary"
  (← IO.getStderr).flush


#eval do
  IO.eprintln "WEIGHTED_COMBINED_PROGRESS begin-packing"
  (← IO.getStderr).flush

namespace WeightedCombinedSmoke.Packing

open DirectedFlowCutGap
open FractionalCover

#eval do
  let mut cases : Nat := 0
  for d in ([2,3,7,1000] : List Nat) do
    let dn : Nat := d
    let dq : ℚ := dn
    let c : Row 2 := #v[(1 : ℚ)/dq,((dn-1 : Nat) : ℚ)/dq]
    let oracle : Nat → Oracle 2 := fun k y =>
      if value y 0 < value y 1 || (value y 0 = value y 1 && k%2=0) then
        ⟨{0},0⟩ else ⟨{1},1⟩
    let out := ApproximatePackingTrace.run c oracle (fuel 2)
    unless 1 ≤ objective c out.weights && 0 < out.total &&
        out.total = traceTotal out.events && out.events.length ≤ 12 do
      throw (IO.userError "Packing trace did not stop with a positive exact retained mass")
    for i in List.finRange 2 do
      unless value out.loads i = traceLoad out.events i &&
          traceLoad out.events i / traceTotal out.events ≤ 3 * value c i do
        throw (IO.userError "Actual retained event marginal exceeds the pathwise bound")
    unless out.events.all (fun e => e.amount = value c e.choice.bottleneck &&
        0 < e.amount && e.choice.bottleneck ∈ e.choice.column) do
      throw (IO.userError "An event lost its attained original input amount")
    cases := cases+1
  IO.println s!"PASS {cases} varying-oracle rational packing traces, exact positive event masses and coordinate marginals"

end WeightedCombinedSmoke.Packing

#eval do
  IO.eprintln "WEIGHTED_COMBINED_PROGRESS end-packing"
  (← IO.getStderr).flush

