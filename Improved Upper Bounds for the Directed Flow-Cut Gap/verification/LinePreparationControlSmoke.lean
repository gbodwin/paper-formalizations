import DirectedFlowCutGap.BinaryLineLabels

open DirectedFlowCutGap EncodedEdgeLineInput
open RawNonnegativeRational (Code)

private def check {n : ℕ} (D : Input n) (legacy work : ℕ) : IO Unit := do
  let metered := BinaryLineLabels.prepareWithControl D
  let actual := metered.1.1
  let expected := lineInput D
  unless decide (actual.adjacency = expected.adjacency) &&
      actual.costs.toList.map (fun q => (q.num,q.den)) == expected.costs.toList.map (fun q => (q.num,q.den)) &&
      actual.demands.map (fun (s,t) => (s.val,t.val)) == expected.demands.map (fun (s,t) => (s.val,t.val)) &&
      metered.1.2 == legacy && metered.2 == work &&
      metered.2 ≤ BinaryLineLabels.controlBudget (lineSize n) do
    throw (IO.userError "line preparation changed the ordered graph or exceeded its scalar bound")
  IO.println s!"PASS binary line preparation on {n} vertices, retained fee {metered.1.2}, nested control {metered.2}"

def main : IO Unit := do
  check (⟨#v[],[],#v[]⟩ : Input 0) 27 9
  check (⟨#v[#v[false,true],#v[true,false]],[(0,1),(1,0),(0,1)],
    #v[#v[Code.zero,Code.ofNat 3],#v[Code.ofNat 5,Code.zero]]⟩ : Input 2) 5591 160297
