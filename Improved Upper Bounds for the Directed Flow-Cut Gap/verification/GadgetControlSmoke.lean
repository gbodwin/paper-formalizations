import DirectedFlowCutGap.BinaryEdgeGadget

open DirectedFlowCutGap RawNonnegativeRational EncodedEdgeGadget

private def fields {n : ℕ} (row : Vector Code n) : List (ℕ × ℕ) :=
  row.toList.map fun q => (q.num,q.den)

def main : IO Unit := do
  let empty : Input 0 := ⟨#v[],#v[],#v[]⟩
  let zero := BinaryEdgeGadget.buildWithControl empty
  unless zero.1.1.size == 0 && zero.1.2 == 265 && 0 < zero.2 && zero.2 ≤ BinaryEdgeGadget.controlBudget 0 (1 : ℕ) do
    throw (IO.userError "the measured empty gadget changed shape or fee")
  IO.println s!"PASS measured empty gadget kept fee {zero.1.2}, scalar work {zero.2}"
  let adjacency : Vector (Vector Bool 3) 3 :=
    #v[#v[true,true,false],#v[false,false,true],#v[true,false,false]]
  let small : Code := ⟨3,8,by decide⟩
  let weights : Vector (Vector Code 3) 3 :=
    #v[#v[Code.zero,small,Code.one],#v[Code.zero,Code.zero,small],#v[Code.one,Code.zero,Code.zero]]
  let prices : Vector (Vector Code 3) 3 :=
    #v[#v[Code.ofNat 2,⟨7,3,by decide⟩,Code.ofNat 42],#v[Code.zero,Code.zero,Code.ofNat 5],#v[Code.ofNat 9,Code.zero,Code.zero]]
  let D : Input 3 := ⟨adjacency,weights,prices⟩
  let source := BinaryEdgeGadget.buildWithControl D
  let measured := source.1.1
  let reference := EncodedEdgeGadget.build D
  let es := edgesWithControl D
  unless es.1.1.map (fun (u,v) => (u.val,v.val)) == [(0,0),(0,1),(1,2),(2,0)] && es.1.2 == 294 &&
      0 < es.2 && measured.size == 14 && source.1.2 == 32893 &&
      decide (measured.labels=reference.labels) &&
      decide (measured.vertices.toList.map Subtype.val=reference.vertices.toList.map Subtype.val) &&
      measured.data.adjacency.toList.map Vector.toList == reference.data.adjacency.toList.map Vector.toList &&
      fields measured.data.weights == fields reference.data.weights && fields measured.data.costs == fields reference.data.costs &&
      0 < source.2 && source.2 ≤ BinaryEdgeGadget.controlBudget 3 (8 : ℕ) do
    throw (IO.userError "the measured gadget changed the labels, order, rational data, topology or fee")
  IO.println s!"PASS measured four-arc gadget kept {measured.size} nodes and fee {source.1.2}, listing {es.2}, scalar work {source.2}"
