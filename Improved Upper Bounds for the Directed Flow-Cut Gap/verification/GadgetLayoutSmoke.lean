import DirectedFlowCutGap.BinaryEdgeGadget

open DirectedFlowCutGap RawNonnegativeRational EncodedEdgeGadget

private def fields {n : ℕ} (row : Vector Code n) : List (ℕ × ℕ) :=
  row.toList.map fun q => (q.num,q.den)

def main : IO Unit := do
  let empty : Input 0 := ⟨#v[],#v[],#v[]⟩
  let zero := BinaryEdgeGadget.build empty
  unless zero.1.size == 0 && 0 < zero.2 && zero.2 ≤ BinaryEdgeGadget.budget 0 (1 : ℕ) do
    throw (IO.userError "the empty dyadic gadget changed shape or charge")
  IO.println s!"PASS empty dyadic gadget retained no vertices, paid {zero.2}"

  let adjacency : Vector (Vector Bool 3) 3 :=
    #v[#v[true,true,false],#v[false,false,true],#v[true,false,false]]
  let small : Code := ⟨3,8,by decide⟩
  let weights : Vector (Vector Code 3) 3 :=
    #v[#v[Code.zero,small,Code.one],#v[Code.zero,Code.zero,small],#v[Code.one,Code.zero,Code.zero]]
  let prices : Vector (Vector Code 3) 3 :=
    #v[#v[Code.ofNat 2,⟨7,3,by decide⟩,Code.ofNat 42],#v[Code.zero,Code.zero,Code.ofNat 5],#v[Code.ofNat 9,Code.zero,Code.zero]]
  let D : Input 3 := ⟨adjacency,weights,prices⟩
  let result := BinaryEdgeGadget.build D
  let reference := EncodedEdgeGadget.build D
  let es := edgesWithCost D
  unless es.1.map (fun (u,v) => (u.val,v.val)) == [(0,0),(0,1),(1,2),(2,0)] &&
      0 < es.2 && result.1.size == 14 &&
      decide (result.1.vertices.toList.map Subtype.val = reference.vertices.toList.map Subtype.val) &&
      result.1.data.adjacency.toList.map Vector.toList == reference.data.adjacency.toList.map Vector.toList &&
      fields result.1.data.weights == fields reference.data.weights &&
      fields result.1.data.costs == fields reference.data.costs &&
      es.2 < result.2 && result.2 ≤ BinaryEdgeGadget.budget 3 (8 : ℕ) do
    throw (IO.userError "binary gadget assembly changed the retained order, arcs, raw fields or bounds")
  IO.println s!"PASS exact dyadic gadget order and matrix for four arcs, {result.1.size} vertices, edge listing paid {es.2}, build paid {result.2}"
