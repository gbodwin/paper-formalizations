import DirectedFlowCutGap.GraphRelaxationProgram

/-! Input-derived bounds for the literal scan. Costs are canonically added
once per accepted extension; comparison never expands the retained result. -/
namespace DirectedFlowCutGap.GraphRelaxationProgram
open BinaryArithmetic BinaryRational BinaryFractionalRows GraphWalkExtension

def EntryBound (B N : ℕ) (x : Entry) : Prop :=
  x.1.length ≤ B ∧ value x.1 ≤ N ∧ StoredBounded x.2.cost B

theorem outgoing_width (rows : List Fraction) (sw u : Bits) (B : ℕ)
    (hB : 1 ≤ B) (hr : ∀ q∈rows,StoredBounded q B) (hi : value u<rows.length) :
    StoredBounded (OutgoingCostProgram.result rows sw u) B := by
  have h := PathCostMaterialization.costs_width rows sw [u] B hB hr (by simpa)
  exact h _ (by simp [PathCostMaterialization.costs])

theorem extension_width {rows : List Fraction} {sw u v : Bits} {q : Walk} {B : ℕ}
    (hw : StoredBounded (OutgoingCostProgram.result rows sw u) B) (hq : StoredBounded q.cost B) :
    StoredBounded (GraphWalkExtension.result rows sw (u,v) q).cost (2*B+2) := by
  have h := add_stored_bounded (stored_raw_bound hw) (stored_raw_bound hq)
  simpa only [GraphWalkExtension.result,two_mul] using h

theorem scan_witness {adjacency : List Bits} {rows : List Fraction} {sw u : Bits}
    {xs : List Entry} {q : Walk} (h : scan adjacency rows sw u xs=some q) :
    ∃ x∈xs,GraphWalkExtension.result rows sw (u,x.1) x.2=q := by
  induction xs generalizing q with
  | nil => simp [scan] at h
  | cons x xs ih =>
    simp only [scan] at h
    split at h
    · cases ht : scan adjacency rows sw u xs with
      | none =>
        simp only [ht,pick,Option.some.injEq] at h
        exact ⟨x,List.mem_cons_self,h⟩
      | some y =>
        simp only [ht,pick,Option.some.injEq,choose] at h
        split at h
        · exact ⟨x,List.mem_cons_self,h⟩
        · obtain ⟨z,hz,hzq⟩ := ih ht
          exact ⟨z,List.mem_cons_of_mem _ hz,hzq.trans h⟩
    · obtain ⟨z,hz,hzq⟩ := ih h
      exact ⟨z,List.mem_cons_of_mem _ hz,hzq⟩

theorem scan_width {adjacency : List Bits} {rows : List Fraction} {sw u : Bits}
    {xs : List Entry} {q : Walk} {B : ℕ}
    (hw : StoredBounded (OutgoingCostProgram.result rows sw u) B)
    (hx : ∀ x∈xs,StoredBounded x.2.cost B) (h : scan adjacency rows sw u xs=some q) :
    StoredBounded q.cost (2*B+2) := by
  obtain ⟨x,hx',rfl⟩ := scan_witness h
  exact extension_width hw (hx x hx')

def perEntryBound (B N S : ℕ) : ℕ :=
  12*N+20*B+100*(S+B+N+1)+20000*(4*B+2)^2+400*(8*B+9)^2+93
def instructionBound (m B N S : ℕ) : ℕ := m*perEntryBound B N S+4

theorem test_bound {u v : Bits} {B N : ℕ}
    (hu : u.length ≤ B) (hv : v.length ≤ B) (iu : value u ≤ N) (iv : value v ≤ N) :
    testSteps u v ≤ 12*N+20*B+39 := by
  have a := BinaryPointerListRead.steps_bound u
  have b := BinaryPointerListRead.steps_bound v
  simp only [testSteps,GraphAdjacencyProgram.steps]
  omega

theorem extension_bound {rows : List Fraction} {sw u v : Bits} {q : Walk} {B N : ℕ}
    (hw : StoredBounded (OutgoingCostProgram.result rows sw u) B) (hq : StoredBounded q.cost B)
    (hu : u.length ≤ B) (iu : value u ≤ N) :
    extendSteps rows sw (u,v) q ≤ 100*(sw.length+B+N+1)+20000*(4*B+2)^2+26 := by
  have ho := OutgoingCostProgram.instructions_bound sw u
  have ha := CanonicalRationalAddition.instructions_bound (OutgoingCostProgram.result rows sw u) q.cost
  have sz : CanonicalRationalAddition.inputSize (OutgoingCostProgram.result rows sw u) q.cost ≤ 4*B+2 := by
    rcases hw with ⟨hwn,hwd⟩;rcases hq with ⟨hqn,hqd⟩
    dsimp [CanonicalRationalAddition.inputSize];omega
  have hb := ha.trans (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left sz 2))
  simp only [extendSteps,GraphWalkExtension.steps]
  omega

theorem pick_bound {x y : Walk} {B : ℕ}
    (hx : StoredBounded x.cost (2*B+2)) (hy : StoredBounded y.cost (2*B+2)) :
    pickSteps x y ≤ 400*(8*B+9)^2+8 := by
  have hc := RationalComparisonProgram.instructions_bound x.cost y.cost
  have sz : RationalComparisonProgram.inputSize x.cost y.cost ≤ 8*B+9 := by
    rcases hx with ⟨hxn,hxd⟩;rcases hy with ⟨hyn,hyd⟩
    dsimp [RationalComparisonProgram.inputSize];omega
  have hb := hc.trans (Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left sz 2))
  simp only [pickSteps];omega

theorem steps_bound (adjacency : List Bits) (rows : List Fraction) (sw u : Bits)
    (xs : List Entry) (B N : ℕ) (hB : 1 ≤ B)
    (hr : ∀ q∈rows,StoredBounded q B) (hi : value u<rows.length)
    (hu : u.length ≤ B) (iu : value u ≤ N) (hx : ∀ x∈xs,EntryBound B N x) :
    steps adjacency rows sw u xs+1 ≤ instructionBound xs.length B N sw.length := by
  have hw := outgoing_width rows sw u B hB hr hi
  suffices h : steps adjacency rows sw u xs ≤ xs.length*perEntryBound B N sw.length+3 by
    dsimp [instructionBound];omega
  induction xs with
  | nil => simp [steps]
  | cons x xs ih =>
    have hhead := hx x List.mem_cons_self
    have htail := fun y hy => hx y (List.mem_cons_of_mem _ hy)
    have ht := ih htail
    have he := extension_bound hw hhead.2.2 hu iu (v:=x.1)
    have ha := test_bound hu hhead.1 iu hhead.2.1
    simp only [steps,List.length_cons]
    split
    · cases hs : scan adjacency rows sw u xs with
      | none => dsimp only;dsimp [perEntryBound] at *;nlinarith
      | some y =>
        have hy := scan_width hw (fun z hz => (htail z hz).2.2) hs
        have hp := pick_bound (extension_width (v:=x.1) hw hhead.2.2) hy
        dsimp only
        dsimp [perEntryBound] at *
        nlinarith
    · dsimp [perEntryBound] at *;nlinarith

end DirectedFlowCutGap.GraphRelaxationProgram
