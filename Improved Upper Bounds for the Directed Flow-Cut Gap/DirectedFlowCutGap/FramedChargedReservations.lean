import DirectedFlowCutGap.FramedEdgeTerminalArrays
import DirectedFlowCutGap.FramedVertexPackedLayout

/-! Bound the recorded solver work and the explicit binary reservation
interpreter together, using the encoded width of the initial address. -/
namespace DirectedFlowCutGap.FramedChargedReservations

open BinaryArithmetic EncodedArrayStorage Polynomial
open BinaryArrayNestedStorage (Code)
open PhysicalIntegerRoundingCost (eval_mono)

def reservationWork (start : ℕ) (trace : Code) : ℕ :=
  (BinaryAllocationTrace.allocate start.bits (trace.map BinaryAllocationTrace.reservation)).charge

private theorem width_add (start cells : ℕ) : (start+cells).size ≤ start.size+cells := by
  induction cells with
  | zero => simp
  | succ cells ih =>
    have width := Nat.size_le.mp ih
    have positive : 1 ≤ 2^(start.size+cells) := Nat.one_le_two_pow
    apply Nat.size_le.mpr
    simp only [Nat.add_succ,Nat.pow_succ]
    omega

noncomputable def budget (charged cells copies : Polynomial ℕ) : Polynomial ℕ :=
  charged+copies*(32*(X+cells+2)+8)+1

private theorem work_le (charged cells copies : Polynomial ℕ) (x start recorded reservation : ℕ)
    (actual : recorded ≤ charged.eval x)
    (placed : reservation ≤ BinaryAllocationTrace.chargeBound (copies.eval x) (start+cells.eval x).size) :
    recorded+reservation ≤ (budget charged cells copies).eval (x+start.size) := by
  let y := x+start.size
  have hxy : x ≤ y := Nat.le_add_right _ _
  have initial : start.size ≤ y := Nat.le_add_left _ _
  have width : (start+cells.eval x).size ≤ y+cells.eval y :=
    (width_add start _).trans (Nat.add_le_add initial (eval_mono cells hxy))
  have room : BinaryAllocationTrace.chargeBound (copies.eval x) (start+cells.eval x).size ≤
      BinaryAllocationTrace.chargeBound (copies.eval y) (y+cells.eval y) := by
    have count := eval_mono copies hxy
    unfold BinaryAllocationTrace.chargeBound
    gcongr
  simp only [budget,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
  rw [Nat.add_assoc]
  exact Nat.add_le_add (actual.trans (eval_mono _ hxy)) (placed.trans room)

theorem vertex : ∃ p : Polynomial ℕ,
    ∀ (κ start : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let solver := PaidFramedVertexWire.vertexWithTerminalRowWork κ mode source tape
      ∃ post rounds : Code, FramedVertexPackedLayout.Prefix source post ∧
        FramedVertexPackedLayout.Model κ mode source tape rounds ∧
        let trace := PhysicalSourceInputJoin.vertexArrayCode source++post++rounds
        solver.1.2+solver.2.1+solver.2.2+reservationWork start trace ≤ p.eval (source.length+κ+start.size) := by
  obtain ⟨charged,paid⟩ := PaidFramedVertexWire.vertex_terminal_row_polynomial
  obtain ⟨cells,copies,layout⟩ := FramedVertexPackedLayout.polynomial
  refine ⟨budget charged cells copies,?_⟩
  intro κ start mode source tape
  obtain ⟨post,rounds,prefixModel,roundModel,_,_,place⟩ := layout κ mode source tape
  exact ⟨post,rounds,prefixModel,roundModel,
    work_le charged cells copies (source.length+κ) start _ _ (paid κ mode source tape) (place start).2.1⟩

theorem edge : ∃ p : Polynomial ℕ,
    ∀ (κ start : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let solver := PaidDirectEdgeWire.edgeWithTerminalRowWork κ mode source tape
      let input := PhysicalSourceInputJoin.edgeArrayCode source
      ∃ post rounds : Code,
        (match (PhysicalSourceInputJoin.edge source).1 with
        | none => post=[]
        | some ⟨_,D⟩ => FramedEdgeStorage.AfterInput D input post) ∧
        FramedEdgePackedLayout.Model κ mode source tape rounds ∧
        let trace := input++post++rounds++FramedEdgeTerminalArrays.wireCode κ mode source tape
        solver.1.2+solver.2.1.total+solver.2.2+reservationWork start trace ≤ p.eval (source.length+κ+start.size) := by
  obtain ⟨charged,paid⟩ := PaidDirectEdgeWire.wire_terminal_row_polynomial
  obtain ⟨cells,copies,layout⟩ := FramedEdgeTerminalArrays.polynomial
  refine ⟨budget charged cells copies,?_⟩
  intro κ start mode source tape
  obtain ⟨post,rounds,prefixModel,roundModel,_,_,place⟩ := layout κ mode source tape
  exact ⟨post,rounds,prefixModel,roundModel,
    work_le charged cells copies (source.length+κ) start _ _ (paid κ mode source tape) (place start).2.1⟩

end DirectedFlowCutGap.FramedChargedReservations
