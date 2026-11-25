import DirectedFlowCutGap.MeasuredPaidSparsestRound
import DirectedFlowCutGap.AmplifiedSparsestDispatch

/-! Use the measured budgeted solvers after screening the original requests.
Disconnected and inseparable instances return their original unread tape. -/
namespace DirectedFlowCutGap.MeasuredBudgetedSparsestDispatch

open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency)
open BinaryFractionalRows (Row)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights)
open RationalSparsestEdgeRound (Mask)
open RetainedGridState (Flags)
open AmplifiedSparsestDispatch (Outcome)
open PhysicalCoverAccess (Read)
open Polynomial

variable {n m : ℕ}

private def unitPrices (n : ℕ) : Weights n :=
  Vector.replicate n (Vector.replicate n BinaryRational.one)

private def unreachable (A : Adjacency n) (P : Vector (Edge n) m) : Read (Fin m) :=
  MeasuredFreeResources.edge A (unitPrices n) P

private theorem unreachable_value (A : Adjacency n) (P : Vector (Edge n) m) :
    (unreachable A P).1 = AmplifiedSparsestDispatch.unreachable A P :=
  MeasuredFreeResources.edge_value A (unitPrices n) P

private theorem unreachable_paid (A : Adjacency n) (P : Vector (Edge n) m) :
    (unreachable A P).2 ≤ MeasuredFreeResources.edgeWork n m 1 := by
  apply MeasuredFreeResources.edge_charge
  intro i j
  simp [unitPrices,BinaryRational.StoredBounded,BinaryRational.one]

private def distinct (P : Vector (Edge n) m) (i : Fin m) : (Edge n × Bool) × ℕ :=
  let request := BinaryVectorAccess.read P i
  let same := BinaryEdgeGadget.equalFin request.1.1 request.1.2
  ((request.1,!same.1),request.2+same.2+1)

private theorem distinct_value (P : Vector (Edge n) m) (i : Fin m) :
    (distinct P i).1 = (P.get i,AmplifiedSparsestDispatch.edgeTest P i) := by
  simp only [distinct,BinaryVectorAccess.read_value,AmplifiedSparsestDispatch.edgeTest]
  change (P.get i,!(BinaryEdgeGadget.equalFin (P.get i).1 (P.get i).2).1) =
    (P.get i,decide ((P.get i).1 ≠ (P.get i).2))
  by_cases equal : (P.get i).1 = (P.get i).2
  · have same := (BinaryEdgeGadget.equalFin_value (P.get i).1 (P.get i).2).mpr equal
    rw [same]
    simp [equal]
  · have no : (BinaryEdgeGadget.equalFin (P.get i).1 (P.get i).2).1 = false :=
      Bool.eq_false_iff.mpr (fun h => equal ((BinaryEdgeGadget.equalFin_value ..).mp h))
    simp [no,equal]

private def pairWork (n m : ℕ) : ℕ :=
  BinaryVectorAccess.budget m+64*(n+1)^2+1

private theorem distinct_paid (P : Vector (Edge n) m) (i : Fin m) :
    (distinct P i).2 ≤ pairWork n m := by
  unfold distinct pairWork
  exact Nat.add_le_add_right (Nat.add_le_add
    (BinaryVectorAccess.read_paid P i (BinaryNaturalOperations.size_le_self m))
    (BinaryEdgeGadget.equalFin_paid _ _)) 1

private def edgeTest (P : Vector (Edge n) m) (i : Fin m) : Bool × ℕ :=
  let probed := distinct P i
  (probed.1.2,probed.2)

private def vertexTest (A : Adjacency n) (P : Vector (Edge n) m) (i : Fin m) : Bool × ℕ :=
  let probed := distinct P i
  if probed.1.2 then
    let arc := BinaryVectorAccess.readMatrix A probed.1.1.1 probed.1.1.2
    (!arc.1,probed.2+arc.2+1)
  else
    (false,probed.2+1)

private theorem vertexTest_value (A : Adjacency n) (P : Vector (Edge n) m) (i : Fin m) :
    (vertexTest A P i).1 = AmplifiedSparsestDispatch.vertexTest A P i := by
  simp only [vertexTest,distinct_value,AmplifiedSparsestDispatch.vertexTest]
  cases AmplifiedSparsestDispatch.edgeTest P i <;> simp [BinaryVectorAccess.readMatrix_value]

private theorem vertexTest_paid (A : Adjacency n) (P : Vector (Edge n) m) (i : Fin m) :
    (vertexTest A P i).2 ≤ pairWork n m+2*BinaryVectorAccess.budget n+1 := by
  have test := distinct_paid P i
  have width := BinaryNaturalOperations.size_le_self n
  have arc := BinaryVectorAccess.readMatrix_paid A (distinct P i).1.1.1 (distinct P i).1.1.2 width width
  unfold vertexTest
  dsimp only
  split <;> dsimp only <;> omega

private def edgeDemand (P : Vector (Edge n) m) : Read (Fin m) :=
  MeasuredFirstResult.find (edgeTest P) (List.finRange m)

private def vertexDemand (A : Adjacency n) (P : Vector (Edge n) m) : Read (Fin m) :=
  MeasuredFirstResult.find (vertexTest A P) (List.finRange m)

private theorem edgeDemand_value (P : Vector (Edge n) m) :
    (edgeDemand P).1 = AmplifiedSparsestDispatch.edgeDemand P := by
  simp only [edgeDemand,MeasuredFirstResult.find_value,edgeTest,distinct_value,AmplifiedSparsestDispatch.edgeDemand]

private theorem vertexDemand_value (A : Adjacency n) (P : Vector (Edge n) m) :
    (vertexDemand A P).1 = AmplifiedSparsestDispatch.vertexDemand A P := by
  simp only [vertexDemand,MeasuredFirstResult.find_value,vertexTest_value,AmplifiedSparsestDispatch.vertexDemand]

private def edgeDemandWork (n m : ℕ) : ℕ := m*(pairWork n m+4)+1
private def vertexDemandWork (n m : ℕ) : ℕ := m*(pairWork n m+2*BinaryVectorAccess.budget n+1+4)+1

private theorem edgeDemand_paid (P : Vector (Edge n) m) :
    (edgeDemand P).2 ≤ edgeDemandWork n m := by
  simpa only [edgeDemand,edgeDemandWork,List.length_finRange] using
    MeasuredFirstResult.find_charge (edgeTest P) (List.finRange m) (fun i _ => distinct_paid P i)

private theorem vertexDemand_paid (A : Adjacency n) (P : Vector (Edge n) m) :
    (vertexDemand A P).2 ≤ vertexDemandWork n m := by
  simpa only [vertexDemand,vertexDemandWork,List.length_finRange] using
    MeasuredFirstResult.find_charge (vertexTest A P) (List.finRange m) (fun i _ => vertexTest_paid A P i)

private def finish {Cut : Type} (connected : Read (Fin m)) (empty : Cut)
    (separable : Unit → Read (Fin m)) (run : Fin m → Read (Cut × Bits)) (bits : Bits) : Read (Outcome Cut) :=
  match connected.1 with
  | some _ => (some (.cut empty bits),connected.2)
  | none =>
    let demanded := separable ()
    match demanded.1 with
    | none => (some (.noSeparatingPair bits),connected.2+demanded.2)
    | some i =>
      let cut := run i
      (cut.1.map fun (mask,rest) => .cut mask rest,connected.2+demanded.2+cut.2)

private theorem finish_paid {Cut : Type} (connected : Read (Fin m)) (empty : Cut)
    (separable : Unit → Read (Fin m)) (run : Fin m → Read (Cut × Bits)) (bits : Bits)
    {A B C : ℕ} (a : connected.2 ≤ A) (b : (separable ()).2 ≤ B) (c : ∀ i, (run i).2 ≤ C) :
    (finish connected empty separable run bits).2 ≤ A+B+C := by
  cases gone : connected.1 with
  | some i => simp only [finish,gone]; omega
  | none =>
    cases needed : (separable ()).1 with
    | none => simp only [finish,gone,needed]; omega
    | some i => simpa only [finish,gone,needed] using Nat.add_le_add (Nat.add_le_add a b) (c i)

def edge (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Read (Outcome (Mask n)) :=
  finish (unreachable A P) (Vector.replicate n (Vector.replicate n false))
    (fun _ => edgeDemand P) (fun i =>
      MeasuredPaidSparsestRound.edge ((Nat.zero_le _).trans_lt (P.get i).1.isLt) A c P extra confidence bits) bits

def vertex (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Read (Outcome (Flags n)) :=
  finish (unreachable A P) (Vector.replicate n false)
    (fun _ => vertexDemand A P) (fun i =>
      MeasuredPaidSparsestRound.vertex ((Nat.zero_le _).trans_lt (P.get i).1.isLt) A c P extra confidence bits) bits

theorem edge_value (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) :
    (edge A c P extra confidence bits).1 = AmplifiedSparsestDispatch.runEdge A c P extra confidence bits := by
  simp only [edge,finish,unreachable_value,edgeDemand_value,AmplifiedSparsestDispatch.runEdge]
  cases AmplifiedSparsestDispatch.unreachable A P with
  | some i => rfl
  | none =>
    cases AmplifiedSparsestDispatch.edgeDemand P with
    | none => rfl
    | some i => simp only [MeasuredPaidSparsestRound.edge_value]

theorem vertex_value (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) :
    (vertex A c P extra confidence bits).1 = (match AmplifiedSparsestDispatch.unreachable A P with
    | some _ => some (.cut (Vector.replicate n false) bits)
    | none => match AmplifiedSparsestDispatch.vertexDemand A P with
      | none => some (.noSeparatingPair bits)
      | some i =>
        (ConcurrentVertexBudgetRound.run ((Nat.zero_le _).trans_lt (P.get i).1.isLt) A c P extra confidence bits).map
          fun (mask,rest) => .cut mask rest) := by
  simp only [vertex,finish,unreachable_value,vertexDemand_value]
  cases AmplifiedSparsestDispatch.unreachable A P with
  | some i => rfl
  | none =>
    cases AmplifiedSparsestDispatch.vertexDemand A P with
    | none => rfl
    | some i => simp only [MeasuredPaidSparsestRound.vertex_value]

theorem edge_complete (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) (enough : AmplifiedSparsestEdgeTape.budget n extra confidence ≤ bits.length) :
    ∃ answer used, (edge A c P extra confidence bits).1 = some answer ∧
      answer.suffix = bits.drop used ∧ used ≤ AmplifiedSparsestEdgeTape.budget n extra confidence := by
  rw [edge_value]
  exact AmplifiedSparsestDispatch.edge_complete A c P extra confidence bits enough

theorem vertex_complete (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) (enough : AmplifiedSparsestVertexTape.budget n extra confidence ≤ bits.length) :
    ∃ answer used, (vertex A c P extra confidence bits).1 = some answer ∧
      answer.suffix = bits.drop used ∧ used ≤ AmplifiedSparsestVertexTape.budget n extra confidence := by
  rw [vertex_value]
  cases gone : AmplifiedSparsestDispatch.unreachable A P with
  | some i => exact ⟨_,0,rfl,rfl,Nat.zero_le _⟩
  | none =>
    cases found : AmplifiedSparsestDispatch.vertexDemand A P with
    | none => exact ⟨_,0,rfl,rfl,Nat.zero_le _⟩
    | some i =>
      have hn : 0 < n := (Nat.zero_le _).trans_lt (P.get i).1.isLt
      have all := AmplifiedSparsestDispatch.reachable_of_none A P gone
      obtain ⟨different,notDirect⟩ := AmplifiedSparsestDispatch.vertexDemand_found A P found
      obtain ⟨mask,used,read,paid⟩ := ConcurrentVertexBudgetRound.complete hn A c P all i different notDirect
        extra confidence bits enough
      exact ⟨.cut mask (bits.drop used),used,by simp only [read,Option.map_some],rfl,paid⟩

noncomputable def edgeWork (p : Polynomial ℕ) (n m B extra confidence : ℕ) : ℕ :=
  MeasuredFreeResources.edgeWork n m 1+edgeDemandWork n m+MeasuredPaidSparsestRound.edgeWork p n m B extra confidence

noncomputable def vertexWork (p : Polynomial ℕ) (n m B extra confidence : ℕ) : ℕ :=
  MeasuredFreeResources.edgeWork n m 1+vertexDemandWork n m+MeasuredPaidSparsestRound.vertexWork p n m B extra confidence

theorem edge_charge (p : Polynomial ℕ)
    (cutoff : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) {B : ℕ} (fits : MatrixFits c B) :
    (edge A c P extra confidence bits).2 ≤ edgeWork p n m B extra confidence :=
  finish_paid _ _ _ _ _ (unreachable_paid A P) (edgeDemand_paid P)
    (fun _ => MeasuredPaidSparsestRound.edge_charge p cutoff _ A c P extra confidence bits fits)

theorem vertex_charge (p : Polynomial ℕ)
    (cutoff : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) {B : ℕ} (fits : ∀ j, StoredBounded (c.get j) B) :
    (vertex A c P extra confidence bits).2 ≤ vertexWork p n m B extra confidence :=
  finish_paid _ _ _ _ _ (unreachable_paid A P) (vertexDemand_paid A P)
    (fun _ => MeasuredPaidSparsestRound.vertex_charge p cutoff _ A c P extra confidence bits fits)

end DirectedFlowCutGap.MeasuredBudgetedSparsestDispatch
