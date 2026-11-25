import DirectedFlowCutGap.MeasuredFirstResult
import DirectedFlowCutGap.MeasuredSparsestDistances
import DirectedFlowCutGap.ConcurrentEdgeZeroPrices
import DirectedFlowCutGap.ConcurrentVertexBudget
import DirectedFlowCutGap.BinaryNaturalOperations

/-! Test free resources with exact binary price checks and the original
ordered demand scan. Vertex separation still excludes both endpoints. -/
namespace DirectedFlowCutGap.MeasuredFreeResources

open scoped NNRat
open BinaryFractionalWalkOracle (Adjacency decodeCost)
open BinaryRational (Fraction StoredBounded)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights cost)
open RawNonnegativeRational (Code)
open RetainedGridState (Flags)
open MeasuredFirstResult (find find_value find_charge)
open MeasuredBudgetPrices (tabulate tabulate_value tabulate_charge)

variable {n m : ℕ}

def positivePrice (a : Fraction) : Bool × ℕ :=
  let read := BinaryRawRational.decode a
  let zero := BinaryRawRational.le read.1 Code.zero
  (!zero.1,read.2+zero.2+1)

theorem positivePrice_value (a : Fraction) :
    (positivePrice a).1 = decide (0 < (BinaryRational.decode a).value) := by
  apply Bool.eq_iff_iff.mpr
  simp only [positivePrice,Bool.not_eq,BinaryRawRational.le_value,BinaryRawRational.decode_value,
    Ne,Code.le_eq_true,Code.value_zero,not_le,decide_eq_true_eq]

def priceWork (B : ℕ) : ℕ := 40*(B+1)^2+BinaryRawRational.budget B+1

theorem positivePrice_charge (a : Fraction) {B : ℕ} (fit : StoredBounded a B) :
    (positivePrice a).2 ≤ priceWork B := by
  have raw : (BinaryRawRational.decode a).1.Bounded B := by
    rw [BinaryRawRational.decode_value]
    exact BinaryFractionalRows.stored_raw_bound fit
  exact Nat.add_le_add_right (Nat.add_le_add (BinaryRawRational.decode_paid fit)
    (BinaryRawRational.le_paid raw (Code.bounded_mono Code.bounded_zero (Nat.zero_le B)))) 1

private def positiveCell (A : Adjacency n) (c : Weights n) (e : Edge n) : Bool × ℕ :=
  if A[e.1.val][e.2.val] then positivePrice ((cost c) e).1 else (false,1)

def positiveGraph (A : Adjacency n) (c : Weights n) : Adjacency n × ℕ :=
  tabulate fun u => tabulate fun v => positiveCell A c (u,v)

theorem positiveGraph_value (A : Adjacency n) (c : Weights n) :
    (positiveGraph A c).1 = ConcurrentEdgeZeroPrices.positiveGraph A c := by
  apply Vector.ext
  intro u hu
  apply Vector.ext
  intro v hv
  simp only [positiveGraph,tabulate_value,Vector.getElem_ofFn,positiveCell,
    ConcurrentEdgeZeroPrices.positiveGraph,ConcurrentEdgeZeroPrices.rawPrice,decodeCost]
  split <;> rename_i present
  · simp only [positivePrice_value,present,Bool.true_and]
    rfl
  · simp [present]

theorem positiveGraph_charge (A : Adjacency n) (c : Weights n) {B : ℕ} (fit : MatrixFits c B) :
    (positiveGraph A c).2 ≤ n*n*priceWork B := by
  rw [Nat.mul_assoc]
  apply tabulate_charge
  intro u
  apply tabulate_charge
  intro v
  simp only [positiveCell]
  split
  · exact positivePrice_charge _ (fit u v)
  · unfold priceWork
    omega

def missingEdge (A : Adjacency n) (c : Weights n) (d : Edge n) : Bool × ℕ :=
  let seen := MeasuredSparsestDistances.edge A c d
  (seen.1.isNone,seen.2+1)

theorem missingEdge_value (A : Adjacency n) (c : Weights n) (d : Edge n) :
    (missingEdge A c d).1 = (RationalSparsestEdgeDistances.distance A c d).isNone := by
  rw [← MeasuredSparsestDistances.edge_value]
  cases h : (MeasuredSparsestDistances.edge A c d).1 <;> simp [missingEdge,h]

def edge (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) : Option (Fin m) × ℕ :=
  let graph := positiveGraph A c
  let first := find (fun d => missingEdge graph.1 c (P.get d)) (List.finRange m)
  (first.1,graph.2+first.2)

theorem edge_value (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (edge A c P).1 = ConcurrentEdgeZeroPrices.detect A c P := by
  simp only [edge,find_value,positiveGraph_value,missingEdge_value,ConcurrentEdgeZeroPrices.detect]

def edgeWork (n m B : ℕ) : ℕ := n*n*priceWork B+m*(MeasuredSparsestDistances.edgeWork n B+5)+1

theorem edge_charge (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) {B : ℕ}
    (fit : MatrixFits c B) : (edge A c P).2 ≤ edgeWork n m B := by
  have built := positiveGraph_charge A c fit
  have scanned := find_charge (fun d => missingEdge (positiveGraph A c).1 c (P.get d))
    (List.finRange m) (B := MeasuredSparsestDistances.edgeWork n B+1) fun d _ =>
      Nat.add_le_add_right (MeasuredSparsestDistances.edge_bounds _ c (P.get d) fit).2 1
  simpa only [edge,edgeWork,List.length_finRange,Nat.add_assoc] using Nat.add_le_add built scanned

private def lengthCell (c : Weights n) (u v : Fin n) (zeroLength fullLength : Fraction) : Fraction × ℕ :=
  let mark := positivePrice ((c.get u).get v)
  (if mark.1 then zeroLength else fullLength,mark.2+1)

def freeLength (c : Weights n) (m : ℕ) : Weights n × ℕ :=
  let zeroLength := BinaryRawRational.encode Code.zero
  let fullLength := BinaryRawRational.encode (Code.ofNat m)
  let matrix := tabulate fun u => tabulate fun v => lengthCell c u v zeroLength.1 fullLength.1
  (matrix.1,zeroLength.2+fullLength.2+matrix.2)

private theorem natCode (j : ℕ) : Code.ofNNRat (j : ℚ≥0) = Code.ofNat j := by
  simp [Code.ofNNRat,Code.ofNat]

theorem freeLength_value (c : Weights n) (m : ℕ) :
    (freeLength c m).1 = ConcurrentEdgeZeroPrices.freeLength c m := by
  apply Vector.ext
  intro u hu
  apply Vector.ext
  intro v hv
  simp only [freeLength,tabulate_value,ConcurrentEdgeZeroPrices.freeLength,Vector.getElem_ofFn,
    lengthCell,positivePrice_value,ConcurrentEdgeZeroPrices.rawPrice,cost,decodeCost,decide_eq_true_eq]
  let q := (BinaryRational.decode ((c.get ⟨u,hu⟩).get ⟨v,hv⟩)).value
  change (if 0 < q then (BinaryRawRational.encode Code.zero).1
      else (BinaryRawRational.encode (Code.ofNat m)).1) =
    (BinaryRawRational.encode (Code.ofNNRat (if 0 < q then 0 else (m : ℚ≥0)))).1
  by_cases positive : 0 < q
  · simp only [ite_eq_left positive]
    rfl
  · simp only [ite_eq_right positive,natCode]

def freeLengthWork (n m B : ℕ) : ℕ := 160+40*(m.size+2)^2+n*n*(priceWork B+1)

theorem freeLength_bounds (c : Weights n) (m : ℕ) {B : ℕ} (fit : MatrixFits c B) :
    MatrixFits (freeLength c m).1 (m.size+1) ∧
      (freeLength c m).2 ≤ freeLengthWork n m B := by
  let zeroLength := BinaryRawRational.encode Code.zero
  let fullLength := BinaryRawRational.encode (Code.ofNat m)
  have unitFit : (Code.ofNat m).Bounded m.size := BinaryNaturalOperations.ofNat_fit le_rfl
  have noneFit : StoredBounded zeroLength.1 (m.size+1) :=
    BinaryFractionalWalkBounds.stored_mono (BinaryRawRational.encode_width Code.bounded_zero) (by omega)
  have someFit : StoredBounded fullLength.1 (m.size+1) := BinaryRawRational.encode_width unitFit
  constructor
  · intro u v
    change StoredBounded (freeLength c m).1[u.val][v.val] _
    simp only [freeLength,tabulate_value,Fin.eta,lengthCell]
    split
    · exact noneFit
    · exact someFit
  · have matrix : (tabulate fun u => tabulate fun v => lengthCell c u v zeroLength.1 fullLength.1).2 ≤
        n*n*(priceWork B+1) := by
      rw [Nat.mul_assoc]
      exact tabulate_charge _ fun u => tabulate_charge _ fun v =>
        Nat.add_le_add_right (positivePrice_charge _ (fit u v)) 1
    have emptyWork : zeroLength.2 ≤ 160 :=
      BinaryRawRational.encode_paid Code.bounded_zero
    have unitWork := BinaryRawRational.encode_paid unitFit
    exact Nat.add_le_add (Nat.add_le_add emptyWork unitWork) matrix

def freeMask (c : BinaryFractionalRows.Row n) : Flags n × ℕ :=
  tabulate fun i =>
    let present := positivePrice (c.get i)
    (!present.1,present.2+1)

theorem freeMask_value (c : BinaryFractionalRows.Row n) :
    (freeMask c).1 = ConcurrentVertexBudget.freeMask c := by
  apply Vector.ext
  intro i hi
  simp only [freeMask,tabulate_value,Vector.getElem_ofFn,positivePrice_value,
    ConcurrentVertexBudget.freeMask,ConcurrentVertexBudget.raw]
  apply Bool.eq_iff_iff.mpr
  let q := (BinaryRational.decode (c.get ⟨i,hi⟩)).value
  change (!decide (0 < q)) = true ↔ decide (q = 0) = true
  simp only [Bool.not_eq,Ne,decide_eq_true_eq,not_lt]
  exact ⟨fun h => le_antisymm h zero_le,fun h => h.le⟩

theorem freeMask_charge (c : BinaryFractionalRows.Row n) {B : ℕ}
    (fit : ∀ i, StoredBounded (c.get i) B) : (freeMask c).2 ≤ n*(priceWork B+1) :=
  tabulate_charge _ (fun i => Nat.add_le_add_right (positivePrice_charge _ (fit i)) 1)

def vertexTest (A : Adjacency n) (w : BinaryFractionalRows.Row n) (d : Edge n) : Bool × ℕ :=
  let distance := MeasuredSparsestDistances.vertex A w d
  match distance.1 with
  | none => (true,distance.2+1)
  | some q =>
    let cut := BinaryRawRational.le Code.one q
    (cut.1,distance.2+cut.2+1)

theorem vertexTest_value (A : Adjacency n) (mask : Flags n) (d : Edge n) :
    (vertexTest A (RationalVertexSparsityCode.indicator mask) d).1 =
      RationalVertexSparsityCode.separates A mask d := by
  simp only [RationalVertexSparsityCode.separates,← MeasuredSparsestDistances.vertex_value]
  cases h : (MeasuredSparsestDistances.vertex A (RationalVertexSparsityCode.indicator mask) d).1 with
  | none => simp [vertexTest,h]
  | some q =>
    apply Bool.eq_iff_iff.mpr
    simp only [vertexTest,h,Option.map_some,Option.getD_some,BinaryRawRational.le_value,Code.le_eq_true,
      Code.value_one,decide_eq_true_eq]

private theorem indicator_fit (mask : Flags n) (i : Fin n) :
    StoredBounded ((RationalVertexSparsityCode.indicator mask).get i) 1 := by
  change StoredBounded (RationalVertexSparsityCode.indicator mask)[i.val] 1
  simp only [RationalVertexSparsityCode.indicator,Vector.getElem_map]
  split
  · norm_num [StoredBounded,BinaryRational.one]
  · exact BinaryFractionalWalkBounds.zero_stored

def vertexTestWork (n : ℕ) : ℕ :=
  MeasuredSparsestDistances.vertexWork n 1+
    BinaryRawRational.budget (MeasuredSparsestDistances.distanceWidth n 1)+1

theorem vertexTest_charge (A : Adjacency n) (mask : Flags n) (d : Edge n) :
    (vertexTest A (RationalVertexSparsityCode.indicator mask) d).2 ≤ vertexTestWork n := by
  obtain ⟨fits,paid⟩ :=
    MeasuredSparsestDistances.vertex_bounds A (RationalVertexSparsityCode.indicator mask) d (indicator_fit mask)
  simp only [max_self] at fits
  unfold vertexTest vertexTestWork
  dsimp only
  split
  · omega
  · rename_i q found
    have work := BinaryRawRational.le_paid (Code.bounded_mono Code.bounded_one
      (Nat.zero_le (MeasuredSparsestDistances.distanceWidth n 1))) (fits q found)
    omega

def vertex (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) :
    (Flags n × Option (Fin m)) × ℕ :=
  let mask := freeMask c
  let weights := RationalVertexSparsityCode.indicator mask.1
  let check := find (fun i => vertexTest A weights (P.get i)) (List.finRange m)
  ((mask.1,check.1),mask.2+check.2)

theorem vertex_value (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) :
    (vertex A c P).1 = (ConcurrentVertexBudget.freeMask c,ConcurrentVertexBudget.freeDemand A c P) := by
  simp only [vertex,find_value,freeMask_value,vertexTest_value,ConcurrentVertexBudget.freeDemand]

def vertexWork (n m B : ℕ) : ℕ := n*(priceWork B+1)+m*(vertexTestWork n+4)+1

theorem vertex_charge (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) {B : ℕ}
    (fit : ∀ i, StoredBounded (c.get i) B) : (vertex A c P).2 ≤ vertexWork n m B := by
  have checked := find_charge (fun i => vertexTest A (RationalVertexSparsityCode.indicator (freeMask c).1) (P.get i))
    (List.finRange m) (fun i _ => vertexTest_charge A (freeMask c).1 (P.get i))
  simpa only [vertex,vertexWork,List.length_finRange,Nat.add_assoc] using
    Nat.add_le_add (freeMask_charge c fit) checked

end DirectedFlowCutGap.MeasuredFreeResources
