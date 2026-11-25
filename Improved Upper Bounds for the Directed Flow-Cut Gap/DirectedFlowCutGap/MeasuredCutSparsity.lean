import DirectedFlowCutGap.MeasuredFreeResources
import DirectedFlowCutGap.MeasuredPathColumn
import DirectedFlowCutGap.MeasuredGraphPlanTotals
import DirectedFlowCutGap.RationalEdgeSparsityCode
import DirectedFlowCutGap.BinaryCutPriceSelection

/-! Account for the exact sparsity scores of returned original masks.
Each indexed request is tested using the previous endpoint convention. -/
namespace DirectedFlowCutGap.MeasuredCutSparsity

open scoped BigOperators NNRat
open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge Resource edge resource)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RawNonnegativeRational (Code)
open FractionalCoverRawCore (RawRow RowBounded get rational)
open RationalEdgeThresholds (Weights)
open RationalSparsestEdgeRound (Mask)
open RetainedGridState (Flags flag)
open MeasuredPathColumn (resourceCount resourceCount_le resourceCount_value resourceCount_charge rowWork indicator)
open MeasuredMultiplicityForms (sum sum_value sum_charge)

variable {n m r : ℕ}

private theorem counted (test : Fin m → Bool × ℕ) :
    (resourceCount test).1 = (Finset.univ.filter fun i => (test i).1).card := by
  rw [resourceCount_value]
  simp [indicator]

private def edgeTests (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (mask : Mask n) :
    Fin m → Bool × ℕ :=
  let graph := RationalEdgeSparsityCode.without A mask
  fun i => MeasuredFreeResources.missingEdge graph c (P.get i)

private theorem edgeCount_value (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (mask : Mask n) :
    (resourceCount (edgeTests A c P mask)).1 = RationalEdgeSparsityCode.count A c P mask := by
  rw [counted]
  simp only [edgeTests,MeasuredFreeResources.missingEdge_value,RationalEdgeSparsityCode.count,
    RationalEdgeSparsityCode.separates]
  rfl

private def vertexTests (A : Adjacency n) (P : Vector (Edge n) m) (mask : Flags n) : Fin m → Bool × ℕ :=
  let marked := RationalVertexSparsityCode.indicator mask
  fun i => MeasuredFreeResources.vertexTest A marked (P.get i)

private theorem vertexCount_value (A : Adjacency n) (P : Vector (Edge n) m) (mask : Flags n) :
    (resourceCount (vertexTests A P mask)).1 = RationalVertexSparsityCode.count A P mask := by
  rw [counted]
  simp only [vertexTests,MeasuredFreeResources.vertexTest_value,RationalVertexSparsityCode.count]
  rfl

private def markedCosts (prices : RawRow r) (marked : Fin r → Bool) : List Code :=
  List.ofFn fun i => if marked i then get prices i else Code.zero

private theorem markedCosts_fits (prices : RawRow r) (marked : Fin r → Bool) {B : ℕ} (fit : RowBounded prices B) :
    ∀ q ∈ markedCosts prices marked, q.Bounded B := by
  intro q found
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp found
  split
  · exact fit i
  · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)

private def edgePrice (A : Adjacency n) (c : Weights n) (mask : Mask n) : Code × ℕ :=
  let prices := MeasuredGraphPlanTotals.arcValues A c
  let subtotal := sum (markedCosts prices.1 (fun i => flag mask (edge i)))
  (subtotal.1,prices.2+subtotal.2)

private theorem edgePrice_value (A : Adjacency n) (c : Weights n) (mask : Mask n) :
    (edgePrice A c mask).1.value = RationalEdgeSparsityCode.cutPrice A c mask := by
  apply NNRat.coe_injective
  let prices := (MeasuredGraphPlanTotals.arcValues A c).1
  change rational (sum (markedCosts prices (fun i => flag mask (edge i)))).1 = _
  rw [sum_value,FractionalCoverRawCore.rational_sum]
  simp only [markedCosts,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  let price (i : Resource n) := rational (if flag mask (edge i) then get prices i else Code.zero)
  change (∑ i, price i) = _
  rw [← (finProdFinEquiv : Edge n ≃ Resource n).sum_comp price]
  change (∑ e : Edge n, price (resource e)) = _
  simp only [RationalEdgeSparsityCode.cutPrice,NNRat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases marked : flag mask e = true
  · simpa only [price,ConcurrentEdgeOracle.edge_resource,ite_eq_left marked,← FractionalCoverRawCore.decode_value]
      using MeasuredGraphPlanTotals.arcValues_value A c e
  · simp only [price,ConcurrentEdgeOracle.edge_resource,ite_eq_right marked,FractionalCoverRawCore.rational_zero,
      NNRat.cast_zero]

def edgePriceWidth (n B : ℕ) : ℕ := n*n*(B+1)

private def edgePriceWork (n B : ℕ) : ℕ :=
  n*n*(40*(B+1)^2)+n*n*BinaryRawRational.budget (edgePriceWidth n B)

private theorem edgePrice_bounds (A : Adjacency n) (c : Weights n) (mask : Mask n)
    {B : ℕ} (fit : MatrixFits c B) :
    (edgePrice A c mask).1.Bounded (edgePriceWidth n B) ∧ (edgePrice A c mask).2 ≤ edgePriceWork n B := by
  obtain ⟨rows,read⟩ := MeasuredGraphPlanTotals.arcValues_bounds A c fit
  let input := markedCosts (MeasuredGraphPlanTotals.arcValues A c).1 (fun i => flag mask (edge i))
  have fields : ∀ q ∈ input, q.Bounded B :=
    markedCosts_fits (MeasuredGraphPlanTotals.arcValues A c).1 (fun i => flag mask (edge i)) rows
  have len : input.length = n*n := List.length_ofFn
  have summed := sum_charge input fields len.le
  have bounded := FractionalCoverRawCore.sumCodes_bounded input B fields
  rw [len] at bounded summed
  exact ⟨by simpa only [edgePrice,input,sum_value,edgePriceWidth] using bounded,
    Nat.add_le_add read summed⟩

private def vertexPrice (c : BinaryFractionalRows.Row n) (mask : Flags n) : Code × ℕ :=
  let packed := BinaryCutPriceSelection.maskScore c mask
  let price := BinaryRawRational.decode packed.1
  (price.1,packed.2+price.2)

private theorem vertexPrice_value (c : BinaryFractionalRows.Row n) (mask : Flags n) :
    (vertexPrice c mask).1 = EncodedCutSelection.maskCost (c.map BinaryRational.decode) mask := by
  have decoded : BinaryFractionalRows.decodeRow c = c.map BinaryRational.decode := by
    ext i
    simp only [BinaryFractionalRows.decodeRow,BinaryFractionalRows.get,Vector.getElem_ofFn,Vector.getElem_map]
  simp only [vertexPrice,BinaryRawRational.decode_value,BinaryCutPriceSelection.maskScore_decodes,decoded]

def vertexPriceWidth (n B : ℕ) : ℕ := n*(max 1 B+1)+1

private def vertexPriceWork (n B : ℕ) : ℕ :=
  BinaryFractionalRows.sumBound n (max 1 B)+40*(vertexPriceWidth n B+1)^2

private theorem vertexPrice_bounds (c : BinaryFractionalRows.Row n) (mask : Flags n)
    {B : ℕ} (fit : ∀ j, StoredBounded (c.get j) B) :
    (vertexPrice c mask).1.Bounded (vertexPriceWidth n B) ∧ (vertexPrice c mask).2 ≤ vertexPriceWork n B := by
  obtain ⟨width,paid⟩ := BinaryCutPriceSelection.maskScore_charge c mask (le_max_left 1 B) (fun i =>
    BinaryFractionalWalkBounds.stored_mono (fit i) (le_max_right 1 B))
  exact ⟨by simpa only [vertexPrice,BinaryRawRational.decode_value,vertexPriceWidth]
      using BinaryFractionalRows.stored_raw_bound width,
    Nat.add_le_add paid (BinaryRawRational.decode_paid width)⟩

private def ratio (price : Code × ℕ) (count : ℕ × ℕ) : Code × ℕ :=
  let q := BinaryRawRational.div price.1 (Code.ofNat count.1)
  (q.1,price.2+count.2+q.2)

private theorem ratio_bounds (price : Code × ℕ) (count : ℕ × ℕ) {B m : ℕ}
    (priceFit : price.1.Bounded B) (countFit : count.1 ≤ m) :
    (ratio price count).1.Bounded (B+m.size) ∧
      (ratio price count).2 ≤ price.2+count.2+BinaryRawRational.budget (max B m.size) := by
  have countWidth : (Code.ofNat count.1).Bounded m.size :=
    BinaryNaturalOperations.ofNat_fit (Nat.size_le_size countFit)
  constructor
  · simp only [ratio,BinaryRawRational.div_value]
    exact Code.bounded_div priceFit countWidth
  · exact Nat.add_le_add_left (BinaryRawRational.div_paid
      (Code.bounded_mono priceFit (le_max_left ..)) (Code.bounded_mono countWidth (le_max_right ..))) _

def edgeScore (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (mask : Mask n) : Code × ℕ :=
  let raw := ratio (edgePrice A c mask) (resourceCount (edgeTests A c P mask))
  let canonical := BinaryRationalNormalize.normalize raw.1
  (canonical.1,raw.2+canonical.2)

theorem edgeScore_value (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (mask : Mask n) :
    (edgeScore A c P mask).1 = RationalEdgeSparsityCode.score A c P mask := by
  simp only [edgeScore,ratio,BinaryRationalNormalize.normalize_value,BinaryRawRational.div_value,Code.value_div,
    Code.value_ofNat,edgePrice_value,edgeCount_value,RationalEdgeSparsityCode.score]

def edgeWork (n m B : ℕ) : ℕ :=
  edgePriceWork n B+rowWork m (MeasuredSparsestDistances.edgeWork n B+1)+
    BinaryRawRational.budget (max (edgePriceWidth n B) m.size)+
    BinaryRationalNormalize.budget (edgePriceWidth n B+m.size)

attribute [local irreducible] MeasuredGraphPlanTotals.arcValues MeasuredPathColumn.resourceCount
  MeasuredSparsestDistances.edge BinaryRationalNormalize.normalize in
theorem edgeScore_bounds (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (mask : Mask n)
    {B : ℕ} (fit : MatrixFits c B) :
    (edgeScore A c P mask).1.Bounded (edgePriceWidth n B+m.size) ∧ (edgeScore A c P mask).2 ≤ edgeWork n m B := by
  let tests := edgeTests A c P mask
  obtain ⟨price,paid⟩ := edgePrice_bounds A c mask fit
  have counts : (resourceCount tests).2 ≤ rowWork m (MeasuredSparsestDistances.edgeWork n B+1) := by
    apply resourceCount_charge
    intro i
    exact Nat.add_le_add_right
      (MeasuredSparsestDistances.edge_bounds (RationalEdgeSparsityCode.without A mask) c (P.get i) fit).2 1
  obtain ⟨raw,compare⟩ := ratio_bounds (edgePrice A c mask) (resourceCount tests) price (resourceCount_le tests)
  let scored := ratio (edgePrice A c mask) (resourceCount tests)
  change (BinaryRationalNormalize.normalize scored.1).1.Bounded _ ∧
    scored.2+(BinaryRationalNormalize.normalize scored.1).2 ≤ edgeWork n m B
  refine ⟨BinaryRationalNormalize.normalize_width raw,Nat.add_le_add ?_ (BinaryRationalNormalize.normalize_paid raw)⟩
  exact compare.trans (Nat.add_le_add_right (Nat.add_le_add paid counts) _)

def vertexScore (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (mask : Flags n) : Code × ℕ :=
  ratio (vertexPrice c mask) (resourceCount (vertexTests A P mask))

theorem vertexScore_value (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (mask : Flags n) :
    (vertexScore A c P mask).1 = RationalVertexSparsityCode.score A c P mask := by
  simp only [vertexScore,ratio,BinaryRawRational.div_value,vertexPrice_value,vertexCount_value,
    RationalVertexSparsityCode.score]

def vertexWork (n m B : ℕ) : ℕ :=
  vertexPriceWork n B+rowWork m (MeasuredFreeResources.vertexTestWork n)+
    BinaryRawRational.budget (max (vertexPriceWidth n B) m.size)

attribute [local irreducible] MeasuredPathColumn.resourceCount MeasuredFreeResources.vertexTest in
theorem vertexScore_bounds (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (mask : Flags n) {B : ℕ} (fit : ∀ i, StoredBounded (c.get i) B) :
    (vertexScore A c P mask).1.Bounded (vertexPriceWidth n B+m.size) ∧
      (vertexScore A c P mask).2 ≤ vertexWork n m B := by
  let tests := vertexTests A P mask
  obtain ⟨price,paid⟩ := vertexPrice_bounds c mask fit
  have counts : (resourceCount tests).2 ≤ rowWork m (MeasuredFreeResources.vertexTestWork n) :=
    resourceCount_charge tests (fun i => MeasuredFreeResources.vertexTest_charge A mask (P.get i))
  obtain ⟨raw,compare⟩ := ratio_bounds (vertexPrice c mask) (resourceCount tests) price (resourceCount_le tests)
  exact ⟨raw,compare.trans (Nat.add_le_add_right (Nat.add_le_add paid counts) _)⟩

end DirectedFlowCutGap.MeasuredCutSparsity
