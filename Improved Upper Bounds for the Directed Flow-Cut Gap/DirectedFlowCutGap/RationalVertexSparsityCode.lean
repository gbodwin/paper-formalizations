import DirectedFlowCutGap.RationalSparsestVertexRound
import DirectedFlowCutGap.EncodedCutSelection

/-! Score an original vertex mask by rational price per separated demand.
Unit lengths on the selected vertices make separation an exact endpoint-safe
distance test. -/
namespace DirectedFlowCutGap.RationalVertexSparsityCode

open scoped NNReal NNRat ENNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open RetainedGridState (Flags)
open RationalSparsestVertexDistances (weights distance)
open EncodedUnitCostReplication (selectedSet)
open RationalSparsestEdgeRound (demandSet)
open RawNonnegativeRational (Code)

variable {m n : ℕ}

def indicator (mask : Flags n) : Row n :=
  mask.map fun flag => if flag then BinaryRational.one else BinaryRational.zero

private theorem indicator_eq (mask : Flags n) (v : Fin n) :
    weights (indicator mask) v = if v ∈ selectedSet mask then 1 else 0 := by
  by_cases selected : mask[v.val] = true <;>
    simp [weights,indicator,selected,selectedSet,RawNonnegativeRational.Code.value_one,
      RawNonnegativeRational.Code.value_zero]

theorem cuts_iff (A : Adjacency n) (mask : Flags n) (d : Fin n × Fin n) :
    (1 : ℝ≥0∞) ≤ vertexDistance (graph A) (weights (indicator mask)) d.1 d.2 ↔
      CutsPair (graph A) (selectedSet mask) d.1 d.2 := by
  rw [← ENNReal.coe_one, coe_le_vertexDistance_iff]
  constructor
  · intro all p
    by_contra absent
    have zero : p.weight (weights (indicator mask)) = 0 := by
      apply Finset.sum_eq_zero
      intro v inside
      rw [indicator_eq,ite_eq_right (fun marked => absent ⟨v,inside,marked⟩)]
    have fit := all p
    rw [zero] at fit
    exact (not_le_of_gt zero_lt_one) fit
  · intro cut p
    obtain ⟨v,inside,marked⟩ := cut p
    have low := Finset.single_le_sum (f := weights (indicator mask)) (fun _ _ => zero_le) inside
    rw [indicator_eq,ite_eq_left marked] at low
    exact low

def separates (A : Adjacency n) (mask : Flags n) (d : Fin n × Fin n) : Bool :=
  decide (1 ≤ (distance A (indicator mask) d).getD 1)

theorem separates_eq (A : Adjacency n) (mask : Flags n) (d : Fin n × Fin n) :
    separates A mask d = true ↔ CutsPair (graph A) (selectedSet mask) d.1 d.2 := by
  rw [← cuts_iff]
  have real := RationalSparsestVertexDistances.distance_exact A (indicator mask) d
  cases found : distance A (indicator mask) d with
  | none => simp only [separates,found,Option.getD_none,le_refl,decide_true,
      RationalSparsestEdgeDistances.observe] at real ⊢
            rw [← real]
            simp
  | some q =>
    rw [found] at real
    simp only [separates,found,Option.getD_some,decide_eq_true_eq,← real,RationalSparsestEdgeDistances.observe]
    rw [← ENNReal.coe_one, ENNReal.coe_le_coe]
    have compare : (((1 : ℚ≥0) : ℝ≥0) ≤ (q : ℝ≥0)) ↔ (1 : ℚ≥0) ≤ q :=
      NNRat.cast_le (K := ℝ≥0)
    simpa only [NNRat.cast_one] using compare.symm

def count (A : Adjacency n) (P : Vector (Fin n × Fin n) m) (mask : Flags n) : ℕ :=
  (Finset.univ.filter fun j : Fin m => separates A mask P[j.val]).card

theorem count_eq (A : Adjacency n) (P : Vector (Fin n × Fin n) m) (mask : Flags n)
    (distinct : Function.Injective fun j : Fin m => P[j.val]) :
    count A P mask = (SparsestVertexBridge.separated (graph A) (demandSet P) (selectedSet mask)).card := by
  classical
  let includePair (j : Fin m) : demandSet P := ⟨P[j.val],Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  have injective : Function.Injective includePair := fun _ _ same => distinct (congrArg Subtype.val same)
  let indexed := Finset.univ.filter fun j : Fin m => separates A mask P[j.val]
  have eq : indexed.image includePair = SparsestVertexBridge.separated (graph A) (demandSet P) (selectedSet mask) := by
    ext d
    simp only [Finset.mem_image,SparsestVertexBridge.separated,Finset.mem_filter,Finset.mem_univ,
      true_and,indexed,separates_eq]
    constructor
    · rintro ⟨j,separated,rfl⟩
      exact separated
    · intro separated
      obtain ⟨j,_,shown⟩ := Finset.mem_image.mp d.property
      have eq : includePair j = d := Subtype.ext shown
      exact ⟨j,by rw [← eq] at separated; exact separated,eq⟩
  rw [← eq,Finset.card_image_of_injective _ injective]
  rfl

def score (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m) (mask : Flags n) : Code :=
  (EncodedCutSelection.maskCost (c.map BinaryRational.decode) mask).div (Code.ofNat (count A P mask))

theorem score_eq (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m) (mask : Flags n)
    (distinct : Function.Injective fun j : Fin m => P[j.val]) :
    (score A c P mask).realValue = SparsestVertexBridge.sparsity (graph A) (weights c) (demandSet P)
      (selectedSet mask) := by
  have price := EncodedCutSelection.maskCost_value (c.map BinaryRational.decode) mask
  have values : (fun i => (FractionalCoverRawCore.get (c.map BinaryRational.decode) i).realValue) = weights c := by
    funext v
    simp only [FractionalCoverRawCore.get,Vector.getElem_map,weights,Code.realValue]
  rw [values] at price
  simp only [Code.realValue,score,Code.value_div,Code.value_ofNat,NNRat.cast_div,NNRat.cast_natCast,
    count_eq A P mask distinct,SparsestVertexBridge.sparsity]
  exact congrArg (fun q : ℝ≥0 => q / _) price

end DirectedFlowCutGap.RationalVertexSparsityCode
