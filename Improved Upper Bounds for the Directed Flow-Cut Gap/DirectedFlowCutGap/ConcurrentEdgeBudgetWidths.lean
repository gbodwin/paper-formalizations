import DirectedFlowCutGap.ConcurrentEdgeCoverWidths
import DirectedFlowCutGap.ConcurrentEdgeBudgetRound

/-! Bound the number and canonical widths of price and mass guesses
generated from the binary input, and the encoded lengths actually
retained by the candidate selector. -/
namespace DirectedFlowCutGap.ConcurrentEdgeBudgetWidths

open scoped BigOperators NNRat
open BinaryFractionalWalkOracle (Adjacency)
open RationalEdgeThresholds (Weights)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeBudgetGrid (grid gridSteps pairs costCeiling massCeiling)
open ConcurrentEdgeCoverWidths (MatrixFits rawPrice_fits outputWidth budget_solve_fits)
open NNRatStoredBounds (Bounded mono value_bounded one_bounded mul_bounded div_bounded sum_bounded)
open RawNonnegativeRational (Code)

variable {m n : ℕ}

private theorem nat_fits {v B : ℕ} (h : v ≤ 2^B) : Bounded (v : ℚ≥0) B := by
  have raw : (Code.ofNat v).Bounded B := ⟨h,Nat.one_le_pow _ _ (by decide)⟩
  simpa only [Code.value_ofNat] using value_bounded raw

private theorem product_fits {ι : Type*} (s : Finset ι) (f : ι → ℚ≥0) (B : ℕ)
    (bound : ∀ e ∈ s, Bounded (f e) B) : Bounded (∏ e ∈ s, f e) (s.card*B) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.card_empty,Nat.zero_mul] using one_bounded
  | @insert e s outside ih =>
    rw [Finset.card_insert_of_notMem outside,Finset.prod_insert outside]
    have one := bound e (Finset.mem_insert_self ..)
    have rest := ih (fun a ha => bound a (Finset.mem_insert_of_mem ha))
    convert mul_bounded one rest using 1
    ring

theorem steps_le (lo hi : ℚ≥0) {L H : ℕ} (left : Bounded lo L) (right : Bounded hi H) :
    gridSteps lo hi ≤ L+H+1 := by
  have h : (hi/lo).num ≤ 2^(H+L) := (div_bounded right left).1
  unfold gridSteps
  exact (Nat.size_le_size h).trans_eq (by rw [Nat.size_pow,Nat.add_comm H L])

theorem grid_length (lo hi : ℚ≥0) {L H : ℕ} (left : Bounded lo L) (right : Bounded hi H) :
    (grid lo hi).length ≤ L+H+3 := by
  have h := steps_le lo hi left right
  simp only [grid,List.length_map,List.length_range]
  omega

theorem grid_item (lo hi : ℚ≥0) {L H : ℕ} (left : Bounded lo L) (right : Bounded hi H)
    {b : ℚ≥0} (present : b ∈ grid lo hi) : Bounded b (2*L+H+2) := by
  obtain ⟨j,inside,rfl⟩ := List.mem_map.mp present
  have small := List.mem_range.mp inside
  have h := steps_le lo hi left right
  have two : Bounded (2 : ℚ≥0) 1 := nat_fits (v := 2) (B := 1) (by decide)
  have p := NNRatStoredBounds.pow_bounded two j
  exact mono (mul_bounded left p) (by omega)

theorem floor_fits (c : Weights n) {B : ℕ} (fit : MatrixFits c B) :
    Bounded (ConcurrentEdgeCappedPrices.floorPrice c) (n*n*B) := by
  have part (e : Edge n) : Bounded (ConcurrentEdgeCappedPrices.floorFactor c e) B := by
    have one := mono one_bounded (Nat.zero_le B)
    unfold ConcurrentEdgeCappedPrices.floorFactor
    split
    · rcases le_total (1 : ℚ≥0) (ConcurrentEdgeZeroPrices.rawPrice c e) with lower | upper
      · rwa [min_eq_left lower]
      · rw [min_eq_right upper]
        exact rawPrice_fits c fit e
    · exact one
  unfold ConcurrentEdgeCappedPrices.floorPrice
  simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using
    product_fits Finset.univ _ B (fun e _ => part e)

private theorem arc_fits (A : Adjacency n) (c : Weights n) {B : ℕ} (fit : MatrixFits c B) (e : Edge n) :
    Bounded (RationalEdgeDecomposition.originalWeight A c e) B := by
  rcases e with ⟨u,v⟩
  unfold RationalEdgeDecomposition.originalWeight
  split
  · exact rawPrice_fits c fit (u,v)
  · exact mono NNRatStoredBounds.zero_bounded (Nat.zero_le B)

theorem costCeiling_fits (A : Adjacency n) (c : Weights n) (m : ℕ) {B : ℕ} (fit : MatrixFits c B) :
    Bounded (costCeiling A c m) (m+n*n*(B+1)) := by
  have subtotal : Bounded (RationalEdgeDecomposition.originalTotal A c) (n*n*(B+1)) := by
    simpa only [RationalEdgeDecomposition.originalTotal,Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using
      sum_bounded (Finset.univ : Finset (Edge n)) _ B (fun e _ => arc_fits A c fit e)
  exact mul_bounded (nat_fits (v := m) (B := m) Nat.lt_two_pow_self.le) subtotal

theorem massCeiling_fits (n m : ℕ) : Bounded (massCeiling n m) (m+n*2) :=
  mul_bounded (nat_fits (v := m) (B := m) Nat.lt_two_pow_self.le)
    (NNRatStoredBounds.pow_bounded (nat_fits (v := n) (B := n) Nat.lt_two_pow_self.le) 2)

def priceWidth (n m B : ℕ) : ℕ := 2*(n*n*B)+(m+n*n*(B+1))+2
def massWidth (n m : ℕ) : ℕ := m+n*2+2

theorem pair_fits (A : Adjacency n) (c : Weights n) (m : ℕ) {L : ℕ} (input : MatrixFits c L)
    {B U : ℚ≥0} (present : (B,U) ∈ pairs A c m) :
    Bounded B (priceWidth n m L) ∧ Bounded U (massWidth n m) := by
  obtain ⟨b,fee,part⟩ := List.mem_flatMap.mp present
  obtain ⟨u,mass,equal⟩ := List.mem_map.mp part
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
  have b := grid_item _ _ (floor_fits c input) (costCeiling_fits A c m input) fee
  have u := grid_item _ _ one_bounded (massCeiling_fits n m) mass
  exact ⟨b,by simpa only [massWidth,Nat.mul_zero,Nat.zero_add] using u⟩

theorem pair_count (A : Adjacency n) (c : Weights n) (m : ℕ) {L : ℕ} (input : MatrixFits c L) :
    (pairs A c m).length ≤ (n*n*L+(m+n*n*(L+1))+3)*(m+n*2+3) := by
  have B := grid_length _ _ (floor_fits c input) (costCeiling_fits A c m input)
  have U := grid_length _ _ one_bounded (massCeiling_fits n m)
  simp only [Nat.zero_add] at U
  unfold pairs
  simp only [List.length_flatMap,List.length_map,List.map_const',List.sum_replicate,nsmul_eq_mul]
  exact Nat.mul_le_mul B U

def candidateWidth (n m L : ℕ) : ℕ :=
  outputWidth n m (L+priceWidth n m L+massWidth n m+2)

theorem candidate_fits (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {L : ℕ} (input : MatrixFits c L) {z : Weights n}
    (found : z ∈ ConcurrentEdgeBudgetGrid.candidates hn A c P) : MatrixFits z (candidateWidth n m L) := by
  obtain ⟨⟨B,U⟩,present,rfl⟩ := List.mem_map.mp found
  obtain ⟨fee,mass⟩ := pair_fits A c m input present
  exact budget_solve_fits hn A c P B U input fee mass

theorem selected_fits (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {L : ℕ} (input : MatrixFits c L) {p : ConcurrentEdgeBudgetSelection.Plan n}
    (found : ConcurrentEdgeBudgetSelection.choose hn A c P = some p) :
    MatrixFits p.lengths (candidateWidth n m L) := by
  obtain ⟨z,member,rfl⟩ := ConcurrentEdgeBudgetSelection.chosen_member hn A c P found
  rw [ConcurrentEdgeBudgetSelection.plan_lengths]
  exact candidate_fits hn A c P input member

private theorem harmonic_fits (m : ℕ) :
    Bounded (NormalizedOptimalMode.harmonic m) (m*(m+1)) := by
  unfold NormalizedOptimalMode.harmonic
  have each (j : Fin m) : Bounded (1/((j.val+1 : ℕ) : ℚ≥0)) m := by
    have denominator : j.val+1 ≤ 2^m := (Nat.succ_le_of_lt j.isLt).trans Nat.lt_two_pow_self.le
    simpa only [Nat.zero_add] using div_bounded one_bounded (nat_fits denominator)
  simpa only [Finset.card_univ,Fintype.card_fin] using
    sum_bounded (Finset.univ : Finset (Fin m)) _ m (fun j _ => each j)

theorem rawCost_fits (A : Adjacency n) (c z : Weights n) {B W : ℕ}
    (input : MatrixFits c B) (lengths : MatrixFits z W) :
    Bounded (ConcurrentEdgeBudgetSelection.rawCost A c z) (n*n*(B+W+1)) := by
  unfold ConcurrentEdgeBudgetSelection.rawCost
  simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using
    sum_bounded (Finset.univ : Finset (Edge n)) _ (B+W)
      (fun e _ => mul_bounded (arc_fits A c input e) (arc_fits A z lengths e))

theorem mass_fits (A : Adjacency n) (z : Weights n) {W : ℕ} (lengths : MatrixFits z W) :
    Bounded (RationalEdgeDecomposition.originalTotal A z) (n*n*(W+1)) := by
  unfold RationalEdgeDecomposition.originalTotal
  simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using
    sum_bounded (Finset.univ : Finset (Edge n)) _ W (fun e _ => arc_fits A z lengths e)

def receiptWidth (n m B W : ℕ) : ℕ :=
  (n*n*(B+W+1)+m)*6 + (n*2+9*(m*(m+1))+3*(n*n*(W+1)))

theorem score_fits (A : Adjacency n) (c z : Weights n) (m : ℕ) {B W : ℕ}
    (input : MatrixFits c B) (lengths : MatrixFits z W) (mode : ChargedVertexModes.Mode) :
    Bounded (ConcurrentEdgeBudgetSelection.score n m (ConcurrentEdgeBudgetSelection.rawCost A c z)
      (RationalEdgeDecomposition.originalTotal A z) mode) (receiptWidth n m B W) := by
  let H := m*(m+1)
  let F := (n*n*(B+W+1)+m)*6
  have fee := NNRatStoredBounds.pow_bounded
    (div_bounded (rawCost_fits A c z input lengths) (nat_fits (v := m) (B := m) Nat.lt_two_pow_self.le)) 6
  have harmonics : Bounded (NormalizedOptimalMode.harmonic m) H := harmonic_fits m
  unfold ConcurrentEdgeBudgetSelection.score
  cases mode with
  | mass =>
    have bounds := mul_bounded fee (mul_bounded (NNRatStoredBounds.pow_bounded harmonics 9)
      (NNRatStoredBounds.pow_bounded (mass_fits A z lengths) 3))
    apply mono bounds
    change F+(H*9+(n*n*(W+1))*3) ≤ F+(n*2+9*H+3*(n*n*(W+1)))
    rw [Nat.mul_comm H 9,Nat.mul_comm (n*n*(W+1)) 3]
    omega
  | size =>
    have bounds := mul_bounded fee (mul_bounded
      (NNRatStoredBounds.pow_bounded (nat_fits (v := n) (B := n) Nat.lt_two_pow_self.le) 2)
      (NNRatStoredBounds.pow_bounded harmonics 6))
    apply mono bounds
    change F+(n*2+H*6) ≤ F+(n*2+9*H+3*(n*n*(W+1)))
    rw [Nat.mul_comm H 6]
    omega

theorem selected_receipt_fits (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {L : ℕ} (input : MatrixFits c L) {p : ConcurrentEdgeBudgetSelection.Plan n}
    (found : ConcurrentEdgeBudgetSelection.choose hn A c P = some p) :
    Bounded p.receipt (receiptWidth n m L (candidateWidth n m L)) := by
  have fit := selected_fits hn A c P input found
  obtain ⟨z,_,rfl⟩ := ConcurrentEdgeBudgetSelection.chosen_member hn A c P found
  rw [ConcurrentEdgeBudgetSelection.plan_lengths] at fit
  rw [ConcurrentEdgeBudgetSelection.plan_receipt]
  exact score_fits A c z m input fit _

end DirectedFlowCutGap.ConcurrentEdgeBudgetWidths
