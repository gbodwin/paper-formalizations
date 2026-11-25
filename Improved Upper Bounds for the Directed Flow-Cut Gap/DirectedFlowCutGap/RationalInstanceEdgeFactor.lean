import DirectedFlowCutGap.RationalExactEdgeOracle
import DirectedFlowCutGap.RationalFourierMotzkin
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-! Compute the least integer rounding factor of one rational instance.
The feasibility system describes nonnegative prices under which every valid
cut exceeds the proposed bound by at least one. A violating price vector can
always be scaled to satisfy that normalization because the cut list is finite. -/
namespace DirectedFlowCutGap.RationalInstanceEdgeFactor

open scoped NNRat NNReal BigOperators
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights demands weights)
open RationalEdgeDecomposition (Good originalWeight originalWeight_eq)
open RationalExactEdgeOracle (Edge candidates mem_candidates)
open RationalFourierMotzkin (Row Satisfies solve)

private def index (n : ℕ) : Edge n ≃ Fin (n*n) := finProdFinEquiv

private def nonnegative {m : ℕ} (i : Fin m) : Row m := ⟨fun j => if j=i then 1 else 0,0⟩

private def violation {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) (X : Finset (Edge n)) :
    Row (n*n) :=
  ⟨fun i =>
    let e := (index n).symm i
    (if e ∈ X then 1 else 0)-(k : ℚ)*(originalWeight A w e : ℚ),-1⟩

private def constraints {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) : List (Row (n*n)) :=
  (List.finRange (n*n)).map nonnegative ++ ((candidates A (demands A w) ∅).map (violation A w k))

private theorem nonnegative_eval {m : ℕ} (i : Fin m) (x : Fin m → ℝ) :
    (nonnegative i).eval x=x i := by
  simp [Row.eval,nonnegative,apply_ite,ite_mul]

private theorem originalWeight_cast {n : ℕ} (A : Adjacency n) (w : Weights n) (e : Edge n) :
    ((originalWeight A w e : ℚ) : ℝ) = (actualEdgeWeight (graph A) (weights w) e : ℝ) := by
  rw [← congrArg (fun t : ℝ≥0 => (t : ℝ)) (originalWeight_eq A w e)]
  exact map_nnratCast (Rat.castHom ℝ) (originalWeight A w e)

private noncomputable def gap {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) (X : Finset (Edge n))
    (c : Edge n → ℝ) : ℝ :=
  (∑ e ∈ X, c e)-(k : ℝ)*mwPotential (fun e => (actualEdgeWeight (graph A) (weights w) e : ℝ)) c

private theorem violation_eval {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) (X : Finset (Edge n))
    (x : Fin (n*n) → ℝ) : (violation A w k X).eval x=gap A w k X (fun e => x (index n e))-1 := by
  unfold Row.eval violation
  simp only [Rat.cast_neg,Rat.cast_one,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,apply_ite,
    Rat.cast_zero,originalWeight_cast]
  let f (e : Edge n) := ((if e ∈ X then 1 else 0)-(k : ℝ)*
    (actualEdgeWeight (graph A) (weights w) e : ℝ))*x (index n e)
  have reindexed : (∑ i : Fin (n*n), f ((index n).symm i))=∑ e, f e :=
    Fintype.sum_equiv (index n).symm _ _ fun _ => rfl
  simp only [f,Equiv.apply_symm_apply] at reindexed
  rw [reindexed]
  simp only [gap,mwPotential,sub_mul,Finset.sum_sub_distrib,ite_mul,one_mul,zero_mul,mul_assoc,
    ← Finset.mul_sum,← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  rw [show (∑ e, (actualEdgeWeight (graph A) (weights w) e : ℝ)*x (index n e))=
    ∑ e, x (index n e)*(actualEdgeWeight (graph A) (weights w) e : ℝ) from
      Finset.sum_congr rfl (fun _ _ => mul_comm ..)]
  ring

private theorem listed_iff {n : ℕ} (A : Adjacency n) (w : Weights n) (X : Finset (Edge n)) :
    X ∈ candidates A (demands A w) ∅ ↔
      X ⊆ graphEdges (graph A) ∧ IsIntegralEdgeCut (graph A) X (edgeThresholdDemands (graph A) (weights w)) := by
  have demandSet : {e | e ∈ demands A w}=edgeThresholdDemands (graph A) (weights w) := by
    ext e
    exact RationalEdgeThresholds.demands_iff A w e
  rw [mem_candidates,demandSet]
  simp

private theorem constraints_iff {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) (x : Fin (n*n) → ℝ) :
    Satisfies (constraints A w k) x ↔
      (∀ i, 0≤x i) ∧ ∀ X ∈ candidates A (demands A w) ∅, 1≤gap A w k X (fun e => x (index n e)) := by
  constructor
  · intro holds
    refine ⟨fun i => ?_,fun X hX => ?_⟩
    · have row := holds (nonnegative i) (List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
      rwa [nonnegative_eval] at row
    · have row := holds (violation A w k X) (List.mem_append_right _ (List.mem_map.mpr ⟨X,hX,rfl⟩))
      rwa [violation_eval,sub_nonneg] at row
  · rintro ⟨pos,gaps⟩ r mem
    simp only [constraints,List.mem_append,List.mem_map] at mem
    rcases mem with ⟨i,_,rfl⟩ | ⟨X,hX,rfl⟩
    · rw [nonnegative_eval]
      exact pos i
    · rw [violation_eval,sub_nonneg]
      exact gaps X hX

private theorem positive_floor {T : Type*} (items : List T) (f : T → ℝ)
    (positive : ∀ x ∈ items, 0<f x) : ∃ d : ℝ, 0<d ∧ ∀ x ∈ items, d≤f x := by
  induction items with
  | nil => exact ⟨1,one_pos,fun x h => (List.not_mem_nil h).elim⟩
  | cons a items ih =>
    obtain ⟨d,hd,less⟩ := ih (fun x hx => positive x (List.mem_cons_of_mem a hx))
    refine ⟨min (f a) d,lt_min (positive a List.mem_cons_self) hd,fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact min_le_left ..
    · exact (min_le_right _ _).trans (less x hx)

private theorem gap_scale {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) (X : Finset (Edge n))
    (c : Edge n → ℝ) (a : ℝ) : gap A w k X (fun e => a*c e)=a*gap A w k X c := by
  simp only [gap,mwPotential,← Finset.mul_sum]
  rw [show (∑ e, (a*c e)*(actualEdgeWeight (graph A) (weights w) e : ℝ)) =
    a*∑ e, c e*(actualEdgeWeight (graph A) (weights w) e : ℝ) by
      simp only [mul_assoc,Finset.mul_sum]]
  ring

private theorem no_price_of_factor {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ)
    (factor : HasEdgeRoundingFactor (graph A) (weights w) (k : ℝ)) (x : Fin (n*n) → ℝ) :
    ¬ Satisfies (constraints A w k) x := by
  intro h
  obtain ⟨nonneg,fails⟩ := (constraints_iff A w k x).mp h
  let c (e : Edge n) := x (index n e)
  obtain ⟨X,good,within⟩ := factor.real_cost_round c (fun e => nonneg _)
  have step := fails X ((listed_iff A w X).mpr good)
  change 1≤gap A w k X c at step
  dsimp only [gap] at step
  linarith only [step,within]

private theorem price_of_not_factor {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ)
    (failure : ¬ HasEdgeRoundingFactor (graph A) (weights w) (k : ℝ)) :
    ∃ x : Fin (n*n) → ℝ, Satisfies (constraints A w k) x := by
  classical
  let G := graph A
  let weight := weights w
  have noRound : ¬ ∀ c : Edge n → ℝ≥0, ∃ X : Finset (Edge n), X ⊆ graphEdges G ∧
    IsIntegralEdgeCut G X (edgeThresholdDemands G weight) ∧
    (edgeCutCost G c X : ℝ) ≤ (k : ℝ)*(weightedEdgeCost G c weight : ℝ) :=
    fun h => failure ⟨Nat.cast_nonneg _,h⟩
  obtain ⟨c,noCut⟩ := not_forall.mp noRound
  let price (e : Edge n) : ℝ := c e
  have positive (X : Finset (Edge n)) (hX : X ∈ candidates A (demands A w) ∅) :
      0<gap A w k X price := by
    obtain ⟨edges,valid⟩ := (listed_iff A w X).mp hX
    have fails := not_le.mp (fun paid => noCut ⟨X,edges,valid,paid⟩)
    rw [edgeCutCost_eq_sum_of_subset G c edges,NNReal.coe_sum,coe_weightedEdgeCost_eq_mwPotential] at fails
    exact sub_pos.mpr fails
  obtain ⟨d,hd,floor⟩ := positive_floor (candidates A (demands A w) ∅) (fun X => gap A w k X price) positive
  let x (i : Fin (n*n)) : ℝ := d⁻¹*price ((index n).symm i)
  refine ⟨x,(constraints_iff A w k x).mpr ⟨fun i => mul_nonneg (inv_nonneg.mpr hd.le) (c _).coe_nonneg,?_⟩⟩
  intro X hX
  simp only [x,Equiv.symm_apply_apply,gap_scale]
  calc
    1=d⁻¹*d := (inv_mul_cancel₀ hd.ne').symm
    _≤d⁻¹*gap A w k X price := mul_le_mul_of_nonneg_left (floor X hX) (inv_nonneg.mpr hd.le)

/-- If the factor fails, return an exact rational vector of violating prices. -/
def counterprice {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) : Option (Fin (n*n) → ℚ) :=
  solve (n*n) (constraints A w k)

theorem counterprice_spec {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ)
    (x : Fin (n*n) → ℚ) (h : counterprice A w k=some x) :
    (∀ i, 0≤(x i : ℝ)) ∧ ∀ X ∈ candidates A (demands A w) ∅,
      1≤gap A w k X (fun e => (x (index n e) : ℝ)) :=
  (constraints_iff A w k _).mp (RationalFourierMotzkin.rational_to_real _ x
    (RationalFourierMotzkin.solve_sound _ x h))

theorem counterprice_none_iff {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) :
    counterprice A w k=none ↔ HasEdgeRoundingFactor (graph A) (weights w) (k : ℝ) := by
  constructor
  · intro h
    by_contra bad
    obtain ⟨x,hx⟩ := price_of_not_factor A w k bad
    have solved := RationalFourierMotzkin.solve_complete (constraints A w k) x hx
    change counterprice A w k=none at h
    rw [← show counterprice A w k=solve (n*n) (constraints A w k) from rfl,h] at solved
    contradiction
  · intro factor
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro x hx
    have rational := RationalFourierMotzkin.solve_sound (constraints A w k) x hx
    exact no_price_of_factor A w k factor _ (RationalFourierMotzkin.rational_to_real _ x rational)

private theorem dimension_bound {n : ℕ} (G : Digraph (Fin n)) (w : Edge n → ℝ≥0) :
    HasEdgeRoundingFactor G w (n : ℝ) := by
  classical
  let Y := (graphEdges G).filter fun e => (1 : ℝ≥0) ≤ (n : ℝ≥0)*w e
  have actual : Y ⊆ graphEdges G := Finset.filter_subset _ _
  refine ⟨Nat.cast_nonneg _,fun c => ⟨Y,actual,?_,?_⟩⟩
  · intro s t far p
    by_contra empty
    have light (e : Edge n) (he : e ∈ p.edges) : (n : ℝ≥0)*w e ≤ 1 := by
      by_contra notLight
      exact empty ⟨e,he,Finset.mem_filter.mpr ⟨p.edges_subset_graphEdges he,(lt_of_not_ge notLight).le⟩⟩
    have mass : 1≤p.edgeWeight w := (coe_le_edgeDistance_iff G w s t 1).mp far p
    have room : (p.edges.card : ℝ≥0)<n := by
      exact_mod_cast (p.card_edges ▸ (show p.edgeLength<n by simpa only [Fintype.card_fin] using p.edgeLength_lt_card))
    have sum := Finset.sum_le_sum light
    simp only [← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,mul_one] at sum
    exact (not_lt_of_ge ((le_mul_of_one_le_right (Nat.cast_nonneg n) mass).trans sum)) room
  · rw [edgeCutCost_eq_sum_of_subset G c actual,weightedEdgeCost,← NNReal.coe_natCast,← NNReal.coe_mul,
      NNReal.coe_le_coe,Finset.mul_sum]
    calc
      _ ≤ ∑ e ∈ Y, (n : ℝ≥0)*(c e*w e) := by
        apply Finset.sum_le_sum
        intro e he
        have heavy := (Finset.mem_filter.mp he).2
        calc
          c e=c e*1 := (mul_one _).symm
          _≤c e*((n : ℝ≥0)*w e) := mul_le_mul_of_nonneg_left heavy zero_le
          _=(n : ℝ≥0)*(c e*w e) := by ac_rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset actual

private def accepted {n : ℕ} (A : Adjacency n) (w : Weights n) : List ℕ :=
  (List.range (n+1)).filter fun k => (counterprice A w k).isNone

/-- Exhaustive and exact on rational input, with the trivial dimension bound
ensuring a successful candidate even for the empty instance. -/
def least {n : ℕ} (A : Adjacency n) (w : Weights n) : ℕ :=
  (accepted A w).min?.getD n

private theorem mem_accepted {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) :
    k ∈ accepted A w ↔ k≤n ∧ HasEdgeRoundingFactor (graph A) (weights w) (k : ℝ) := by
  simp only [accepted,List.mem_filter,List.mem_range,Nat.lt_succ_iff,Option.isNone_iff_eq_none,
    counterprice_none_iff]

theorem least_valid {n : ℕ} (A : Adjacency n) (w : Weights n) :
    HasEdgeRoundingFactor (graph A) (weights w) (least A w : ℝ) := by
  unfold least
  cases h : (accepted A w).min? with
  | none => exact dimension_bound _ _
  | some k => exact ((mem_accepted A w k).mp (List.min?_eq_some_iff.mp h).1).2

theorem least_le_of_factor {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ)
    (h : HasEdgeRoundingFactor (graph A) (weights w) (k : ℝ)) : least A w≤k := by
  let L := accepted A w
  have hn : n ∈ L := (mem_accepted A w n).mpr ⟨le_rfl,dimension_bound _ _⟩
  unfold least
  cases hL : L.min? with
  | none => exact (List.not_mem_nil ((List.min?_eq_none_iff.mp hL) ▸ hn)).elim
  | some a =>
    change a≤k
    have le := (List.min?_eq_some_iff.mp hL).2
    by_cases hk : k≤n
    · exact le _ ((mem_accepted A w k).mpr ⟨hk,h⟩)
    · exact (le _ hn).trans (Nat.le_of_not_ge hk)

theorem least_le_original_factor {n : ℕ} (A : Adjacency n) (w : Weights n) :
    least A w ≤ ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) :=
  least_le_of_factor A w _ (ExactFlowCutGap.efg_bound n _ (graph A) (weights w) rfl)

def minimalCuts {n : ℕ} (cuts : List (Finset (Edge n))) : List (Finset (Edge n)) :=
  cuts.filter fun X => cuts.all fun Y => decide (¬ Y ⊂ X)

theorem minimalCuts_subset {n : ℕ} (cuts : List (Finset (Edge n))) : minimalCuts cuts ⊆ cuts :=
  fun _ h => (List.mem_filter.mp h).1

theorem exists_minimal_subset {n : ℕ} (cuts : List (Finset (Edge n))) (X : Finset (Edge n))
    (valid : X ∈ cuts) : ∃ Y ∈ minimalCuts cuts, Y ⊆ X := by
  let inner := cuts.filter fun Y => decide (Y ⊆ X)
  have member : X ∈ inner := List.mem_filter.mpr ⟨valid,decide_eq_true (Finset.Subset.rfl)⟩
  let Y := inner.minOn Finset.card (List.ne_nil_of_mem member)
  have present : Y ∈ inner := List.minOn_mem
  obtain ⟨listed,included⟩ := List.mem_filter.mp present
  have inside : Y ⊆ X := of_decide_eq_true included
  refine ⟨Y,List.mem_filter.mpr ⟨listed,List.all_eq_true.mpr ?_⟩,inside⟩
  intro Z available
  apply decide_eq_true
  intro less
  have smaller : Z ⊆ X := fun e hit => inside (less.subset hit)
  have found : Z ∈ inner := List.mem_filter.mpr ⟨available,decide_eq_true smaller⟩
  have lowest : Y.card ≤ Z.card := List.apply_minOn_le_of_mem (f:=Finset.card) found
  exact (not_lt_of_ge lowest) (Finset.card_lt_card less)

private def minimalConstraints {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) : List (Row (n*n)) :=
  (List.finRange (n*n)).map nonnegative ++ ((minimalCuts (candidates A (demands A w) ∅)).map (violation A w k))

private theorem minimal_constraints_iff {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ)
    (x : Fin (n*n) → ℝ) : Satisfies (minimalConstraints A w k) x ↔ Satisfies (constraints A w k) x := by
  rw [constraints_iff]
  constructor
  · intro satisfied
    have positive (i : Fin (n*n)) : 0 ≤ x i := by
      have row := satisfied (nonnegative i) (List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩))
      rwa [nonnegative_eval] at row
    refine ⟨positive,fun X listed => ?_⟩
    obtain ⟨Y,minimal,inside⟩ := exists_minimal_subset _ X listed
    have row := satisfied (violation A w k Y) (List.mem_append_right _ (List.mem_map.mpr ⟨Y,minimal,rfl⟩))
    rw [violation_eval,sub_nonneg] at row
    refine row.trans ?_
    unfold gap
    exact sub_le_sub_right (Finset.sum_le_sum_of_subset_of_nonneg inside (fun e _ _ => positive (index n e))) _
  · rintro ⟨pos,gaps⟩ r member
    unfold minimalConstraints at member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
      rw [nonnegative_eval]
      exact pos i
    · obtain ⟨X,selected,rfl⟩ := List.mem_map.mp member
      rw [violation_eval,sub_nonneg]
      exact gaps X (minimalCuts_subset _ selected)

private theorem solve_none_iff {m : ℕ} (rows : List (Row m)) :
    solve m rows = none ↔ ¬ ∃ x : Fin m → ℝ, Satisfies rows x := by
  constructor
  · rintro absent ⟨x,satisfies⟩
    have present := RationalFourierMotzkin.solve_complete rows x satisfies
    simp only [absent,Option.isSome_none,Bool.false_eq_true] at present
  · intro impossible
    cases found : solve m rows with
    | none => rfl
    | some x =>
      exact (impossible ⟨_,RationalFourierMotzkin.rational_to_real rows x
        (RationalFourierMotzkin.solve_sound rows x found)⟩).elim

private theorem minimal_isNone {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) :
    (solve (n*n) (minimalConstraints A w k)).isNone = (counterprice A w k).isNone := by
  apply Bool.eq_iff_iff.mpr
  simp only [Option.isNone_iff_eq_none,counterprice,solve_none_iff,minimal_constraints_iff]

/-- Compute the same exact factor using the cut constraints that are
minimal under inclusion. -/
def leastMinimal {n : ℕ} (A : Adjacency n) (w : Weights n) : ℕ :=
  ((List.range (n+1)).filter fun k => (solve (n*n) (minimalConstraints A w k)).isNone).min?.getD n

theorem leastMinimal_eq {n : ℕ} (A : Adjacency n) (w : Weights n) : leastMinimal A w = least A w := by
  simp only [leastMinimal,least,accepted,minimal_isNone]

private def support {n : ℕ} (A : Adjacency n) (w : Weights n) : Finset (Fin (n*n)) :=
  Finset.univ.filter fun j => originalWeight A w ((index n).symm j) ≠ 0

private theorem mem_support {n : ℕ} (A : Adjacency n) (w : Weights n) (j : Fin (n*n)) :
    j ∈ support A w ↔ originalWeight A w ((index n).symm j) ≠ 0 := by
  simp [support]

/-- Number of price coordinates carried by the support solver. -/
def supportDimension {n : ℕ} (A : Adjacency n) (w : Weights n) : ℕ :=
  (support A w).card

theorem supportDimension_eq {n : ℕ} (A : Adjacency n) (w : Weights n) :
    supportDimension A w = (Finset.univ.filter fun e => 0 < originalWeight A w e).card := by
  have mapped : (Finset.univ.filter fun e => 0 < originalWeight A w e).map (index n).toEmbedding =
      support A w := by
    ext j
    simp only [Finset.mem_map,Equiv.coe_toEmbedding,Finset.mem_filter,Finset.mem_univ,true_and,mem_support]
    constructor
    · rintro ⟨e,positive,rfl⟩
      simpa only [Equiv.symm_apply_apply] using ne_of_gt positive
    · intro nonzero
      exact ⟨(index n).symm j,pos_iff_ne_zero.mpr nonzero,(index n).apply_symm_apply j⟩
  simp only [supportDimension,← mapped,Finset.card_map]

private def supportIso {n : ℕ} (A : Adjacency n) (w : Weights n) :
    Fin (supportDimension A w) ≃ ↥(support A w) :=
  ((support A w).orderIsoOfFin rfl).toEquiv

private def zeroArcs {n : ℕ} (A : Adjacency n) (w : Weights n) : Finset (Edge n) :=
  Finset.univ.filter fun e => originalWeight A w e = 0

/-- Check demands in the original graph, enumerating only cuts on positive-weight arcs.
Retain the inclusion-minimal valid cuts among those candidates. -/
def supportedMinimalCuts {n : ℕ} (A : Adjacency n) (w : Weights n) : List (Finset (Edge n)) :=
  minimalCuts (candidates A (demands A w) (zeroArcs A w))

private theorem supported_candidates_iff {n : ℕ} (A : Adjacency n) (w : Weights n) (X : Finset (Edge n)) :
    X ∈ candidates A (demands A w) (zeroArcs A w) ↔
      X ∈ candidates A (demands A w) ∅ ∧ ∀ e ∈ X, originalWeight A w e ≠ 0 := by
  rw [mem_candidates,mem_candidates]
  simp [Finset.disjoint_left,zeroArcs,and_assoc]

private def supportedViolation {n : ℕ} (A : Adjacency n) (w : Weights n)
    (k : ℕ) (X : Finset (Edge n)) : Row (supportDimension A w) :=
  let full := violation A w k X
  let coord := supportIso A w
  ⟨fun i => full.coeff (coord i).val,full.constant⟩

private def supportedRows {n : ℕ} (A : Adjacency n) (w : Weights n) (cuts : List (Finset (Edge n))) (k : ℕ) :
    List (Row (supportDimension A w)) :=
  (List.finRange (supportDimension A w)).map nonnegative ++ cuts.map (supportedViolation A w k)

private abbrev supportedConstraints {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) :=
  supportedRows A w (supportedMinimalCuts A w) k

private theorem sum_supported {n : ℕ} (A : Adjacency n) (w : Weights n) (f : Fin (n*n) → ℝ)
    (vanishes : ∀ j ∉ support A w, f j = 0) :
    (∑ i, f (supportIso A w i).val) = ∑ j, f j := by
  rw [← Finset.sum_subset (Finset.subset_univ (support A w)) (fun j _ hj => vanishes j hj)]
  let coord := supportIso A w
  apply Finset.sum_bij (fun i _ => (coord i).val)
  · exact fun i _ => (coord i).property
  · exact fun i _ j _ same => coord.injective (Subtype.ext same)
  · intro j hj
    refine ⟨coord.symm ⟨j,hj⟩,Finset.mem_univ _,?_⟩
    exact congrArg Subtype.val (coord.apply_symm_apply ⟨j,hj⟩)
  · exact fun _ _ => rfl

private theorem supportedViolation_eval {n : ℕ} (A : Adjacency n) (w : Weights n)
    (k : ℕ) (X : Finset (Edge n)) (x : Fin (n*n) → ℝ)
    (inside : ∀ e ∈ X, originalWeight A w e ≠ 0) :
    (supportedViolation A w k X).eval (fun i => x (supportIso A w i).val) =
      gap A w k X (fun e => x (index n e))-1 := by
  rw [← violation_eval A w k X x]
  unfold Row.eval supportedViolation
  congr 1
  apply sum_supported A w (fun j => ((violation A w k X).coeff j : ℝ)*x j)
  intro j absent
  have zero : originalWeight A w ((index n).symm j) = 0 := by
    simpa only [mem_support,not_not] using absent
  have hX : (index n).symm j ∉ X := fun h => inside _ h zero
  simp [violation,hX,zero]

private theorem supportedConstraints_iff {n : ℕ} (A : Adjacency n) (w : Weights n)
    (k : ℕ) (x : Fin (n*n) → ℝ) :
    Satisfies (supportedConstraints A w k) (fun i => x (supportIso A w i).val) ↔
      (∀ j ∈ support A w, 0 ≤ x j) ∧
        ∀ X ∈ candidates A (demands A w) (zeroArcs A w), 1 ≤ gap A w k X (fun e => x (index n e)) := by
  constructor
  · intro satisfied
    have positive (j : Fin (n*n)) (hj : j ∈ support A w) : 0 ≤ x j := by
      let i := (supportIso A w).symm ⟨j,hj⟩
      have row := satisfied (nonnegative i) (List.mem_append_left _
        (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
      rw [nonnegative_eval] at row
      simpa [i] using row
    refine ⟨positive,fun X listed => ?_⟩
    obtain ⟨Y,minimal,inside⟩ := exists_minimal_subset _ X listed
    have row := satisfied (supportedViolation A w k Y) (List.mem_append_right _ (List.mem_map.mpr ⟨Y,minimal,rfl⟩))
    have hY := ((supported_candidates_iff A w Y).mp (minimalCuts_subset _ minimal)).2
    rw [supportedViolation_eval A w k Y x hY,sub_nonneg] at row
    refine row.trans ?_
    unfold gap
    have hX := ((supported_candidates_iff A w X).mp listed).2
    have nonneg (e : Edge n) (he : e ∈ X) : 0 ≤ x (index n e) :=
      positive _ ((mem_support A w _).mpr (by simpa only [Equiv.symm_apply_apply] using hX e he))
    exact sub_le_sub_right (Finset.sum_le_sum_of_subset_of_nonneg inside fun e he _ => nonneg e he) _
  · rintro ⟨positive,gaps⟩ r member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
      rw [nonnegative_eval]
      exact positive _ (supportIso A w i).property
    · obtain ⟨X,selected,rfl⟩ := List.mem_map.mp member
      have listed := minimalCuts_subset _ selected
      rw [supportedViolation_eval A w k X x ((supported_candidates_iff A w X).mp listed).2,sub_nonneg]
      exact gaps X listed

private def extendPrice {n : ℕ} (A : Adjacency n) (w : Weights n)
    (y : Fin (supportDimension A w) → ℝ) (outside : ℝ) (j : Fin (n*n)) : ℝ :=
  if hj : j ∈ support A w then y ((supportIso A w).symm ⟨j,hj⟩) else outside

private theorem extendPrice_apply {n : ℕ} (A : Adjacency n) (w : Weights n)
    (y : Fin (supportDimension A w) → ℝ) (outside : ℝ) (i : Fin (supportDimension A w)) :
    extendPrice A w y outside (supportIso A w i).val = y i := by
  rw [extendPrice,dite_eq_left (supportIso A w i).property]
  exact congrArg y ((supportIso A w).symm_apply_apply i)

private theorem extendPrice_potential {n : ℕ} (A : Adjacency n) (w : Weights n)
    (y : Fin (supportDimension A w) → ℝ) (p q : ℝ) :
    mwPotential (fun e => (actualEdgeWeight (graph A) (weights w) e : ℝ)) (fun e => extendPrice A w y p (index n e)) =
      mwPotential (fun e => (actualEdgeWeight (graph A) (weights w) e : ℝ)) (fun e => extendPrice A w y q (index n e)) := by
  unfold mwPotential
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hit : index n e ∈ support A w
  · simp [extendPrice,hit]
  · have zero : originalWeight A w e = 0 := by
      simpa only [mem_support,Equiv.symm_apply_apply,not_not] using hit
    simp [← originalWeight_cast A w e,zero]

private theorem supported_feasible_iff {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) :
    (∃ y : Fin (supportDimension A w) → ℝ, Satisfies (supportedConstraints A w k) y) ↔
      ∃ x : Fin (n*n) → ℝ, Satisfies (constraints A w k) x := by
  constructor
  · rintro ⟨y,feasible⟩
    let paid := mwPotential (fun e => (actualEdgeWeight (graph A) (weights w) e : ℝ))
      (fun e => extendPrice A w y 0 (index n e))
    let outside := 1+(k : ℝ)*paid
    let x := extendPrice A w y outside
    have restricted : (fun i => x (supportIso A w i).val) = y :=
      funext (extendPrice_apply A w y outside)
    have projected : Satisfies (supportedConstraints A w k) (fun i => x (supportIso A w i).val) := by
      rwa [restricted]
    obtain ⟨positive,gaps⟩ := (supportedConstraints_iff A w k x).mp projected
    have samePaid : mwPotential (fun e => (actualEdgeWeight (graph A) (weights w) e : ℝ))
        (fun e => x (index n e)) = paid := extendPrice_potential A w y outside 0
    have paid_nonneg : 0 ≤ paid := by
      unfold paid mwPotential
      refine Finset.sum_nonneg fun e _ => mul_nonneg ?_ (NNReal.coe_nonneg _)
      by_cases hi : index n e ∈ support A w
      · simpa only [extendPrice,dite_eq_left hi,x] using positive (index n e) hi
      · simp [extendPrice,hi]
    have nonneg (j : Fin (n*n)) : 0 ≤ x j := by
      by_cases hj : j ∈ support A w
      · exact positive j hj
      · simp only [x,extendPrice,dite_eq_right hj,outside]
        exact add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) paid_nonneg)
    refine ⟨x,(constraints_iff A w k x).mpr ⟨nonneg,fun X listed => ?_⟩⟩
    by_cases inside : ∀ e ∈ X, originalWeight A w e ≠ 0
    · exact gaps X ((supported_candidates_iff A w X).mpr ⟨listed,inside⟩)
    · push Not at inside
      obtain ⟨e,he,zero⟩ := inside
      have absent : index n e ∉ support A w := by
        simp [mem_support,zero]
      have expensive : outside ≤ ∑ f ∈ X, x (index n f) := by
        simpa only [x,extendPrice,dite_eq_right absent] using
          (Finset.single_le_sum (f := fun f => x (index n f)) (fun f _ => nonneg (index n f)) he)
      unfold gap
      rw [samePaid]
      exact le_sub_iff_add_le.mpr expensive
  · rintro ⟨x,feasible⟩
    obtain ⟨positive,gaps⟩ := (constraints_iff A w k x).mp feasible
    refine ⟨_,(supportedConstraints_iff A w k x).mpr ⟨fun j _ => positive j,fun X listed => ?_⟩⟩
    exact gaps X ((supported_candidates_iff A w X).mp listed).1

private theorem supported_isNone {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) :
    (solve (supportDimension A w) (supportedConstraints A w k)).isNone = (counterprice A w k).isNone := by
  apply Bool.eq_iff_iff.mpr
  simp only [Option.isNone_iff_eq_none,counterprice,solve_none_iff,supported_feasible_iff]

/-- Search an inclusive interval. Report the number of predicate calls. -/
private def bisectFactor (accept : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, lo, _ => (lo,0)
  | fuel+1, lo, hi =>
    if lo < hi then
      let mid := lo+(hi-lo)/2
      let result :=
        if accept mid then bisectFactor accept fuel lo mid
        else bisectFactor accept fuel (mid+1) hi
      (result.1,result.2+1)
    else (lo,0)

private theorem bisectFactor_spec (accept : ℕ → Bool) (target fuel lo hi : ℕ)
    (accepted : ∀ k, accept k = true ↔ target ≤ k)
    (left : lo ≤ target) (right : target ≤ hi) (width : hi-lo < 2^fuel) :
    (bisectFactor accept fuel lo hi).1 = target ∧ (bisectFactor accept fuel lo hi).2 ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [pow_zero] at width
    simpa only [bisectFactor] using show lo=target ∧ 0≤0 from ⟨by omega,le_rfl⟩
  | succ fuel ih =>
    rw [bisectFactor]
    by_cases interval : lo < hi
    · rw [ite_eq_left interval]
      let mid := lo+(hi-lo)/2
      let choose := if accept mid then bisectFactor accept fuel lo mid
        else bisectFactor accept fuel (mid+1) hi
      change choose.1=target ∧ choose.2+1≤fuel+1
      have leftWidth : mid-lo < 2^fuel := by
        rw [Nat.pow_succ] at width
        dsimp [mid]
        omega
      have rightWidth : hi-(mid+1) < 2^fuel := by
        rw [Nat.pow_succ] at width
        dsimp [mid]
        omega
      by_cases good : accept mid = true
      · have step := ih lo mid left ((accepted mid).mp good) leftWidth
        dsimp only [choose]
        rw [ite_eq_left good]
        exact ⟨step.1,Nat.succ_le_succ step.2⟩
      · have lower : mid+1 ≤ target := Nat.succ_le_of_lt (Nat.lt_of_not_ge (fun le => good ((accepted mid).mpr le)))
        have step := ih (mid+1) hi lower right rightWidth
        dsimp only [choose]
        rw [ite_eq_right good]
        exact ⟨step.1,Nat.succ_le_succ step.2⟩
    · rw [ite_eq_right interval]
      exact ⟨by omega,Nat.zero_le _⟩

private theorem supported_accepts_iff {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ) :
    (solve (supportDimension A w) (supportedConstraints A w k)).isNone = true ↔ least A w ≤ k := by
  rw [supported_isNone,Option.isNone_iff_eq_none,counterprice_none_iff]
  refine ⟨least_le_of_factor A w k,fun bound => ⟨Nat.cast_nonneg _,fun c => ?_⟩⟩
  obtain ⟨X,edges,cut,cost⟩ := (least_valid A w).round c
  have cast : (least A w : ℝ) ≤ (k : ℝ) := by exact_mod_cast bound
  exact ⟨X,edges,cut,cost.trans (mul_le_mul_of_nonneg_right cast (NNReal.coe_nonneg _))⟩

private def positiveNonloops {n : ℕ} (A : Adjacency n) (w : Weights n) : Finset (Edge n) :=
  Finset.univ.filter fun e => e.1 ≠ e.2 ∧ 0 < originalWeight A w e

/-- Every simple path uses at most this many positive-weight edges.
Count only actual positive-weight arcs with distinct endpoints. -/
def endpointCap {n : ℕ} (A : Adjacency n) (w : Weights n) : ℕ :=
  let positive := positiveNonloops A w
  min (positive.image Prod.fst).card (positive.image Prod.snd).card

theorem endpointCap_le_vertices {n : ℕ} (A : Adjacency n) (w : Weights n) :
    endpointCap A w ≤ n := by
  unfold endpointCap
  exact (min_le_left ..).trans (by simpa using Finset.card_le_univ (s := (positiveNonloops A w).image Prod.fst))

private theorem path_positive_card {n : ℕ} (A : Adjacency n) (w : Weights n)
    {s t : Fin n} (p : SimplePath (graph A) s t) :
    (p.edges.filter fun e => 0 < weights w e).card ≤ endpointCap A w := by
  let paid := p.edges.filter fun e => 0 < weights w e
  have contained : paid ⊆ positiveNonloops A w := by
    intro e he
    obtain ⟨mem,positive⟩ := Finset.mem_filter.mp he
    have weight : (0 : ℚ≥0) < originalWeight A w e := by
      rw [← NNRat.cast_lt (K := ℝ≥0),NNRat.cast_zero,originalWeight_eq,actualEdgeWeight_of_adj _ _ (p.edge_adj mem)]
      exact positive
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.edge_ne mem,weight⟩
  have distinctTails : Set.InjOn Prod.fst (↑paid : Set (Edge n)) := by
    intro e he f hf equal
    obtain ⟨i,rfl⟩ := (p.mem_edges e).mp (Finset.mem_filter.mp (show e ∈ paid from he)).1
    obtain ⟨j,rfl⟩ := (p.mem_edges f).mp (Finset.mem_filter.mp (show f ∈ paid from hf)).1
    have same : i.castSucc = j.castSucc := p.injective equal
    exact congrArg p.edgeAt (Fin.ext (congrArg (fun j : Fin (p.edgeLength+1) => j.val) same))
  have distinctHeads : Set.InjOn Prod.snd (↑paid : Set (Edge n)) := by
    intro e he f hf equal
    obtain ⟨i,rfl⟩ := (p.mem_edges e).mp (Finset.mem_filter.mp (show e ∈ paid from he)).1
    obtain ⟨j,rfl⟩ := (p.mem_edges f).mp (Finset.mem_filter.mp (show f ∈ paid from hf)).1
    have same : i.succ = j.succ := p.injective equal
    have val := congrArg Fin.val same
    change i.val+1 = j.val+1 at val
    exact congrArg p.edgeAt (Fin.ext (by omega))
  refine le_min ?_ ?_
  · rw [← Finset.card_image_of_injOn distinctTails]
    exact Finset.card_le_card (Finset.image_subset_image contained)
  · rw [← Finset.card_image_of_injOn distinctHeads]
    exact Finset.card_le_card (Finset.image_subset_image contained)

private theorem endpoint_factor {n : ℕ} (A : Adjacency n) (w : Weights n) :
    HasEdgeRoundingFactor (graph A) (weights w) (endpointCap A w : ℝ) := by
  classical
  let G := graph A
  let v := weights w
  let k := endpointCap A w
  let Y := (graphEdges G).filter fun e => (1 : ℝ≥0) ≤ (k : ℝ≥0)*v e
  have actual : Y ⊆ graphEdges G := Finset.filter_subset _ _
  refine ⟨Nat.cast_nonneg _,fun c => ⟨Y,actual,?_,?_⟩⟩
  · intro s t far p
    by_contra missing
    let paid := p.edges.filter fun e => 0<v e
    have paid_weight : (∑ e ∈ paid, v e) = p.edgeWeight v := by
      unfold SimplePath.edgeWeight
      refine Finset.sum_subset (Finset.filter_subset _ _) fun e member absent => ?_
      by_contra unequal
      exact absent (Finset.mem_filter.mpr ⟨member,pos_iff_ne_zero.mpr unequal⟩)
    have mass := (coe_le_edgeDistance_iff G v s t 1).mp far p
    rw [← paid_weight] at mass
    have nonempty : paid.Nonempty := by
      by_contra absent
      rw [Finset.not_nonempty_iff_eq_empty.mp absent,Finset.sum_empty] at mass
      norm_num at mass
    have small (e : Edge n) (member : e ∈ paid) : (k : ℝ≥0)*v e < 1 := by
      apply lt_of_not_ge
      intro large
      have hp := (Finset.mem_filter.mp member).1
      exact missing ⟨e,hp,Finset.mem_filter.mpr ⟨p.edges_subset_graphEdges hp,large⟩⟩
    have strict := Finset.sum_lt_sum_of_nonempty nonempty small
    simp only [← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,mul_one] at strict
    have cap : (paid.card : ℝ≥0) ≤ k := by exact_mod_cast path_positive_card A w p
    have bound : (k : ℝ≥0) ≤ (k : ℝ≥0)*∑ e ∈ paid, v e :=
      le_mul_of_one_le_right (Nat.cast_nonneg k) mass
    exact (not_lt_of_ge cap) (bound.trans_lt strict)
  · rw [edgeCutCost_eq_sum_of_subset G c actual,weightedEdgeCost,← NNReal.coe_natCast,← NNReal.coe_mul,
      NNReal.coe_le_coe,Finset.mul_sum]
    calc
      _ ≤ ∑ e ∈ Y, (k : ℝ≥0)*(c e*v e) := by
        apply Finset.sum_le_sum
        intro e he
        have heavy := (Finset.mem_filter.mp he).2
        calc
          c e=c e*1 := (mul_one _).symm
          _≤c e*((k : ℝ≥0)*v e) := mul_le_mul_of_nonneg_left heavy zero_le
          _=(k : ℝ≥0)*(c e*v e) := by ac_rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset actual

theorem least_le_endpointCap {n : ℕ} (A : Adjacency n) (w : Weights n) :
    least A w ≤ endpointCap A w :=
  least_le_of_factor A w _ (endpoint_factor A w)

private def emptyCutAccepted {n : ℕ} (A : Adjacency n) (w : Weights n) : Bool :=
  decide (∅ ∈ candidates A (demands A w) Finset.univ)

private theorem emptyCutAccepted_iff {n : ℕ} (A : Adjacency n) (w : Weights n) :
    emptyCutAccepted A w = true ↔
      IsIntegralEdgeCut (graph A) ∅ (edgeThresholdDemands (graph A) (weights w)) := by
  have demandSet : {e | e ∈ demands A w} = edgeThresholdDemands (graph A) (weights w) := by
    ext e
    exact RationalEdgeThresholds.demands_iff A w e
  rw [emptyCutAccepted,decide_eq_true_eq,mem_candidates,demandSet]
  simp

private theorem emptyCutAccepted_zero {n : ℕ} (A : Adjacency n) (w : Weights n) :
    emptyCutAccepted A w = true ↔ least A w = 0 := by
  rw [emptyCutAccepted_iff]
  constructor
  · intro cut
    have factor : HasEdgeRoundingFactor (graph A) (weights w) (0 : ℝ) := by
      refine ⟨le_rfl,fun c => ⟨∅,Finset.empty_subset _,cut,?_⟩⟩
      simp [edgeCutCost]
    exact Nat.le_zero.mp (least_le_of_factor A w 0 (by simpa using factor))
  · intro h
    have factor := least_valid A w
    rw [h,Nat.cast_zero] at factor
    obtain ⟨X,valid,cost⟩ := factor.real_cost_round (fun _ => 1) (fun _ => zero_le_one)
    have card : (X.card : ℝ) ≤ 0 := by simpa using cost
    have empty : X = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (by exact_mod_cast card))
    simpa [empty] using valid.2

/-- Return the exact factor and the number of exact feasibility tests.
Each test uses the same prepared positive-support cut list. -/
def leastSupportedWithCalls {n : ℕ} (A : Adjacency n) (w : Weights n) : ℕ × ℕ :=
  let hi := endpointCap A w
  if hi = 0 then (0,0)
  else if emptyCutAccepted A w then (0,0)
  else if hi = 1 then (1,0) else
    let cuts := supportedMinimalCuts A w
    let accepts k := (solve (supportDimension A w) (supportedRows A w cuts k)).isNone
    bisectFactor accepts (hi.log2+1) 1 hi

theorem leastSupportedWithCalls_zero {n : ℕ} (A : Adjacency n) (w : Weights n)
    (zeroCap : endpointCap A w = 0) : leastSupportedWithCalls A w = (0,0) := by
  simp [leastSupportedWithCalls,zeroCap]

theorem leastSupportedWithCalls_spec {n : ℕ} (A : Adjacency n) (w : Weights n) :
    (leastSupportedWithCalls A w).1 = least A w ∧
      (leastSupportedWithCalls A w).2 ≤ (endpointCap A w).log2+1 := by
  unfold leastSupportedWithCalls
  dsimp only
  split
  · rename_i h
    have cap := least_le_endpointCap A w
    rw [h] at cap
    exact ⟨(Nat.le_zero.mp cap).symm,Nat.zero_le _⟩
  · split
    · rename_i accepted
      exact ⟨((emptyCutAccepted_zero A w).mp accepted).symm,Nat.zero_le _⟩
    · rename_i lost
      have positive : 1 ≤ least A w := Nat.one_le_iff_ne_zero.mpr
        fun h => lost ((emptyCutAccepted_zero A w).mpr h)
      have bounded := least_le_endpointCap A w
      split
      · rename_i capOne
        exact ⟨(Nat.le_antisymm (bounded.trans_eq capOne) positive).symm,Nat.zero_le _⟩
      · exact bisectFactor_spec _ _ _ 1 _ (supported_accepts_iff A w) positive bounded
          ((Nat.sub_le ..).trans_lt Nat.lt_log2_self)

/-- The exact instance factor found using positive-edge prices. -/
def leastSupported {n : ℕ} (A : Adjacency n) (w : Weights n) : ℕ :=
  (leastSupportedWithCalls A w).1

theorem leastSupported_eq {n : ℕ} (A : Adjacency n) (w : Weights n) :
    leastSupported A w = least A w :=
  (leastSupportedWithCalls_spec A w).1

end DirectedFlowCutGap.RationalInstanceEdgeFactor
