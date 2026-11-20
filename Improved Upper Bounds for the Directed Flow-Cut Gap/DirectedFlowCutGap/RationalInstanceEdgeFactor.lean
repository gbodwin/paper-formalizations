import DirectedFlowCutGap.RationalExactEdgeOracle
import DirectedFlowCutGap.RationalFourierMotzkin
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

end DirectedFlowCutGap.RationalInstanceEdgeFactor
