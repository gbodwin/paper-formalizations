import DirectedFlowCutGap.RationalExactEdgeOracle
import DirectedFlowCutGap.BinaryFamilySampler

/-! An executable uniform family for the original rational edge weights.
The dimension-sized horizon is used when the excluded light mass permits it.
The general fallback uses the actual number of arcs. Both use the
same exact finite cut search. -/
namespace DirectedFlowCutGap.RationalOriginalEdgeFamily

open scoped NNRat NNReal BigOperators
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights demands weights)
open RationalEdgeDecomposition (Good originalWeight originalWeight_eq originalTotal)
open RationalExactEdgeOracle (Edge arcSet arcSet_value selectAvoiding selectAvoiding_minimum)

def floor (k : ℕ) (α : ℚ≥0) : ℚ≥0 := (4 * α * k)⁻¹

def scale (k : ℕ) : ℚ≥0 := (2 * (k : ℚ≥0))⁻¹

def light {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (k : ℕ) :
    Finset (Edge n) :=
  Finset.univ.filter fun e => originalWeight A w e < floor k α

def lightMass {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (k : ℕ) : ℚ≥0 :=
  α * ∑ e ∈ light A w α k, originalWeight A w e

def chooseScale {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) : ℕ :=
  if lightMass A w α n ≤ 1 / 4 then n else max 1 (arcSet A).card

def horizon {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (k : ℕ) : ℕ :=
  RationalWeakFamily.edgeRounds k (2 * α * originalTotal A w + (n : ℚ≥0)^2)

private def raised {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (k : ℕ)
    (e : Edge n) : ℚ≥0 :=
  max (floor k α) (originalWeight A w e)

def build {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (k : ℕ) :
    RationalWeakFamily.History (Edge n) :=
  let D := demands A w
  let S := light A w α k
  RationalWeakFamily.run (raised A w α k) (2*α) (scale k)
    (fun c => (selectAvoiding A D S c).getD ∅) (horizon A w α k)

def adaptive {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) :
    RationalWeakFamily.History (Edge n) :=
  if α=0 then ⟨fun _ => 1,[∅]⟩ else build A w α (chooseScale A w α)

private theorem floor_pos {k : ℕ} (hk : 0 < k) {α : ℚ≥0} (hα : 0 < α) :
    0 < floor k α := by unfold floor; positivity

private theorem scale_eq {k : ℕ} (hk : 0 < k) {α : ℚ≥0} (hα : 0 < α) :
    scale k=floor k α*(2*α) := by
  unfold scale floor
  have hk' : (k : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp [hα.ne',hk']
  norm_num

private theorem outside {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (k : ℕ) (e : Edge n)
    (he : e ∉ light A w α k) : floor k α ≤ originalWeight A w e := by
  exact le_of_not_gt (fun low => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,low⟩))

private theorem bounded_mass {n : ℕ} (A : Adjacency n) (w : Weights n)
    (α : ℚ≥0) (hα : 0 < α) : lightMass A w α (max 1 (arcSet A).card) ≤ 1/4 := by
  let m := max 1 (arcSet A).card
  let δ := floor m α
  let S := light A w α m
  let relevant := S ∩ arcSet A
  have hm : 0 < m := Nat.zero_lt_one.trans_le (le_max_left _ _)
  have ignoreZeros : (∑ e ∈ relevant, originalWeight A w e)=∑ e ∈ S, originalWeight A w e := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro e lightEdge notRelevant
    have absent : A[e.1.val][e.2.val] = false := by
      apply Bool.eq_false_iff.mpr
      intro isArc
      apply notRelevant
      refine Finset.mem_inter.mpr ⟨lightEdge,?_⟩
      rw [arcSet_value]
      exact (mem_graphEdges _ _).mpr isArc
    simp [originalWeight,absent]
  have cap : (∑ e ∈ S, originalWeight A w e) ≤ (m : ℚ≥0) * δ := by
    rw [← ignoreZeros]
    calc
      _ ≤ ∑ _e ∈ relevant, δ := Finset.sum_le_sum fun _ he =>
        (Finset.mem_filter.mp (Finset.mem_inter.mp he).1).2.le
      _ = (relevant.card : ℚ≥0) * δ := by simp [nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ zero_le
        exact_mod_cast ((Finset.card_le_card Finset.inter_subset_right : relevant.card≤(arcSet A).card).trans
          (le_max_right 1 (arcSet A).card))
  have tight : α * ((m : ℚ≥0) * δ) = 1/4 := by
    have hm' : (m : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    dsimp only [δ,floor]
    field_simp [hα.ne',hm']
  exact (mul_le_mul_of_nonneg_left cap zero_le).trans_eq tight

private theorem horizon_valid {n k : ℕ} (hk : 0 < k) (A : Adjacency n) (w : Weights n)
    (α : ℚ≥0) (hα : 0 < α) (e : Edge n) :
    Real.log ((∑ a, (raised A w α k a : ℝ)) / (raised A w α k e : ℝ)) ≤
      (scale k : ℝ) * (horizon A w α k : ℝ) := by
  let δ := (floor k α : ℝ)
  let W := (originalTotal A w : ℝ)
  let r (e : Edge n) := (raised A w α k e : ℝ)
  let M := (n : ℝ)^2
  let N := (k : ℝ)
  have hδ : 0 < δ := NNRat.cast_pos.mpr (floor_pos hk hα)
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ (k : ℝ)
    exact_mod_cast (show 1 ≤ k from hk)
  have lo (a : Edge n) : δ ≤ r a := NNRat.cast_le.mpr (le_max_left _ _)
  have positives (a : Edge n) : 0 < r a := hδ.trans_le (lo a)
  have totalPos : 0 < ∑ a, r a := (positives e).trans_le
    (Finset.single_le_sum (fun a _ => (positives a).le) (Finset.mem_univ e))
  have total : (∑ a, r a) ≤ W+M*δ := by
    calc
      _ ≤ ∑ a, ((originalWeight A w a : ℝ)+δ) := by
        apply Finset.sum_le_sum
        intro a _
        simp only [r,raised,NNRat.cast_max]
        exact max_le (le_add_of_nonneg_left (NNRat.cast_nonneg _)) (le_add_of_nonneg_right hδ.le)
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin,nsmul_eq_mul,W,originalTotal,NNRat.cast_sum,Nat.cast_mul,M,pow_two]
  have factor : δ⁻¹=4*(α : ℝ)*N := by
    simp only [δ,floor,NNRat.cast_inv,NNRat.cast_mul,NNRat.cast_ofNat,NNRat.cast_natCast,inv_inv,N]
  have cap : (∑ a, r a) / r e ≤
      (RationalWeakFamily.edgeMagnitude k (2*α*originalTotal A w+(n : ℚ≥0)^2) : ℝ) := by
    calc
      _ ≤ (∑ a, r a) / δ := div_le_div_of_nonneg_left totalPos.le hδ (lo e)
      _ ≤ (W+M*δ)/δ := div_le_div_of_nonneg_right total hδ.le
      _ = 4*(α : ℝ)*N*W+M := by
        rw [add_div,mul_div_cancel_right₀ _ hδ.ne',div_eq_mul_inv,factor]
        ring
      _ ≤ _ := by
        simp only [RationalWeakFamily.edgeMagnitude,NNRat.cast_add,NNRat.cast_mul,NNRat.cast_pow,
          NNRat.cast_ofNat,NNRat.cast_natCast]
        change _ ≤ N*(2*(2*(α : ℝ)*W+M)+N)
        have spare := mul_le_mul_of_nonneg_right hN (show 0 ≤ M by positivity)
        nlinarith [mul_nonneg (show 0 ≤ N by linarith) (show 0 ≤ M by positivity), sq_nonneg N]
  have log := (Real.log_le_log (div_pos totalPos (positives e)) cap).trans
    (RationalWeakFamily.edgeRounds_log hk (2*α*originalTotal A w+(n : ℚ≥0)^2))
  simpa only [horizon,scale,NNRat.cast_inv,NNRat.cast_mul,NNRat.cast_ofNat,NNRat.cast_natCast,r] using log

theorem build_length {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (k : ℕ) :
    (build A w α k).cuts.length=horizon A w α k := RationalWeakFamily.run_length ..

/-- Every output cut is valid and excludes all designated light arcs. The
counts are relative to the original weights and the certified original factor. -/
theorem build_spec {n k : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0)
    (hk : 0 < k) (hα : 0 < α) (small : lightMass A w α k ≤ 1/4)
    (factor : HasEdgeRoundingFactor (graph A) (weights w) (α : ℝ)) :
    let L := (build A w α k).cuts
    (∀ X ∈ L, Good A w X ∧ Disjoint X (light A w α k)) ∧
      ∀ e, (L.countP (fun X => decide (e ∈ X)) : ℝ)/(L.length : ℝ) ≤
        8*(originalWeight A w e : ℝ)*(α : ℝ) := by
  let S := light A w α k
  let μ := originalWeight A w
  let P (X : Finset (Edge n)) := Good A w X
  let Q (X : Finset (Edge n)) := P X ∧ Disjoint X S
  let r := raised A w α k
  let select (c : Edge n → ℚ≥0) := (selectAvoiding A (demands A w) S c).getD ∅
  have cert (c : Edge n → ℝ) (hc : ∀ e, 0 ≤ c e) : ∃ X : Finset (Edge n),
      P X ∧ (∑ e ∈ X, c e) ≤ (α : ℝ)*mwPotential (fun e => (μ e : ℝ)) c := by
    obtain ⟨X,⟨arcs,cut⟩,price⟩ := factor.real_cost_round c hc
    have exactMu (e : Edge n) : (μ e : ℝ) = (actualEdgeWeight (graph A) (weights w) e : ℝ) :=
      congrArg (fun x : ℝ≥0 => (x : ℝ)) (originalWeight_eq A w e)
    refine ⟨X,⟨arcs,fun s t h => cut s t ((RationalEdgeThresholds.demands_iff A w _).mp h)⟩,?_⟩
    simpa only [mwPotential,exactMu] using price
  have mass : (α : ℝ) * ∑ e ∈ S, (μ e : ℝ) ≤ 1/4 := by
    simpa only [lightMass,S,μ,NNRat.cast_mul,NNRat.cast_sum,NNRat.cast_div,NNRat.cast_one,NNRat.cast_ofNat] using
      (NNRat.cast_le (K := ℝ)).mpr small
  have enough (e : Edge n) (he : e ∉ S) : 0 < (μ e : ℝ) :=
    NNRat.cast_pos.mpr ((floor_pos hk hα).trans_le (outside A w α k e he))
  have sound (c : Edge n → ℝ) (hc : ∀ e, 0 ≤ c e) : ∃ X : Finset (Edge n),
      Q X ∧ (∑ e ∈ X, c e) ≤ ((2*α : ℚ≥0) : ℝ)*mwPotential (fun e => (r e : ℝ)) c := by
    obtain ⟨X,good,apart,price⟩ := BoundedSampling.oracle_avoids_small_mass
      (fun e => (μ e : ℝ)) (α : ℝ) P S (fun _ => NNRat.cast_nonneg _) (NNRat.cast_pos.mpr hα)
      mass enough cert c hc
    refine ⟨X,⟨good,apart⟩,price.trans ?_⟩
    simp only [NNRat.cast_mul,NNRat.cast_ofNat,mwPotential]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro e _
    split_ifs
    · exact mul_nonneg (hc e) (NNRat.cast_nonneg _)
    · exact mul_le_mul_of_nonneg_left (NNRat.cast_le.mpr (le_max_right _ _)) (hc e)
  have rational (c : Edge n → ℚ≥0) :
      Q (select c) ∧ (∑ e ∈ select c, c e) ≤ (2*α) * ∑ e, c e * r e := by
    obtain ⟨Y,⟨valid,apart⟩,paid⟩ := sound (fun e => (c e : ℝ)) (fun _ => NNRat.cast_nonneg _)
    obtain ⟨X,chosen,arcs,cut,excluded,minCost⟩ :=
      selectAvoiding_minimum A (demands A w) S c valid.1 valid.2 apart
    have realCost : (∑ e ∈ Y, c e) ≤ (2*α) * ∑ e, c e * r e := by
      apply (NNRat.cast_le (K := ℝ)).mp
      simpa only [NNRat.cast_sum,NNRat.cast_mul,mwPotential] using paid
    rw [show select c=X by simp only [select,chosen,Option.getD_some]]
    exact ⟨⟨⟨arcs,cut⟩,excluded⟩,minCost.trans realCost⟩
  have properties := RationalWeakFamily.run_spec r (2*α) (scale k) Q select
    (fun e => (floor_pos hk hα).trans_le (le_max_left _ _)) (by positivity)
    (by unfold scale; positivity)
    (fun e => (scale_eq hk hα).le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le))
    rational sound (horizon A w α k) (horizon_valid hk A w α hα)
  let L := (build A w α k).cuts
  have good : ∀ X ∈ L, Q X := properties.1
  refine ⟨good,?_⟩
  intro e
  by_cases he : e ∈ S
  · have absent : L.countP (fun X => decide (e ∈ X))=0 := by
      apply List.countP_eq_zero.mpr
      intro X hX mem
      exact Finset.disjoint_left.mp (good X hX).2 (decide_eq_true_eq.mp mem) he
    rw [absent,Nat.cast_zero,zero_div]
    positivity
  · have weight : r e=μ e := max_eq_right (outside A w α k e he)
    have h := properties.2 e
    change (L.countP (fun X => decide (e ∈ X)) : ℝ) ≤
      4*(r e : ℝ)*((2*α : ℚ≥0) : ℝ)*(horizon A w α k : ℝ) at h
    have size : L.length=horizon A w α k := build_length A w α k
    have pos : 0 < (horizon A w α k : ℝ) := Nat.cast_pos.mpr (RationalWeakFamily.edgeRounds_pos _ _)
    rw [size]
    apply (div_le_iff₀ pos).mpr
    rw [weight,NNRat.cast_mul,NNRat.cast_ofNat] at h
    exact h.trans_eq (by ring)

theorem adaptive_spec {n : ℕ} (hn : 0 < n) (A : Adjacency n) (w : Weights n)
    (α : ℚ≥0) (hα : 0 < α) (factor : HasEdgeRoundingFactor (graph A) (weights w) (α : ℝ)) :
    let L := (adaptive A w α).cuts
    L.length=horizon A w α (chooseScale A w α) ∧
      (∀ X ∈ L, Good A w X) ∧
      ∀ e, (L.countP (fun X => decide (e ∈ X)) : ℝ)/(L.length : ℝ) ≤
        8*(originalWeight A w e : ℝ)*(α : ℝ) := by
  let k := chooseScale A w α
  have feasible : 0 < k ∧ lightMass A w α k ≤ 1/4 := by
    unfold k chooseScale
    split
    · exact ⟨hn,by assumption⟩
    · exact ⟨Nat.zero_lt_one.trans_le (le_max_left _ _),bounded_mass A w α hα⟩
  have h := build_spec A w α feasible.1 hα feasible.2 factor
  simp only [adaptive,ite_eq_right hα.ne']
  exact ⟨build_length A w α k,fun X hX => (h.1 X hX).1,h.2⟩

theorem adaptive_nonempty {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) :
    0 < (adaptive A w α).cuts.length := by
  unfold adaptive
  split
  · exact Nat.zero_lt_succ _
  · rw [build_length]
    exact RationalWeakFamily.edgeRounds_pos _ _

private theorem empty_at_zero {n : ℕ} (A : Adjacency n) (w : Weights n)
    (factor : HasEdgeRoundingFactor (graph A) (weights w) 0) : Good A w ∅ := by
  obtain ⟨Y,⟨arcs,cut⟩,cost⟩ := factor.real_cost_round (fun _ => 1) (fun _ => zero_le_one)
  have card : (Y.card : ℝ) ≤ 0 := by simpa [nsmul_eq_mul] using cost
  have ey : Y=∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (by exact_mod_cast card))
  refine ⟨Finset.empty_subset _,fun s t h => ?_⟩
  rw [← ey]
  exact cut s t ((RationalEdgeThresholds.demands_iff A w _).mp h)

theorem adaptive_spec_all {n : ℕ} (hn : 0 < n) (A : Adjacency n) (w : Weights n)
    (α : ℚ≥0) (factor : HasEdgeRoundingFactor (graph A) (weights w) (α : ℝ)) :
    let L := (adaptive A w α).cuts
    (∀ X ∈ L, Good A w X) ∧
      ∀ e, (L.countP (fun X => decide (e ∈ X)) : ℝ)/(L.length : ℝ) ≤
        8*(originalWeight A w e : ℝ)*(α : ℝ) := by
  by_cases h : α=0
  · subst α
    simp only [adaptive]
    refine ⟨?_,by intro e; simp⟩
    intro X member
    have eq : X=∅ := List.mem_singleton.mp member
    rw [eq]
    apply empty_at_zero A w
    simpa using factor
  · exact (adaptive_spec hn A w α (lt_of_le_of_ne zero_le (Ne.symm h)) factor).2

private theorem index_count {A : Type} (L : List A) (P : A → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i : Fin L.length => P L[i.val])).card =
      L.countP (fun x => decide (P x)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [Finset.card_filter,List.length_cons,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,
      List.getElem_cons_zero,List.getElem_cons_succ,List.countP_cons,decide_eq_true_eq]
    have sum : (∑ i : Fin L.length, if P L[i.val] then 1 else 0)=L.countP (fun x => decide (P x)) :=
      by simpa only [Finset.card_filter] using ih
    rw [sum]
    split <;> simp_all [Nat.add_comm]

/-- The law samples the actual returned list by its indices. Multiplicity
of equal cuts is retained. -/
noncomputable def law {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) :
    PMF (Finset (Edge n)) :=
  let L := (adaptive A w α).cuts
  WeakDecomposition.familyLaw (adaptive_nonempty A w α) (fun i : Fin L.length => L[i.val])

theorem law_spec {n : ℕ} (hn : 0 < n) (A : Adjacency n) (w : Weights n) (α : ℚ≥0)
    (factor : HasEdgeRoundingFactor (graph A) (weights w) (α : ℝ)) :
    (∀ X ∈ (law A w α).support, Good A w X) ∧
      ∀ e, ((law A w α).toOuterMeasure {X | e ∈ X}).toReal ≤
        8*(originalWeight A w e : ℝ)*(α : ℝ) := by
  let L := (adaptive A w α).cuts
  have certified := adaptive_spec_all hn A w α factor
  refine ⟨?_,?_⟩
  · intro X member
    exact WeakDecomposition.familyLaw_support (adaptive_nonempty A w α)
      (fun i : Fin L.length => L[i.val]) (Good A w)
      (fun i => certified.1 _ (List.getElem_mem (l := L) i.isLt)) member
  · intro e
    change ((WeakDecomposition.familyLaw (adaptive_nonempty A w α)
      (fun i : Fin L.length => L[i.val])).toOuterMeasure {X | e ∈ X}).toReal ≤ _
    rw [WeakDecomposition.familyLaw_marginal]
    have counted := index_count L (fun X : Finset (Edge n) => e ∈ X)
    rw [counted]
    exact certified.2 e

theorem adaptive_at_original_factor {n : ℕ} (hn : 0 < n) (A : Adjacency n) (w : Weights n)
    (positive : 0 < ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w))) :
    let k := ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w))
    let α := (k : ℚ≥0)
    let L := (adaptive A w α).cuts
    L.length=horizon A w α (chooseScale A w α) ∧
      (∀ X ∈ L, Good A w X) ∧
      ∀ e, (L.countP (fun X => decide (e ∈ X)) : ℝ)/(L.length : ℝ) ≤
        8*(originalWeight A w e : ℝ)*(k : ℝ) := by
  let W := totalEdgeWeight (graph A) (weights w)
  let k := ExactFlowCutGap.efg n W
  have hk : 0 < (k : ℚ≥0) := Nat.cast_pos.mpr positive
  have f := ExactFlowCutGap.efg_bound n W (graph A) (weights w) rfl
  have hF : HasEdgeRoundingFactor (graph A) (weights w) ((k : ℚ≥0) : ℝ) :=
    by simpa only [NNRat.cast_natCast] using f
  simpa only [NNRat.cast_natCast] using adaptive_spec hn A w (k : ℚ≥0) hk hF

theorem law_at_original_factor {n : ℕ} (A : Adjacency n) (w : Weights n) :
    let k := ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w))
    let p := law A w (k : ℚ≥0)
    (∀ X ∈ p.support, Good A w X) ∧
      ∀ e, (p.toOuterMeasure {X | e ∈ X}).toReal ≤
        8*(originalWeight A w e : ℝ)*(k : ℝ) := by
  by_cases hn : 0 < n
  · let W := totalEdgeWeight (graph A) (weights w)
    let k := ExactFlowCutGap.efg n W
    have f := ExactFlowCutGap.efg_bound n W (graph A) (weights w) rfl
    have factor : HasEdgeRoundingFactor (graph A) (weights w) ((k : ℚ≥0) : ℝ) :=
      by simpa only [NNRat.cast_natCast] using f
    simpa only [NNRat.cast_natCast] using law_spec hn A w (k : ℚ≥0) factor
  · have none : n=0 := by omega
    subst n
    exact ⟨fun _ _ => ⟨fun e _ => Fin.elim0 e.1,fun s => Fin.elim0 s⟩,fun e => Fin.elim0 e.1⟩

def draw {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (trials : ℕ)
    (tape : List Bool) : Option ((Option (Finset (Edge n)) × ℕ) × EncodedSolverBits.Tape) :=
  let L := (adaptive A w α).cuts
  EncodedSolverBits.run (BinaryFamilySampler.choose L trials) tape

theorem draw_used {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (trials : ℕ)
    (tape : List Bool)
    (enough : trials*FairBitWords.width (adaptive A w α).cuts.length ≤ tape.length) :
    ∃ cut paid used, draw A w α trials tape=some ((cut,paid),(tape.drop used,used)) ∧
      used ≤ trials*FairBitWords.width (adaptive A w α).cuts.length :=
  BinaryFamilySampler.choose_used _ _ _ enough

theorem draw_valid {n : ℕ} (hn : 0 < n) (A : Adjacency n) (w : Weights n) (α : ℚ≥0)
    (factor : HasEdgeRoundingFactor (graph A) (weights w) (α : ℝ))
    {trials : ℕ} {tape rest : List Bool} {cut : Finset (Edge n)} {paid used : ℕ}
    (found : draw A w α trials tape=some ((some cut,paid),(rest,used))) : Good A w cut := by
  let L := (adaptive A w α).cuts
  have seen := EncodedSolverBits.run_support (BinaryFamilySampler.choose_binary L trials) found
  have present := (BinaryFamilySampler.choose_supported L trials seen).1 cut (by simp)
  exact (adaptive_spec_all hn A w α factor).1 cut present

private theorem draw_fair_law {n : ℕ} (A : Adjacency n) (w : Weights n) (α : ℚ≥0) (trials : ℕ) :
    let L := (adaptive A w α).cuts
    let q := trials*FairBitWords.width L.length
    (EncodedSolverBits.fairTape q).map (fun tape => ((draw A w α trials tape).map (fun r => r.1.1)).join) =
      (FiniteDrawTrees.ideal (BinaryFamilySampler.choose L trials)).map Prod.fst := by
  let L := (adaptive A w α).cuts
  have h := congrArg (PMF.map (fun o : Option (Option (Finset (Edge n)) × ℕ) => (o.map Prod.fst).join))
    (EncodedSolverBits.run_fairTape (BinaryFamilySampler.choose_within L trials)
      (BinaryFamilySampler.choose_binary L trials))
  simpa only [PMF.map_comp,Function.comp_def,Option.map_map,Option.map_some,Option.join_some,draw] using h

/-- With enough fair bits, bounded rejection changes the success mass but
retains the multiplicity of every successful index. -/
theorem draw_law {n : ℕ} (hn : 0 < n) (A : Adjacency n) (w : Weights n) (α : ℚ≥0)
    (factor : HasEdgeRoundingFactor (graph A) (weights w) (α : ℝ)) (trials : ℕ) :
    let L := (adaptive A w α).cuts
    let q := trials*FairBitWords.width L.length
    let p := (EncodedSolverBits.fairTape q).map (fun tape => ((draw A w α trials tape).map (fun r => r.1.1)).join)
    p none = BoundedBitRejection.law L.length trials none ∧
      ∀ e, FiniteAmplification.probability p (fun o => ∃ X ∈ o, e ∈ X) ≤
        8*(originalWeight A w e : ℝ)*(α : ℝ) := by
  let L := (adaptive A w α).cuts
  let q := trials*FairBitWords.width L.length
  let p := (EncodedSolverBits.fairTape q).map (fun tape => ((draw A w α trials tape).map (fun r => r.1.1)).join)
  change p none = _ ∧ ∀ e, FiniteAmplification.probability p (fun o => ∃ X ∈ o, e ∈ X) ≤
    8*(originalWeight A w e : ℝ)*(α : ℝ)
  have eq : p = (FiniteDrawTrees.ideal (BinaryFamilySampler.choose L trials)).map Prod.fst :=
    draw_fair_law A w α trials
  rw [eq]
  refine ⟨BinaryFamilySampler.choose_failure L (adaptive_nonempty A w α) trials,fun e => ?_⟩
  rw [BinaryFamilySampler.choose_marginal L (adaptive_nonempty A w α) trials (fun X => e ∈ X)]
  have nonnegative : (0 : ℝ) ≤ (L.countP (fun X => decide (e ∈ X)) : ℝ)/(L.length : ℝ) := by positivity
  exact (mul_le_of_le_one_left nonnegative (sub_le_self _ ENNReal.toReal_nonneg)).trans
    ((adaptive_spec_all hn A w α factor).2 e)

end DirectedFlowCutGap.RationalOriginalEdgeFamily
