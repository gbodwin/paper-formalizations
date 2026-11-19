import OnlineReachabilityPreservers.LocalOnlineAverage
import OnlineReachabilityPreservers.OnlineBound

/-! The Appendix A extremal estimate for arbitrary local path orders. -/

namespace OnlineReachabilityPreservers

open Finset

universe u v

local notation "ListBefore" => SourceAudit.BeforeIn

/-- The inductive envelope for simple lists with unique intersections and
no half-bridge through size four. -/
def OnlineListIncidenceBound (a b C : ℝ) : Prop :=
  ∀ (V : Type u) (I : Type v) [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
    (paths : I → List V), (∀ i, (paths i).Nodup) →
    (∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y) →
    HalfBridgeFree (ListBefore paths) 4 →
    (∑ i, ((paths i).length : ℝ)) ≤ C*onlineRate a b (Fintype.card V) (Fintype.card I)

private theorem online_list_regular_step {a b C : ℝ} (hC : 1 ≤ C) (ha₀ : 29/40 ≤ a)
    (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 701/1000)
    (hβ₀ : 2/3 ≤ onlineExponentStep b) (hβ₁ : onlineExponentStep b ≤ 701/1000)
    (prior : OnlineListIncidenceBound.{u,v} a b C) :
    ∃ A > 0, ∀ {V : Type u} {I : Type v} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → List V}, (∀ i, (paths i).Nodup) →
      (∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y) →
      HalfBridgeFree (ListBefore paths) 4 →
      ∀ (L D : ℕ), 0 < Fintype.card V → 0 < Fintype.card I →
      let M := ∑ i, (paths i).length
      16*Fintype.card V < M → 8*Fintype.card I < M →
      L*Fintype.card I ≤ 4*M → D*Fintype.card V ≤ 4*M →
      (∀ i, (paths i).length ≤ L) →
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) →
      (M:ℝ) ≤ A*onlineRate ((2+b)/(3+b)) (onlineExponentStep b) (Fintype.card V) (Fintype.card I) := by
  have bwide : b ≤ 3/4 := by linarith
  obtain ⟨X, hX, Y, hY, sampled⟩ := lemma36_list_expectation hC
    (show 7/10 ≤ a by linarith) ha₁ hb₀ bwide
  obtain ⟨A, hA, update⟩ := online_regular_step_from_counts hX hY ha₀ ha₁ hb₀ hb₁ hβ₀ hβ₁
  refine ⟨A, hA, ?_⟩
  intro V I _ _ _ _ paths simple unique free L D hn hp
  dsimp only
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).length
  intro dense long avgL avgD lengths degree
  change 16*n < M at dense
  change 8*p < M at long
  have hm : 0 < M := by omega
  have cube : M^3 ≤ 2048*(n*p)^2 :=
    ((lemma27_list_unique paths simple free unique).resolve_left (not_le_of_gt dense)).resolve_left
      (not_le_of_gt long)
  have length_total : M ≤ p*L := calc
    _ ≤ ∑ _ : I, L := sum_le_sum (fun i _ => lengths i)
    _ = _ := by simp [p]
  have degree_total : M ≤ n*D := by
    change (∑ i, (paths i).length) ≤ n*D
    simp_rw [← List.toFinset_card_of_nodup (simple _)]
    rw [← sum_occurrences]
    calc
      _ ≤ ∑ _ : V, D := sum_le_sum (fun v _ => degree v)
      _ = _ := by simp [n]
  have input : ListInducedSizeBound paths C a b := by
    intro S J
    have bound := prior S J (restrictListPaths paths S J)
      (fun i => restrictListPath_nodup (simple i.val) S)
      (fun ne w x y z => restrictListPaths_unique unique S J ne w x y z)
      (restrictListPaths_halfFree simple free S J)
    simpa only [Fintype.card_coe, onlineRate] using bound
  apply update n p M L D hn hp hm length_total degree_total cube
  intro h hh hl hd length_window _ hlarge
  let Q := ∑ base : I, (fullListBranchTuples paths base h).card
  refine ⟨Q, ?_, ?_⟩
  · have lower := lemma28_list_scaled_mean_lower simple free unique L h lengths hn hp dense.le long.le
      avgL length_window hlarge
    have sup : (∑ base, (listBranchTuples paths base h).card) ≤ Q :=
      sum_le_sum fun base _ => card_le_card (listBranchTuples_subset_full paths base h)
    exact lower.trans (Nat.mul_le_mul_left _ sup)
  · have castQ : (Q:ℝ) = ∑ base : I, ((fullListBranchTuples paths base h).card:ℝ) := Nat.cast_sum _ _
    rw [castQ]
    exact sampled simple free unique L D h hn hp hh hl hd lengths degree input hm avgL avgD

/-- The corrected online exponent update for half-4-bridge-free
systems in local path orders. The chosen branching window uses the input envelope coefficient. -/
theorem lemma37_list_update {a b C : ℝ} (hC : 1 ≤ C) (ha₀ : 29/40 ≤ a) (ha₁ : a < 3/4)
    (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 701/1000)
    (hβ₀ : 2/3 ≤ onlineExponentStep b) (hβ₁ : onlineExponentStep b ≤ 701/1000)
    (prior : OnlineListIncidenceBound.{u,v} a b C) :
    ∃ A ≥ 1, OnlineListIncidenceBound.{u,v} ((2+b)/(3+b)) (onlineExponentStep b) A := by
  let α := (2+b)/(3+b)
  let β := onlineExponentStep b
  have α0 : 0 ≤ α := by unfold α; exact div_nonneg (by linarith) (by linarith)
  have α1 : α ≤ 1 := (div_le_iff₀ (by linarith : 0 < 3+b)).mpr (by linarith)
  have β0 : 0 ≤ β := by linarith
  have β1 : β ≤ 1 := by linarith
  obtain ⟨A, hA, denseBound⟩ := online_list_regular_step hC ha₀ ha₁ hb₀ hb₁ hβ₀ hβ₁ prior
  refine ⟨32+4*A, by linarith, ?_⟩
  intro V I _ _ _ _ paths simple unique free
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).length
  let F := onlineRate α β (n:ℝ) (p:ℝ)
  have fN : (n:ℝ) ≤ F := le_max_left _ _
  have fP : (p:ℝ) ≤ F :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have f0 : 0 ≤ F := (Nat.cast_nonneg n).trans fN
  have castMass : (∑ i, ((paths i).length : ℝ)) = M := by simp only [M,Nat.cast_sum]
  rw [castMass]
  change (M:ℝ) ≤ (32+4*A)*F
  by_cases dense : 32*n < M
  swap
  · have real : (M:ℝ) ≤ 32*n := by exact_mod_cast (le_of_not_gt dense)
    nlinarith only [real, fN, mul_nonneg hA.le f0]
  by_cases long : 16*p < M
  swap
  · have real : (M:ℝ) ≤ 16*p := by exact_mod_cast (le_of_not_gt long)
    nlinarith only [real, fP, f0, mul_nonneg hA.le f0]
  have cap : M ≤ p*n := calc
    _ ≤ ∑ _i : I, n := sum_le_sum (fun i _ => by
      rw [← List.toFinset_card_of_nodup (simple i)]
      exact card_le_univ _)
    _ = _ := by simp [p, mul_comm]
  have hn : 0 < n := Nat.pos_of_ne_zero (fun e => by rw [e, mul_zero] at cap; omega)
  have hp : 0 < p := Nat.pos_of_ne_zero (fun e => by rw [e, zero_mul] at cap; omega)
  let D := M/n+1
  let L := M/p+1
  let vertices := splitListVertices paths D
  let after := listRegularizedPaths paths D L
  let n' := Fintype.card (ListVertexBlockIndex paths D)
  let p' := Fintype.card (ListBlockIndex vertices L)
  obtain ⟨ncap, pcap, same, length, degree, avgD, avgL⟩ :=
    regularization_list_average_caps paths simple hn hp (by omega) (by omega)
  change n' ≤ 2*n at ncap
  change p' ≤ 2*p at pcap
  change (∑ i, (after i).length) = M at same
  have hn' : 0 < n' := hn.trans_le (blockIndex_card_ge (occurrences (fun i => (paths i).toFinset)) D)
  have hp' : 0 < p' := hp.trans_le (blockIndex_card_ge (fun i => (vertices i).toFinset) L)
  have deg' : 16*n' < ∑ i, (after i).length := by rw [same]; omega
  have len' : 8*p' < ∑ i, (after i).length := by rw [same]; omega
  have capL : L*p' ≤ 4*∑ i, (after i).length := same.symm ▸ avgL
  have capD : D*n' ≤ 4*∑ i, (after i).length := same.symm ▸ avgD
  have stage := denseBound (paths := after) (listRegularizedPaths_simple paths simple D L)
    (fun ne w x y z => listRegularizedPaths_unique simple unique D L ne w x y z)
    (listRegularizedPaths_halfFree simple unique free D L) L D hn' hp'
    deg' len' capL capD length degree
  rw [same] at stage
  have size : onlineRate α β (n':ℝ) (p':ℝ) ≤ 4*F :=
    (onlineRate_mono α0 α1 β0 β1 (Nat.cast_nonneg n') (Nat.cast_nonneg p')
      (by exact_mod_cast ncap) (by exact_mod_cast pcap)).trans
      (onlineRate_double α0 β0 (Nat.cast_nonneg n) (Nat.cast_nonneg p))
  exact stage.trans ((mul_le_mul_of_nonneg_left size hA.le).trans (by nlinarith only [f0]))

private theorem online_list_incidence_initial : OnlineListIncidenceBound.{u,v} (8/11) (2/3) 16 := by
  intro V I _ _ _ _ paths simple unique free
  rw [← Nat.cast_sum]
  exact online_incidence_from_cubic_cases (lemma27_list_unique paths simple free unique)

/-- Each finite iterate in Theorem 38 is an incidence bound on actual
locally ordered systems with unique intersections, with a constant uniform over systems at that iterate. -/
theorem theorem38_list_unique_iteration (k : ℕ) :
    ∃ C ≥ 1, OnlineListIncidenceBound.{u,v} (onlineFirstExponent k) (onlineSecondExponent k) C := by
  obtain ⟨α, ⟨ha, hz⟩, _⟩ := theorem38_root
  obtain ⟨_, hsec, hfirst, _, _⟩ := theorem38_exponent_limits ha hz
  induction k with
  | zero => exact ⟨16, by norm_num, online_list_incidence_initial⟩
  | succ k ih =>
    obtain ⟨C, hC, prior⟩ := ih
    have next : onlineSecondExponent (k+1) = onlineExponentStep (onlineSecondExponent k) :=
      Function.iterate_succ_apply' _ _ _
    have hβ := hsec (k+1)
    rw [next] at hβ
    have b := hsec k
    have a := hfirst k
    have carry := lemma37_list_update hC ((by norm_num : (29/40:ℝ) ≤ 8/11).trans a.1) a.2
      b.1 (b.2.trans ha.2).le hβ.1 (hβ.2.trans ha.2).le prior
    rw [next]
    exact carry

/-- Every finite iterate on arbitrary simple path lists. Pruning keeps the
arrival order and loses at most a factor two in incidence mass. -/
theorem theorem38_list_iteration (k : ℕ) :
    ∃ C ≥ 1, ∀ (V : Type u) [LinearOrder V] [Fintype V] (p : ℕ)
      (paths : Fin p → List V), (∀ i, (paths i).Nodup) → HalfBridgeFree (ListBefore paths) 4 →
      (∑ i, ((paths i).length : ℝ)) ≤
        C*onlineRate (onlineFirstExponent k) (onlineSecondExponent k) (Fintype.card V) p := by
  obtain ⟨B, hB, bound⟩ := theorem38_list_unique_iteration.{u,0} k
  refine ⟨2*B, by linarith, ?_⟩
  intro V _ _ p paths simple free
  let kept := removeOppositeIntersections paths
  have half := removeOppositeIntersections_mass simple free (by decide)
  have retained := bound V (Fin p) kept
    (fun i => (removeOppositeIntersections_sublist paths i).nodup (simple i))
    (fun ne a b c d => removeOppositeIntersections_unique simple free (by decide) ne a b c d)
    (removeOppositeIntersections_halfFree simple free)
  rw [Fintype.card_fin] at retained
  calc
    _ ≤ 2 * ∑ i, ((kept i).length : ℝ) := by exact_mod_cast half
    _ ≤ 2 * (B*onlineRate (onlineFirstExponent k) (onlineSecondExponent k) (Fintype.card V) p) :=
      mul_le_mul_of_nonneg_left retained (by norm_num)
    _ = _ := by ring

end OnlineReachabilityPreservers
