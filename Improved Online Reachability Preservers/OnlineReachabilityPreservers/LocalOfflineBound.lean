import OnlineReachabilityPreservers.LocalOfflineMoment
import OnlineReachabilityPreservers.OfflineBound

/-! The Appendix B extremal estimate for arbitrary local path orders. -/

namespace OnlineReachabilityPreservers

open Finset

universe u v

local notation "ListBefore" => SourceAudit.BeforeIn

/-- The inductive envelope for simple lists with unique intersections and
no bridge of size at most four. -/
def OfflineListIncidenceBound (b B : ℝ) : Prop :=
  ∀ (V : Type u) (I : Type v) [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
    (paths : I → List V), (∀ i, (paths i).Nodup) →
    (∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y) →
    BridgeFree (ListBefore paths) 4 →
    (∑ i, ((paths i).length : ℝ)) ≤ offlineRate b (Fintype.card V) (Fintype.card I) * B

private theorem offline_list_sample_mean {V : Type u} {I : Type v}
    [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
    {b B N : ℝ} (prior : OfflineListIncidenceBound.{u,v} b B)
    (hb : 1/2 < b) (hb_le : b ≤ 1) (hB : 0 < B)
    {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (free : BridgeFree (ListBefore paths) 4) (L D h : ℕ) (hp : 0 < Fintype.card I)
    (hnN : 1 ≤ N) (hL : 0 < L) (hD : 0 < D) (hDN : (D:ℝ) ≤ N)
    (lengths : ∀ i, (paths i).length ≤ L)
    (degrees : ∀ x, (occurrences (fun i => (paths i).toFinset) x).card ≤ D)
    (ambient : ∀ base, ((listBranchSupport paths base h).card : ℝ) ≤ N) :
    let q := (∑ base : I, ((listOffBaseBranchTuples paths base h).card : ℝ))/(Fintype.card I:ℝ)
    q ≤ 2*B*N*L + Real.exp 8*(max 1 B)^2*(2+Real.log N)*N^(3/2:ℝ) +
      (2*B+(1/(2*b-1)+1)*B^(1/b))*N^(1/b)*(D:ℝ)^((2*b-1)/b) := by
  dsimp only
  let E := 2*B*N*L + Real.exp 8*(max 1 B)^2*(2+Real.log N)*N^(3/2:ℝ) +
      (2*B+(1/(2*b-1)+1)*B^(1/b))*N^(1/b)*(D:ℝ)^((2*b-1)/b)
  have hLr : (0:ℝ) < L := Nat.cast_pos.mpr hL
  have ppos : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr hp
  have bpos : 0 ≤ b := by linarith only [hb]
  apply (div_le_iff₀ ppos).mpr
  calc
    _ ≤ ∑ _ : I, E := by
      apply sum_le_sum
      intro base _
      let S := listBranchSupport paths base h
      exact lemma41_list_sampled_upper simple free unique base h D hnN hD hDN hLr hB hb hb_le
        (ambient base) (fun i => Nat.cast_le.mpr (lengths i)) (fun x _ => degrees x) (by
          intro J
          have bound := prior S J (restrictListPaths paths S J)
            (fun i => restrictListPath_nodup (simple i.val) S)
            (fun ne a d c f => restrictListPaths_unique unique S J ne a d c f)
            (restrictListPaths_fullFree simple free S J)
          simp only [Fintype.card_coe] at bound
          change _ ≤ B*offlineRate b N (J.card : ℝ)
          rw [mul_comm B]
          exact bound.trans (mul_le_mul_of_nonneg_right
            (offlineRate_mono bpos hb_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (ambient base) le_rfl) hB.le))
    _ = _ := by
      change (∑ _ : I, E) = E*(Fintype.card I:ℝ)
      rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

private theorem offline_list_regular_step :
    ∃ R ≥ 1, ∀ {b B : ℝ}, 2/3 ≤ b → b ≤ 71/100 → 1 ≤ B →
      OfflineListIncidenceBound.{u,v} b B → ∀ {V : Type u} {I : Type v}
      [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      (paths : I → List V), (∀ i, (paths i).Nodup) →
      (∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y) →
      BridgeFree (ListBefore paths) 4 → ∀ L D : ℕ,
      0 < Fintype.card V → 0 < Fintype.card I → 0 < L → 0 < D →
      let M := ∑ i, (paths i).length
      16*Fintype.card V < M → 8*Fintype.card I < M →
      L*Fintype.card I ≤ 4*M → D*Fintype.card V ≤ 4*M →
      (∀ i, (paths i).length ≤ L) → (∀ x, (occurrences (fun i => (paths i).toFinset) x).card ≤ D) →
      (M : ℝ) ≤ R*B^(1/2:ℝ)*offlineRate (offlineExponentStep b) (Fintype.card V) (Fintype.card I) := by
  obtain ⟨R, hR, update⟩ := offline_regular_step_from_sample
  refine ⟨R, hR, ?_⟩
  intro b B hb₀ hb₁ hB prior V I _ _ _ _ paths simple unique free L D hn hp hL hD
  dsimp only
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).length
  intro hdense hlong hcapL hcapD lengths degrees
  have cube : M^3 ≤ 2048*(n*p)^2 :=
    ((lemma27_list_unique paths simple free.halfFree unique).resolve_left (not_le_of_gt hdense)).resolve_left
      (not_le_of_gt hlong)
  apply update hb₀ hb₁ hB n p M L D hn hp hL hD hlong hcapL hcapD cube
  intro h window hlarge N hnN hDN
  let Q := ∑ base : I, (listOffBaseBranchTuples paths base h).card
  let q : ℝ := (∑ base : I, ((listOffBaseBranchTuples paths base h).card : ℝ))/p
  have lower : ((M : ℝ)/p)^2*((M : ℝ)/n)^2 ≤ 4096*q := by
    have count := lemma28_list_off_base_mean_lower simple free unique L h lengths hn hp hdense.le hlong.le
      hcapL window hlarge
    have mean := branch_window_mean_lower (M := M) (Q := Q) hn hp hlarge count
    change (40960 : ℝ)*(((M : ℝ)/p)^2*((M : ℝ)/n)^2) ≤
      (40*2048^2)*((Q:ℝ)/p) at mean
    have heq : (Q:ℝ) = ∑ base : I, ((listOffBaseBranchTuples paths base h).card:ℝ) := Nat.cast_sum _ _
    rw [heq] at mean
    change (40960 : ℝ)*(((M : ℝ)/p)^2*((M : ℝ)/n)^2) ≤ (40*2048^2)*q at mean
    linarith only [mean]
  have cards (base : I) : ((listBranchSupport paths base h).card : ℝ) ≤ N := by
    change ((listBranchSupport paths base h).card : ℝ) ≤ (L:ℝ)*(D:ℝ)*((h:ℝ)+1)
    exact_mod_cast (listBranchSupport_card_caps paths base h L D (lengths base) (fun x _ => degrees x))
  exact ⟨q, lower, offline_list_sample_mean prior (by linarith) (by linarith)
    (zero_lt_one.trans_le hB) simple unique free L D h hp hnN hL hD hDN lengths degrees cards⟩

/-- The Appendix B update on local paths with unique intersections. -/
theorem lemma42_list_update :
    ∃ R ≥ 1, ∀ {b B : ℝ}, 2/3 ≤ b → b ≤ 71/100 → 1 ≤ B →
      OfflineListIncidenceBound.{u,v} b B →
      OfflineListIncidenceBound.{u,v} (offlineExponentStep b) (R*B^(1/2:ℝ)) := by
  obtain ⟨R, hR, denseBound⟩ := offline_list_regular_step
  let K := 32+4*R
  refine ⟨K, by dsimp only [K]; linarith only [hR], ?_⟩
  intro b B hb₀ hb₁ hB prior
  let S := B^(1/2:ℝ)
  have hS : 1 ≤ S := by
    unfold S
    conv_lhs => rw [← Real.one_rpow (1/2:ℝ)]
    exact Real.rpow_le_rpow zero_le_one hB (by norm_num)
  have hRS : 0 ≤ R*S := mul_nonneg (zero_le_one.trans hR) (zero_le_one.trans hS)
  have hsmall : 32 ≤ K*S := by
    have hK : 32 ≤ K := by dsimp only [K]; linarith only [hR]
    exact hK.trans ((mul_one K).symm.le.trans
      (mul_le_mul_of_nonneg_left hS ((by norm_num : (0:ℝ) ≤ 32).trans hK)))
  let β := offlineExponentStep b
  have beta_pos : 0 ≤ β := by
    have : 0 < b := by linarith
    unfold β offlineExponentStep
    positivity
  have beta_le : β ≤ 1 := by
    change (2*b+1)/(2*b+2) ≤ (1 : ℝ)
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  intro V I _ _ _ _ paths simple unique free
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).length
  let F := offlineRate β (n:ℝ) (p:ℝ)
  have hNF : (n:ℝ) ≤ F := le_max_left _ _
  have hPF : (p:ℝ) ≤ F :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hF : 0 ≤ F := (Nat.cast_nonneg n).trans hNF
  rw [← Nat.cast_sum]
  change (M:ℝ) ≤ F*(K*S)
  have linCoeff := mul_le_mul_of_nonneg_right hsmall hF
  by_cases ndense : 32*n < M
  swap
  · have real : (M:ℝ) ≤ 32*n := by exact_mod_cast (le_of_not_gt ndense)
    nlinarith only [real, hNF, linCoeff]
  by_cases nlong : 16*p < M
  swap
  · have real : (M:ℝ) ≤ 16*p := by exact_mod_cast (le_of_not_gt nlong)
    nlinarith only [real, hPF, hF, linCoeff]
  have cap : M ≤ p*n := by
    calc
      _ ≤ ∑ i : I, n := sum_le_sum fun i _ => by
        rw [← List.toFinset_card_of_nodup (simple i)]
        exact card_le_univ _
      _ = _ := by simp [p]
  have hn : 0 < n := Nat.pos_of_ne_zero (fun e => by rw [e, mul_zero] at cap; omega)
  have hp : 0 < p := Nat.pos_of_ne_zero (fun e => by rw [e, zero_mul] at cap; omega)
  let D := M/n+1
  let L := M/p+1
  let vertices := splitListVertices paths D
  let after := listRegularizedPaths paths D L
  let n' := Fintype.card (ListVertexBlockIndex paths D)
  let p' := Fintype.card (ListBlockIndex vertices L)
  obtain ⟨ncap, pcap, sameMass, pathCaps, degreeCaps, degreeAvg, lengthAvg⟩ :=
    regularization_list_average_caps paths simple hn hp (by omega) (by omega)
  change n' ≤ 2*n at ncap
  change p' ≤ 2*p at pcap
  change (∑ i, (after i).length) = M at sameMass
  have hn' : 0 < n' := hn.trans_le (blockIndex_card_ge (occurrences (fun i => (paths i).toFinset)) D)
  have hp' : 0 < p' := hp.trans_le (blockIndex_card_ge (fun i => (vertices i).toFinset) L)
  have deg' : 16*n' < ∑ i, (after i).length := by rw [sameMass]; omega
  have len' : 8*p' < ∑ i, (after i).length := by rw [sameMass]; omega
  have capL : L*p' ≤ 4*∑ i, (after i).length := sameMass.symm ▸ lengthAvg
  have capD : D*n' ≤ 4*∑ i, (after i).length := sameMass.symm ▸ degreeAvg
  have stage := denseBound hb₀ hb₁ hB prior after (listRegularizedPaths_simple paths simple D L)
    (fun ne a b c d => listRegularizedPaths_unique simple unique D L ne a b c d)
    (listRegularizedPaths_fullFree simple unique free D L) L D hn' hp' (Nat.succ_pos _) (Nat.succ_pos _)
    deg' len' capL capD pathCaps degreeCaps
  rw [sameMass] at stage
  have size : offlineRate β (n':ℝ) (p':ℝ) ≤ 4*F :=
    (offlineRate_mono beta_pos beta_le (by positivity) (by positivity)
      (by exact_mod_cast ncap) (by exact_mod_cast pcap)).trans
      (offlineRate_double beta_pos beta_le (by positivity) (by positivity))
  exact stage.trans ((mul_le_mul_of_nonneg_left size hRS).trans (by
    dsimp only [K]
    nlinarith only [mul_nonneg (zero_le_one.trans hS) hF]))

private theorem offline_list_incidence_initial : OfflineListIncidenceBound.{u,v} (2/3) 16 := by
  intro V I _ _ _ _ paths simple unique free
  rw [← Nat.cast_sum]
  exact offline_incidence_from_cubic_cases (lemma27_list_unique paths simple free.halfFree unique)

/-- One constant works for the whole offline iteration on local orders. -/
theorem theorem43_list_iteration_uniform :
    ∃ B ≥ 1, ∀ k, OfflineListIncidenceBound.{u,v} (offlineExponent k) B := by
  obtain ⟨R, hR, step⟩ := lemma42_list_update
  let B := max 16 (R^2)
  have base : 16 ≤ B := le_max_left _ _
  have hB : 1 ≤ B := (by norm_num : (1:ℝ) ≤ 16).trans base
  have coeff := sqrt_coefficient hB (zero_le_one.trans hR) (le_max_right 16 (R^2))
  refine ⟨B, hB, ?_⟩
  intro k
  induction k with
  | zero =>
    intro V I _ _ _ _ paths simple unique free
    have bound := offline_list_incidence_initial V I paths simple unique free
    exact bound.trans (mul_le_mul_of_nonneg_left base ((Nat.cast_nonneg _).trans (le_max_left _ _)))
  | succ k ih =>
    have bounds := theorem43_exponent_limit.2.1 k
    have bound := step bounds.1 (bounds.2.trans offline_limit_lt).le hB ih
    have eq : offlineExponent (k+1) = offlineExponentStep (offlineExponent k) :=
      Function.iterate_succ_apply' _ _ _
    rw [eq]
    intro V I _ _ _ _ paths simple unique free
    exact (bound V I paths simple unique free).trans (mul_le_mul_of_nonneg_left coeff
      ((Nat.cast_nonneg _).trans (le_max_left _ _)))

/-- At the limit, the local-order envelope holds with exponent `1/√2`. -/
theorem theorem43_list_unique_limit :
    ∃ B ≥ 1, OfflineListIncidenceBound.{u,v} (1/Real.sqrt 2) B := by
  obtain ⟨B, hB, all⟩ := theorem43_list_iteration_uniform
  refine ⟨B, hB, ?_⟩
  intro V I _ _ _ _ paths simple unique free
  let n : ℝ := Fintype.card V
  let p : ℝ := Fintype.card I
  let m : ℝ := ∑ i, ((paths i).length:ℝ)
  have mass : m ≤ p*n := calc
    _ ≤ ∑ _ : I, n := sum_le_sum fun i _ => by
      rw [← List.toFinset_card_of_nodup (simple i)]
      exact Nat.cast_le.mpr (card_le_univ _)
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, p]
  exact offline_incidence_at_limit (Nat.cast_nonneg _) (Nat.cast_nonneg _) hB mass
    (fun k => all k V I paths simple unique free)

/-- Theorem 43 for arbitrary finite simple paths with no bridge through
size four. Remove opposite intersections once and absorb the factor two. -/
theorem theorem43_list_limit :
    ∃ B ≥ 1, ∀ (V : Type u) [LinearOrder V] [Fintype V] (p : ℕ)
      (paths : Fin p → List V), (∀ i, (paths i).Nodup) → BridgeFree (ListBefore paths) 4 →
      (∑ i, ((paths i).length:ℝ)) ≤ offlineRate (1/Real.sqrt 2) (Fintype.card V) p * B := by
  obtain ⟨B, hB, bound⟩ := theorem43_list_unique_limit.{u,0}
  refine ⟨2*B, by linarith, ?_⟩
  intro V _ _ p paths simple free
  let kept := removeOppositeIntersections paths
  have half := removeOppositeIntersections_mass simple free.halfFree (by decide)
  have retained := bound V (Fin p) kept
    (fun i => (removeOppositeIntersections_sublist paths i).nodup (simple i))
    (fun ne a b c d => removeOppositeIntersections_unique simple free.halfFree (by decide) ne a b c d)
    (removeOppositeIntersections_fullFree simple free)
  rw [Fintype.card_fin] at retained
  calc
    _ ≤ 2 * ∑ i, ((kept i).length : ℝ) := by exact_mod_cast half
    _ ≤ 2 * (offlineRate (1/Real.sqrt 2) (Fintype.card V) p * B) :=
      mul_le_mul_of_nonneg_left retained (by norm_num)
    _ = _ := by ring

end OnlineReachabilityPreservers
