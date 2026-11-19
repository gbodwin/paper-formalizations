import OnlineReachabilityPreservers.OnlineSharp
import OnlineReachabilityPreservers.PairwiseBudget
import OnlineReachabilityPreservers.PathAssignments

/-! Theorem 5 for unrestricted pairs, in both preassigned path models. -/

namespace OnlineReachabilityPreservers

open Finset

universe v

section Assignment

variable {V : Type v} [LinearOrder V] [Fintype V]

private def pairwiseRule (G : Arcs V) : PathRule V :=
  fun A d => forwardPath (condensation G) A d.1 d.2

private theorem pairwiseRule_valid (G : Arcs V) :
    ∀ A ⊆ condensation G, ∀ d ∈ (univ : Arcs V),
      pathArcs (pairwiseRule G A d) ⊆ condensation G ∧
        (∀ l, pairwiseRule G A d = some l → Walk (condensation G) d.1 d.2 l) ∧
        (Reach (condensation G) d.1 d.2 → ∃ l, pairwiseRule G A d = some l) := by
  intro A hA d _
  exact ⟨forwardEdges_subset hA d, fun _ hl => (forwardPath_spec hA hl).1,
    (forwardPath_succeeds hA (condensation_dag G)).mpr⟩

private def pairwiseCertifiedBudget (G : Arcs V) (q : ℕ) : ℕ :=
  certifiedBudget (pairwiseRule G) univ q (condensation G).card

private theorem pairwiseCertifiedBudget_spec (G : Arcs V) {q : ℕ} (hq : 0 < q) :
    KnownBudgetCertified (pairwiseRule G) univ q (pairwiseCertifiedBudget G q) ∧
      ∀ F, KnownBudgetCertified (pairwiseRule G) univ q F → pairwiseCertifiedBudget G q ≤ F := by
  apply certifiedBudget_spec
  apply knownBudget_certify _ _ _ _ hq
  intro T _ _ _
  exact card_le_card (forwardRunFrom_subset (empty_subset _) T)

/-- The all-pairs path assignment with known total demand count. The budget
search uses only finite integer computations on the input graph. -/
def knownPairPath (G : Arcs V) (p : ℕ) (d : V × V) : Option (List (V × V)) :=
  liftPath G d (knownBudgetPath (pairwiseRule G) univ p
    (pairwiseCertifiedBudget G p) (projectDemand G d))

/-- The all-pairs path assignment with zero-based arrival index. Each quota
uses only the input graph, so the assignment has no final-length input. -/
def indexedPairPath (G : Arcs V) (i : ℕ) (d : V × V) : Option (List (V × V)) :=
  liftPath G d (indexSensitivePath (pairwiseRule G) univ (pairwiseBase (Fintype.card V))
    (pairwiseCertifiedBudget G) i (projectDemand G d))

theorem knownPairPath_valid (G : Arcs V) (p : ℕ) (d : V × V) :
    ValidPathChoice G d (knownPairPath G p d) := by
  apply liftPath_valid
  obtain ⟨hw, he⟩ := knownBudgetPath_valid (pairwiseRule G) (condensation G) univ p
    (pairwiseCertifiedBudget G p) (projectDemand G d) (mem_univ _) (pairwiseRule_valid G)
  exact ⟨fun l hl => (hw l hl).simple_of_dag (condensation_dag G), he⟩

theorem indexedPairPath_valid (G : Arcs V) (i : ℕ) (d : V × V) :
    ValidPathChoice G d (indexedPairPath G i d) := by
  apply liftPath_valid
  obtain ⟨hw, he⟩ := indexSensitivePath_valid (pairwiseRule G) (condensation G) univ
    (pairwiseBase (Fintype.card V)) (pairwiseCertifiedBudget G) i (projectDemand G d)
    (mem_univ _) (pairwiseRule_valid G)
  exact ⟨fun l hl => (hw l hl).simple_of_dag (condensation_dag G), he⟩

/-- The selected original-graph paths are feasible for both modes, with a
common edge guarantee. The index-sensitive output is irrevocable. -/
def PairwiseNonAdaptiveBound (bound : ℕ → ℕ → ℝ) : Prop :=
  ∀ (V : Type v) [LinearOrder V] [Fintype V] (G : Arcs V),
    (∀ p (D : List (V × V)), D.length ≤ p →
      let H := plannedArcs (fun _ => knownPairPath G p) D
      H ⊆ G ∧ Preserves G H D ∧ (H.card:ℝ) ≤ bound (Fintype.card V) p) ∧
    (∀ D : List (V × V),
      let H := plannedArcs (indexedPairPath G) D
      H ⊆ G ∧ Preserves G H D ∧ (H.card:ℝ) ≤ bound (Fintype.card V) D.length) ∧
    ∀ D E : List (V × V), D <+: E →
      plannedArcs (indexedPairPath G) D ⊆ plannedArcs (indexedPairPath G) E

private theorem knownPairPath_card (G : Arcs V) {p : ℕ} (hp : 0 < p) (D : List (V × V))
    (hD : D.length ≤ p) :
    (plannedArcs (fun _ => knownPairPath G p) D).card ≤
      2*Fintype.card V + 2*pairwiseCertifiedBudget G p := by
  let P := D.map (projectDemand G)
  let pick := knownBudgetPath (pairwiseRule G) univ p (pairwiseCertifiedBudget G p)
  have hcard : P.toFinset.card ≤ p := by
    apply (List.toFinset_card_le P).trans
    simpa only [P,List.length_map] using hD
  have hcert := theorem15_certified_budget (pairwiseRule G) univ p (pairwiseCertifiedBudget G p)
    hp (pairwiseCertifiedBudget_spec G hp).1 P.toFinset (subset_univ _) hcard
  have hunion := (card_le_card (plannedArcs_constant_le pick P)).trans hcert
  exact (plannedArcs_lift_card G (fun _ => pick) D).trans (Nat.add_le_add_left hunion _)

private theorem indexedPairPath_card (G : Arcs V) (D : List (V × V)) (F : ℕ → ℕ)
    (envelope : ∀ q, 0 < q → pairwiseCertifiedBudget G q ≤ F q)
    (summable : ∀ k, (∑ j ∈ range (k+1), F (dyadicQuota (pairwiseBase (Fintype.card V)) j)) ≤
      8*F (dyadicQuota (pairwiseBase (Fintype.card V)) k))
    (last : ∀ p, 0 < p →
      F (dyadicQuota (pairwiseBase (Fintype.card V)) (indexLevel (pairwiseBase (Fintype.card V)) (p-1))) ≤
        32*F p) :
    (plannedArcs (indexedPairPath G) D).card ≤ 2*Fintype.card V + 512*F D.length := by
  let P := D.map (projectDemand G)
  let base := pairwiseBase (Fintype.card V)
  let pick := indexSensitivePath (pairwiseRule G) univ base (pairwiseCertifiedBudget G)
  have h := theorem16_certified_budget (pairwiseRule G) univ base (pairwiseCertifiedBudget G) F
    (by simp [base,pairwiseBase]) (fun _ hq => (pairwiseCertifiedBudget_spec G hq).1)
    envelope 8 32 summable last P (fun _ _ => mem_univ _)
  change (plannedArcs pick P).card ≤ 512*F P.length at h
  rw [show P.length = D.length by simp [P]] at h
  exact (plannedArcs_lift_card G pick D).trans (Nat.add_le_add_left h _)

end Assignment

private theorem theorem5_pairwise_transfer {a b K : ℝ} {ε : ℕ → ℝ}
    (ha₀ : 1/2 ≤ a) (ha₁ : a ≤ 3/4) (hb₀ : 1/2 ≤ b) (hb₁ : b ≤ 1)
    (he : ∀ n, 0 ≤ ε n) (hK : 1 ≤ K)
    (adaptive : ∀ (V : Type v) [LinearOrder V] [Fintype V] (G : Arcs V) (D : List (V × V)),
      ((sinkPreserver G D).card:ℝ) ≤ K*pairwiseRate a b (ε (Fintype.card V)) (Fintype.card V) D.length) :
    PairwiseNonAdaptiveBound.{v} (fun n p => (2+512*(3*K+1))*pairwiseRate a b (ε n) n p) := by
  intro V _ _ G
  let n := Fintype.card V
  let F := pairwiseBudget a b (ε n) (3*K) n
  have hK3 : 1 ≤ 3*K := by linarith
  have envelope (q : ℕ) (hq : 0 < q) : pairwiseCertifiedBudget G q ≤ F q := by
    apply (pairwiseCertifiedBudget_spec G hq).2
    apply knownBudget_certify _ _ _ _ hq
    intro T _ _ hl
    let C := condensation G
    have dag : IsDAG C := condensation_dag G
    change (forwardRun C T).card ≤ F q
    apply forwardRun_pairwise_budget dag T hl (zero_le_one.trans hK)
    have hmono := pairwiseRate_mono (e := ε n) (by positivity : (0:ℝ) ≤ n)
      (show a ≤ 1 by linarith only [ha₁]) (show 0 ≤ b by linarith only [hb₀])
      (show 0 ≤ (T.length:ℝ) by positivity) (Nat.cast_le.mpr hl)
    exact (Nat.cast_le.mpr (forwardRun_card_le_sinkPreserver dag T)).trans
      ((adaptive V C T).trans (mul_le_mul_of_nonneg_left hmono (zero_le_one.trans hK)))
  have emptyBound (q : ℕ) : 0 ≤ (2+512*(3*K+1))*pairwiseRate a b (ε n) n q := by
    apply mul_nonneg (by linarith only [hK]) (pairwiseRate_nonneg (by positivity) (by positivity))
  have edgeBound {H : Arcs V} {q : ℕ} (hn : 0 < n) (hH : H.card ≤ 2*n+512*F q) :
      (H.card:ℝ) ≤ (2+512*(3*K+1))*pairwiseRate a b (ε n) n q := by
    let R := pairwiseRate a b (ε n) (n:ℝ) q
    have nR : (n:ℝ) ≤ R := by
      have l : 0 ≤ (n:ℝ)^(a+ε n)*(q:ℝ)^(2-2*a) := by positivity
      have r : 0 ≤ (n:ℝ)^(2-2*b+ε n)*(q:ℝ)^b := by positivity
      dsimp [R,pairwiseRate]
      linarith only [l,r]
    have hFR : (F q:ℝ) ≤ (3*K+1)*R := pairwiseBudget_le_rate hn hK3
    have hHR : (H.card:ℝ) ≤ 2*(n:ℝ)+512*(F q:ℝ) := by exact_mod_cast hH
    change (H.card:ℝ) ≤ (2+512*(3*K+1))*R
    linarith only [hFR,hHR,nR]
  refine ⟨?_,?_,fun D E h => plannedArcs_prefix (indexedPairPath G) h⟩
  · intro p D length_le
    obtain ⟨sub,correct⟩ := plannedArcs_correct G (fun _ => knownPairPath G p) D
      (fun i => knownPairPath_valid G p (D.get i))
    refine ⟨sub,correct,?_⟩
    cases D with
    | nil => simpa [plannedArcs] using emptyBound p
    | cons d ds =>
      have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨d.1⟩
      have hp : 0 < p := (List.length_pos_iff.mpr (List.cons_ne_nil _ _)).trans_le length_le
      apply edgeBound hn
      apply (knownPairPath_card G hp (d :: ds) length_le).trans
      apply Nat.add_le_add_left _ _
      exact (Nat.mul_le_mul_left _ (envelope p hp)).trans (Nat.mul_le_mul_right _ (by norm_num))
  · intro D
    obtain ⟨sub,correct⟩ := plannedArcs_correct G (indexedPairPath G) D
      (fun i => indexedPairPath_valid G i (D.get i))
    refine ⟨sub,correct,?_⟩
    cases D with
    | nil => simpa [plannedArcs] using emptyBound 0
    | cons d ds =>
      have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨d.1⟩
      apply edgeBound hn
      exact indexedPairPath_card G _ F envelope (pairwiseBudget_dyadic_sum hn ha₁ hb₀ (he n) hK3)
        (fun _ hp => pairwiseBudget_final_quota hn hp ha₀ ha₁ hb₀ hb₁ hK3)

/-- The rounded pairwise rate of Theorem 5 for both executable path assignments. -/
theorem theorem5_pairwise_rounded :
    ∃ K > 0, PairwiseNonAdaptiveBound.{v} (fun n p =>
      K*((n:ℝ)+(n:ℝ)^(18/25:ℝ)*(p:ℝ)^(14/25:ℝ)+(n:ℝ)^(3/5:ℝ)*(p:ℝ)^(7/10:ℝ))) := by
  obtain ⟨K,hK,bound⟩ := theorem1_rounded.{v}
  let C := max 1 K
  have C1 : 1 ≤ C := le_max_left _ _
  have K_C : K ≤ C := le_max_right _ _
  have adaptive (V : Type v) [LinearOrder V] [Fintype V] (G : Arcs V) (D : List (V × V)) :
      ((sinkPreserver G D).card:ℝ) ≤ C*pairwiseRate (18/25) (7/10) 0 (Fintype.card V) D.length := by
    have h := ((bound V G).2 D).2.2
    have rate : pairwiseRate (18/25) (7/10) 0 (Fintype.card V) D.length =
        (Fintype.card V:ℝ)+(Fintype.card V:ℝ)^(18/25:ℝ)*(D.length:ℝ)^(14/25:ℝ)+
          (Fintype.card V:ℝ)^(3/5:ℝ)*(D.length:ℝ)^(7/10:ℝ) := by
      unfold pairwiseRate
      norm_num
    rw [← rate] at h
    exact h.trans (mul_le_mul_of_nonneg_right K_C (pairwiseRate_nonneg (by positivity) (by positivity)))
  refine ⟨2+512*(3*C+1),by linarith,?_⟩
  have main := theorem5_pairwise_transfer (ε := fun _ => 0) (a := 18/25) (b := 7/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ => le_rfl) C1 adaptive
  have ex₁ : (2:ℝ)-2*(18/25) = 14/25 := by norm_num
  have ex₂ : (2:ℝ)-2*(7/10) = 3/5 := by norm_num
  simpa only [pairwiseRate,add_zero,ex₁,ex₂] using main

open Set Filter
open scoped Topology

/-- Both pairwise modes of Theorem 5 achieve the exact limiting exponent pair.
The slack is used only in the proof of the edge count. -/
theorem theorem5_pairwise_limiting_rate {α : ℝ} (ha : α ∈ Ioo (7/10:ℝ) (701/1000))
    (hz : onlineCubic α = 0) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧ ∃ K > 0,
      PairwiseNonAdaptiveBound.{v} (fun n p => K*((n:ℝ)+
        (n:ℝ)^((2+α)/(3+α)+ε n)*(p:ℝ)^(2/(3+α))+
        (n:ℝ)^(2-2*α+ε n)*(p:ℝ)^α)) := by
  obtain ⟨ε,he,hlim,K,hK,bound⟩ := theorem1_limiting_rate.{v} ha hz
  let a := (2+α)/(3+α)
  let C := max 1 K
  have C1 : 1 ≤ C := le_max_left _ _
  have K_C : K ≤ C := le_max_right _ _
  have den : 0 < 3+α := by linarith [ha.1]
  have hA₀ : 1/2 ≤ a := (le_div_iff₀ den).mpr (by linarith [ha.1])
  have hA₁ : a ≤ 3/4 := (div_le_iff₀ den).mpr (by linarith [ha.2])
  have ex : 2-2*a = 2/(3+α) := by
    dsimp [a]
    field_simp
    ring
  have adaptive (V : Type v) [LinearOrder V] [Fintype V] (G : Arcs V) (D : List (V × V)) :
      ((sinkPreserver G D).card:ℝ) ≤ C*pairwiseRate a α (ε (Fintype.card V)) (Fintype.card V) D.length := by
    have h := ((bound V G).2 D).2.2
    change ((sinkPreserver G D).card:ℝ) ≤ K*((Fintype.card V:ℝ)+
      (Fintype.card V:ℝ)^(a+ε (Fintype.card V))*(D.length:ℝ)^(2/(3+α))+
      (Fintype.card V:ℝ)^(2-2*α+ε (Fintype.card V))*(D.length:ℝ)^α) at h
    rw [← ex] at h
    exact h.trans (mul_le_mul_of_nonneg_right K_C (pairwiseRate_nonneg (by positivity) (by positivity)))
  refine ⟨ε,he,hlim,2+512*(3*C+1),by linarith,?_⟩
  have main := theorem5_pairwise_transfer hA₀ hA₁ (show 1/2 ≤ α by linarith [ha.1])
    (show α ≤ 1 by linarith [ha.2]) he C1 adaptive
  simpa only [pairwiseRate,ex,a] using main

end OnlineReachabilityPreservers
