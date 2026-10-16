import LightEFTSpanners.NativeSeedForests
import LightEFTSpanners.HostCounting

namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E I : Type*}
attribute [local instance] Classical.propDecidable

/-- The existing incidence identity applies to original IDs without converting
them to endpoint pairs. Congestion two and nonnegative weights give the budget. -/
theorem forest_weight_le_two_seed [Fintype I] (w : E → ℝ≥0) (H : Finset E)
    (B : I → Finset E) (hB : ∀ i, B i ⊆ H)
    (hcong : ∀ e, (univ.filter fun i => e ∈ B i).card ≤ 2) :
    (∑ i, totalWeight w (B i)) ≤ 2 * totalWeight w H := by
  classical
  have hr : (∑ i, ∑ e ∈ B i, (w e : ℝ)) ≤ 2 * ∑ e ∈ H, (w e : ℝ) := by
    rw [HostCounting.weighted_incidence univ H B (fun e => (w e : ℝ)) (fun i _ => hB i), mul_sum]
    apply sum_le_sum
    intro e _
    have hc : ((HostCounting.hosts univ B e).card : ℝ) ≤ 2 := by
      change ((univ.filter fun i => e ∈ B i).card : ℝ) ≤ 2
      exact_mod_cast hcong e
    exact mul_le_mul_of_nonneg_right hc (NNReal.coe_nonneg _)
  unfold totalWeight
  exact_mod_cast hr

/-- A concrete original-ID forest family with its derived weight budget and
actual omitted-edge walk witnesses. This is constructed below, not assumed as
a substitute for the budget proof. -/
structure SeedForestBudget (G : Graph V E) (w : E → ℝ≥0) (H : Finset E) (q : ℕ)
    (B : Fin (q+1) → Finset E) : Prop where
  subset : ∀ c, B c ⊆ H
  forest : ∀ c, ∀ e ∈ (G.restrict (B c : Set E)).edgeSet, (G.restrict (B c : Set E)).IsBridge e
  congestion : ∀ e, (univ.filter fun c => e ∈ B c).card ≤ 2
  weight_le : (∑ c, totalWeight w (B c)) ≤ 2 * totalWeight w H
  paths : ∀ c (u v : G.vertexSet) e, G.IsLink e u.val v.val → e ∉ H → Nonempty (Walk G (B c) ∅ u v)

/-- The genuine seed-to-forest construction supplies the budget internally. -/
theorem exists_seed_forest_budget [Fintype V] [Fintype E] (G : Graph V E)
    (w : E → ℝ≥0) (H : Finset E) (q : ℕ)
    (hH : IsConnectivityPreserver G (inputEdges G) H q) :
    ∃ B : Fin (q+1) → Finset E, SeedForestBudget G w H q B := by
  classical
  obtain ⟨_, _, _, B, hB, hcong, hpaths⟩ := exists_seed_forests G H q hH
  have hsub (c) : (B c).toFinset ⊆ H := fun _ he => (hB c).1 (Set.mem_toFinset.mp he)
  have hc (e) : (univ.filter fun c => e ∈ (B c).toFinset).card ≤ 2 := by
    simpa only [Set.mem_toFinset] using hcong e
  refine ⟨fun c => (B c).toFinset, hsub, ?_, hc, ?_, hpaths⟩
  · intro c
    simpa only [Set.coe_toFinset] using (hB c).2.2
  · exact forest_weight_le_two_seed w H _ hsub hc

/-- Choose an attained minimum native connectivity preserver, then construct
its forests. Their total weight is at most twice that genuine optimum,
including a zero optimum; no division or positivity assertion is involved. -/
theorem exists_minimum_seed_budget [Fintype V] [Fintype E] (G : Graph V E)
    (w : E → ℝ≥0) (q : ℕ) :
    ∃ (H : Finset E) (B : Fin (q+1) → Finset E),
      IsConnectivityPreserver G (inputEdges G) H q ∧
      totalWeight w H = minimumPreserverWeight G w (inputEdges G) q ∧
      (∀ J, IsConnectivityPreserver G (inputEdges G) J q → totalWeight w H ≤ totalWeight w J) ∧
      SeedForestBudget G w H q B ∧
      (∑ c, totalWeight w (B c)) ≤ 2 * minimumPreserverWeight G w (inputEdges G) q := by
  obtain ⟨H,hH,hw,hmin⟩ := minimumPreserverWeight_attained G w (inputEdges G) q
  obtain ⟨B,hB⟩ := exists_seed_forest_budget G w H q hH
  refine ⟨H,B,hH,hw,?_,hB,?_⟩
  · intro J hJ
    rw [hw]
    exact hmin J hJ
  · simpa only [hw] using hB.weight_le

/-- A selected forest disjoint from the faults keeps its original-ID walk. -/
theorem Walk.survives_disjoint {G : Graph V E} {B F : Finset E}
    (h : Disjoint B F) {u v : G.vertexSet} (p : Walk G B ∅ u v) :
    Nonempty (Walk G B F u v) := by
  induction p with
  | nil u => exact ⟨.nil u⟩
  | cons e hl he _ p ih =>
    obtain ⟨r⟩ := ih
    exact ⟨.cons e hl he (fun hf => Finset.disjoint_left.mp h he hf) r⟩

/-- The existing arbitrary-ID host count applies to these constructed native
forests, and every counted unblocked host has a genuine surviving walk.
The coverage requirement 2*f+h <= q+1 remains explicit. -/
theorem SeedForestBudget.good_hosts [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {B : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q B)
    (F : Finset E) (f h : ℕ) (hF : F.card ≤ f) (hcount : 2*f+h ≤ q+1)
    {u v : G.vertexSet} {e : E} (he : G.IsLink e u.val v.val) (homit : e ∉ H) :
    h ≤ (univ.filter fun c => Disjoint (B c) F).card ∧
      ∀ c ∈ univ.filter (fun c => Disjoint (B c) F), Nonempty (Walk G (B c) F u v) := by
  classical
  constructor
  · apply HostCounting.two_congestion_hosts univ B F f h (by simpa using hcount) hF
    intro d _
    exact hb.congestion d
  · intro c hc
    obtain ⟨p⟩ := hb.paths c u v e he homit
    exact p.survives_disjoint (mem_filter.mp hc).2

/-- This supplies exactly the real-valued congestion premise in the existing
baseline charging algebra. It does not supply a per-host candidate-weight
estimate or a final lightness bound. -/
theorem SeedForestBudget.real_weight_le {G : Graph V E} {w : E → ℝ≥0}
    {H : Finset E} {q : ℕ} {B : Fin (q+1) → Finset E}
    (hb : SeedForestBudget G w H q B) :
    (∑ c, (totalWeight w (B c) : ℝ)) ≤ 2 * (totalWeight w H : ℝ) := by
  exact_mod_cast hb.weight_le

end LightEFTSpanners.NativeWeighted
