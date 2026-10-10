import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Actual finite incidence counting for the host-tree argument. The packing
itself is not assumed to have been constructed by these lemmas. -/
namespace LightEFTSpanners.HostCounting
open Finset
variable {E I : Type*} [DecidableEq E] [DecidableEq I]

def hosts (indices : Finset I) (tree : I → Finset E) (e : E) : Finset I :=
  indices.filter (fun i => e ∈ tree i)

def badHosts (indices : Finset I) (tree : I → Finset E) (B : Finset E) : Finset I :=
  B.biUnion (hosts indices tree)

@[simp] theorem mem_badHosts (indices : Finset I) (tree : I → Finset E)
    (B : Finset E) (i : I) : i ∈ badHosts indices tree B ↔
    i ∈ indices ∧ ¬ Disjoint (tree i) B := by
  simp only [badHosts, mem_biUnion, hosts, mem_filter, not_disjoint_iff]
  constructor
  · rintro ⟨e,heB,hi,heT⟩
    exact ⟨hi,e,heT,heB⟩
  · rintro ⟨hi,e,heT,heB⟩
    exact ⟨e,heB,hi,heT⟩

theorem badHosts_card_le (indices : Finset I) (tree : I → Finset E)
    (B : Finset E) (c : ℕ) (h : ∀ e ∈ B, (hosts indices tree e).card ≤ c) :
    (badHosts indices tree B).card ≤ B.card * c := by
  calc
    _ ≤ ∑ e ∈ B, (hosts indices tree e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ B, c := sum_le_sum h
    _ = _ := by simp

theorem goodHosts_count (indices : Finset I) (tree : I → Finset E)
    (B : Finset E) (c : ℕ) (h : ∀ e ∈ B, (hosts indices tree e).card ≤ c) :
    indices.card ≤ (indices.filter (fun i => Disjoint (tree i) B)).card + B.card * c := by
  have hbad := badHosts_card_le indices tree B c h
  have heq : indices.filter (fun i => ¬ Disjoint (tree i) B) = badHosts indices tree B := by
    ext i; simp
  have hh := card_filter_add_card_filter_not (s := indices) (p := fun i => Disjoint (tree i) B)
  rw [heq] at hh
  omega

/-- Congestion two and 2f+h candidate trees yield at least h unblocked hosts. -/
theorem two_congestion_hosts (indices : Finset I) (tree : I → Finset E)
    (B : Finset E) (f h : ℕ) (hcount : 2*f+h ≤ indices.card) (hcap : B.card ≤ f)
    (hcong : ∀ e ∈ B, (hosts indices tree e).card ≤ 2) :
    h ≤ (indices.filter (fun i => Disjoint (tree i) B)).card := by
  have hh := goodHosts_count indices tree B 2 hcong
  omega

/-- Every original edge is counted with its actual multiplicity. -/
theorem weighted_incidence (indices : Finset I) (edges : Finset E)
    (assigned : I → Finset E) (w : E → ℝ)
    (hsub : ∀ i ∈ indices, assigned i ⊆ edges) :
    (∑ i ∈ indices, ∑ e ∈ assigned i, w e) =
      ∑ e ∈ edges, (hosts indices assigned e).card * w e := by
  calc
    _ = ∑ i ∈ indices, ∑ e ∈ edges, if e ∈ assigned i then w e else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [← sum_filter]
      congr 1
      ext e
      simp only [mem_filter]
      exact ⟨fun he => ⟨hsub i hi he,he⟩,And.right⟩
    _ = ∑ e ∈ edges, ∑ i ∈ indices, if e ∈ assigned i then w e else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro e he
      rw [← sum_filter]
      simp [hosts]

/-- Charging only the hosted (non-seed) edges leaves the seed weight intact. -/
theorem baseline_charging {seedWeight addedWeight hostWeight treeWeight L : ℝ}
    {f h : ℕ} (hseed : 0 < seedWeight) (hh : 0 < h)
    (hadded : 0 ≤ addedWeight) (hL : 0 ≤ L)
    (multiplicity : (h : ℝ) * addedWeight ≤ hostWeight)
    (perHost : hostWeight ≤ 4 * (f : ℝ) * L * treeWeight)
    (congestion : treeWeight ≤ 2 * seedWeight) :
    (seedWeight + addedWeight) / seedWeight ≤ 1 + 8 * (f : ℝ) * L / h := by
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hf : 0 ≤ (f : ℝ) := by positivity
  have hc := mul_le_mul_of_nonneg_left congestion (show 0 ≤ 4*(f:ℝ)*L by positivity)
  have hsum : (h : ℝ) * addedWeight ≤ 8 * (f : ℝ) * L * seedWeight := by nlinarith
  apply (div_le_iff₀ hseed).mpr
  have ht : addedWeight ≤ (8*(f:ℝ)*L*seedWeight)/(h:ℝ) := (le_div_iff₀ hhR).mpr (by nlinarith)
  field_simp
  nlinarith

end LightEFTSpanners.HostCounting
