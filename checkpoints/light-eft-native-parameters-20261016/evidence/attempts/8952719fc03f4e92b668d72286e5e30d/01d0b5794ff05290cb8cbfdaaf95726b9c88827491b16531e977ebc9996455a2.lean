import LightEFTSpanners.NativePaperParameters

/-! First native heavy/light bridge: distinct seed and residual blocker caps
for the same actual traced family. No residual-cap sampling bound is asserted. -/
namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E I : Type*}
attribute [local instance] Classical.propDecidable

/-- Only blockers in H can meet a host whose IDs are contained in H. -/
theorem native_host_seed_restriction (U H : Finset E) (T : I → Finset E)
    (block : E → Finset E) (hT : ∀ i, T i ⊆ H) :
    hostCandidates U T block = hostCandidates U T (fun e => block e ∩ H) := by
  classical
  funext i
  ext e
  simp only [hostCandidates,mem_filter]
  constructor
  · rintro ⟨he,hd⟩
    exact ⟨he,hd.mono_right inter_subset_left⟩
  · rintro ⟨he,hd⟩
    refine ⟨he,Finset.disjoint_left.mpr ?_⟩
    intro d hdT hdB
    exact Finset.disjoint_left.mp hd hdT (mem_inter.mpr ⟨hdB,hT i hdT⟩)

/-- Host multiplicity uses the seed cap b, independently of any sampling cap. -/
theorem native_seed_candidate_multiplicity [Fintype I] (U H : Finset E) (T : I → Finset E)
    (block : E → Finset E) (b h : ℕ) (hT : ∀ i, T i ⊆ H)
    (hcount : 2*b+h ≤ Fintype.card I) (hcap : ∀ e ∈ U, (block e ∩ H).card ≤ b)
    (hcong : ∀ e, (univ.filter fun i => e ∈ T i).card ≤ 2) {e : E} (he : e ∈ U) :
    h ≤ (HostCounting.hosts univ (hostCandidates U T block) e).card := by
  classical
  rw [native_host_seed_restriction U H T block hT]
  exact candidate_multiplicity U T (fun e => block e ∩ H) b h hcount hcap hcong he

theorem native_seed_weight_multiplicity [Fintype I] (w : E → ℝ≥0)
    (U H : Finset E) (T : I → Finset E) (block : E → Finset E) (b h : ℕ)
    (hT : ∀ i, T i ⊆ H) (hcount : 2*b+h ≤ Fintype.card I)
    (hcap : ∀ e ∈ U, (block e ∩ H).card ≤ b)
    (hcong : ∀ e, (univ.filter fun i => e ∈ T i).card ≤ 2) :
    (h : ℝ)*(totalWeight w U : ℝ) ≤
      ∑ i, (totalWeight w (hostCandidates U T block i) : ℝ) := by
  classical
  rw [native_host_seed_restriction U H T block hT]
  exact candidate_weight_multiplicity w U T (fun e => block e ∩ H) b h hcount hcap hcong

/-- The light side's large residual set forces a smaller seed blocker cap. -/
theorem native_light_seed_cap [DecidableEq E] (B H : Finset E) (f r : ℕ)
    (hcap : B.card ≤ f) (hlight : ¬ (B \ H).card ≤ r) :
    (B ∩ H).card ≤ f-r := by
  have h := card_inter_add_card_sdiff B H
  omega

/-- Exact disjoint weight accounting on original IDs; no endpoint projection. -/
theorem native_heavy_light_weight_partition (w : E → ℝ≥0) (U H : Finset E)
    (block : E → Finset E) (r : ℕ) :
    totalWeight w (U.filter fun e => (block e \ H).card ≤ r) +
      totalWeight w (U.filter fun e => ¬ (block e \ H).card ≤ r) = totalWeight w U := by
  classical
  exact sum_filter_add_sum_filter_not _ _ _

/-- For one fixed actual traced family at q=2f, every candidate has a host.
Light candidates have 2r+1 hosts; heavy candidates have residual cap r.
This is counting, not a native square-root weight estimate. -/
theorem native_traced_heavy_light_counts [DecidableEq E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {f : ℕ}
    {T : Fin (2*f+1) → Finset E} (hb : SeedForestBudget G w H (2*f) T)
    (t : ℝ≥0) (es : List E) (hsort : es.Pairwise (fun e d => w d ≤ w e))
    (r : ℕ) (hrf : r ≤ f) :
    ∃ block : E → Finset E, TracedBlockers G w t f H es block ∧
      ∀ e ∈ nativeGreedy G w t f H es \ H,
        1 ≤ (HostCounting.hosts univ (hostCandidates (nativeGreedy G w t f H es \ H) T block) e).card ∧
        ((block e \ H).card ≤ r ∨
          ((block e ∩ H).card ≤ f-r ∧
            2*r+1 ≤ (HostCounting.hosts univ (hostCandidates (nativeGreedy G w t f H es \ H) T block) e).card)) := by
  classical
  obtain ⟨block,hblock,_⟩ := exists_traced_blockers G w t f H es hsort
  let U := nativeGreedy G w t f H es \ H
  refine ⟨block,hblock,?_⟩
  intro e he
  have hc : ∀ d ∈ U, (block d).card ≤ f := fun d hd => (hblock.sampling d hd).1
  refine ⟨candidate_multiplicity U T block f 1 (by simp) hc hb.congestion he,?_⟩
  by_cases hres : (block e \ H).card ≤ r
  · exact Or.inl hres
  · right
    have hs := native_light_seed_cap (block e) H f r (hc e he) hres
    refine ⟨hs,?_⟩
    have hi : ∀ i, Disjoint (T i) (block e ∩ H) ↔ Disjoint (T i) (block e) := by
      intro i
      constructor
      · intro hd
        apply Finset.disjoint_left.mpr
        intro d hdT hdB
        exact Finset.disjoint_left.mp hd hdT (mem_inter.mpr ⟨hdB,hb.subset i hdT⟩)
      · exact fun hd => hd.mono_right inter_subset_left
    have hn := HostCounting.two_congestion_hosts univ T (block e ∩ H) (f-r) (2*r+1)
      (by simp; omega) hs (fun d _ => hb.congestion d)
    have heq : (univ.filter fun i => Disjoint (T i) (block e ∩ H)) =
        HostCounting.hosts univ (hostCandidates U T block) e := by
      ext i
      simp only [mem_filter,mem_univ,true_and,HostCounting.hosts,hostCandidates]
      have heU : e ∈ U := he
      simp [heU,hi]
    rwa [heq] at hn

end LightEFTSpanners.NativeWeighted
