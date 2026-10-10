import MinorFreeSpanners.ClusterWalkLift
import MinorFreeSpanners.ClusterEdgeWeights
import MinorFreeSpanners.CycleEdgeRemoval

/-! A short actual quotient cycle is lifted, edge by edge, to an alternative
host walk. Its weight contradicts intrinsic weighted girth. No cycle-lifting
oracle or preserved greedy ordering is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {I V : Type*} [DecidableEq V]
variable {A G B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
namespace ClusterFamily

/-- Graph-level girth of a cluster quotient, with explicit geometric budgets.
The cluster family itself is supplied; constructing a hierarchy remains separate. -/
theorem girth (C : ClusterFamily (I := I) A w D) (hA : A ≤ G) (hB : B ≤ G)
    (r : ℕ) {g L : ℝ} (hG : WeightedGirthAbove G w g)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) (hlight : ∀ e ∈ A.edgeSet, w e < L)
    (hheavy : ∀ e ∈ B.edgeSet, L ≤ w e) (hL : 0 < L) (hD : 0 ≤ D)
    (hbudget : (r:ℝ)*(1+D/L) ≤ g) : GirthAbove (C.graph B) r := by
  classical
  intro a p hp
  by_contra hlong
  have hshort : p.length ≤ r := by omega
  let μ := C.edgeWeight hA hB
  obtain ⟨e,he,hmax⟩ := exists_max_cycle_edge μ p hp
  obtain ⟨i,j,hij,heq,q,hnot,hlen,hsub⟩ := closed_trail_remove_edge p hp.isTrail e he
  obtain ⟨u,hu,v,hv,huv,hwuv⟩ := C.exists_bridge_with_weight hA hB i j hij
  have hwM : w s(u,v) = μ e := by simpa only [μ,heq] using hwuv
  have hML : L ≤ w s(u,v) := hheavy _ ((mem_edgeSet B).mpr huv)
  have hav : ∀ {x y : V} (t : A.Walk x y), s(u,v) ∉ t.edges :=
    fun t => heavy_edge_not_mem hlight hML t
  have hbr : ∀ x y, (C.graph B).Adj x y → s(x,y) ∈ q.edges →
      ∃ b ∈ C.branch x, ∃ c ∈ C.branch y,
        ∃ hbc : G.Adj b c, w s(b,c) ≤ w s(u,v) ∧ s(b,c) ≠ s(u,v) := by
    intro x y hxy hmem
    obtain ⟨b,hb,c,hc,hbc,hweight⟩ := C.exists_bridge_with_weight hA hB x y hxy
    refine ⟨b,hb,c,hc,hB hbc,?_,?_⟩
    · rw [hweight,hwM]
      exact hmax _ (hsub _ hmem)
    · intro hehost
      have hlab := congrArg (Sym2.map (C.minorModel hA hB).branchLabel) hehost
      have hco : s(x,y) = s(i,j) := by
        apply Sym2.map.injective (fun _ _ h => Option.some.inj h)
        simpa only [Sym2.map_mk,(C.minorModel hA hB).branchLabel_eq hb,
          (C.minorModel hA hB).branchLabel_eq hc,(C.minorModel hA hB).branchLabel_eq hu,
          (C.minorModel hA hB).branchLabel_eq hv] using hlab
      apply hnot
      simpa only [hco,heq] using hmem
  obtain ⟨t,htnot,htweight⟩ := C.lift_walk_bounded_on_edges hA (C.graph B)
    (w s(u,v)) s(u,v) hav q hbr hv hu
  have hgap := replacement_walk_gap hG hw (hB huv).symm t
    (by simpa only [Sym2.eq_swap] using htnot)
  simp only [Sym2.eq_swap] at hgap
  have hlenR : (q.length:ℝ)+1 = p.length := by exact_mod_cast hlen
  have hshortR : (p.length:ℝ) ≤ r := by exact_mod_cast hshort
  have hcyclebound : g*w s(u,v) < (p.length:ℝ)*(D+w s(u,v)) := by
    rw [← hlenR]
    nlinarith
  have hupper := mul_le_mul_of_nonneg_right hshortR (show 0 ≤ D+w s(u,v) by linarith)
  have hgr : (r:ℝ) ≤ g := by
    have := mul_nonneg (Nat.cast_nonneg r : (0:ℝ) ≤ r) (div_nonneg hD hL.le)
    nlinarith
  have hbudget' : (r:ℝ)*(L+D) ≤ g*L := by
    have hb := mul_le_mul_of_nonneg_right hbudget hL.le
    have he : (r:ℝ)*(1+D/L)*L = r*(L+D) := by field_simp [hL.ne']
    rwa [he] at hb
  have hscale := mul_le_mul_of_nonneg_left hML (sub_nonneg.mpr hgr)
  nlinarith

end ClusterFamily
end MinorFreeSpanners
