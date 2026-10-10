import GreedyShortcuts.SuffixIncidence
import GreedyShortcuts.IntervalCharging

/-! Actual suffix intersections of canonical DAG paths are intervals. -/
namespace GreedyShortcuts.SuffixIntersections

open scoped NNReal
open Finset SimpleGraph DirectedPaths CanonicalSegments SuffixWindowPath SuffixIncidence
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem offset_le {s t : V} (p : DWalk s t) (hm : 0 < suffixSize p) :
    suffixOffset p ≤ p.length := by
  have hs : suffixSize p ≤ p.length+1 := by dsimp [suffixSize]; omega
  dsimp [suffixOffset]
  omega

theorem vertices_eq_segment {s t : V} (p : DWalk s t) (hm : 0 < suffixSize p) :
    vertices p = (segment p (suffixOffset p) p.length (offset_le p hm)).support.toFinset := by
  rw [segment_support p (offset_le p hm) le_rfl]
  ext v
  simp only [vertices,Finset.mem_image,Finset.mem_range,Finset.mem_Icc]
  have hs : suffixSize p ≤ p.length+1 := by dsimp [suffixSize]; omega
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨suffixOffset p+j,⟨by omega,index_bound p hj⟩,rfl⟩
  · rintro ⟨k,⟨hk,hk'⟩,rfl⟩
    refine ⟨k-suffixOffset p,?_,?_⟩
    · dsimp [suffixOffset] at *
      omega
    · rw [Nat.add_sub_of_le hk]

/-- Positions on the base path lying in the last quarter of another path. -/
def indices {s t u v : V} (q : DWalk s t) (p : DWalk u v) : Finset ℕ :=
  (Finset.range (q.length+1)).filter (fun j => q.getVert j ∈ vertices p)

theorem indices_card {s t u v : V} {q : DWalk s t} (hq : q.IsPath) (p : DWalk u v) :
    (indices q p).card = (q.support.toFinset ∩ vertices p).card := by
  apply Finset.card_bij (fun j _ => q.getVert j)
  · intro j hj
    exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr (q.getVert_mem_support j),
      (Finset.mem_filter.mp hj).2⟩
  · intro i hi j hj he
    have hiL : i ≤ q.length := by
      have h : i < q.length+1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      omega
    have hjL : j ≤ q.length := by
      have h : j < q.length+1 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      omega
    exact hq.getVert_injOn hiL hjL he
  · intro x hx
    obtain ⟨j,hjx,hj⟩ := Walk.mem_support_iff_exists_getVert.mp
      (List.mem_toFinset.mp (Finset.mem_inter.mp hx).1)
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩,hjx⟩
    simpa only [hjx] using (Finset.mem_inter.mp hx).2

theorem indices_convex {G : V → V → Prop} (hG : Acyclic G)
    {w : V → V → ℝ≥0} {s t u v : V} {q : DWalk s t} {p : DWalk u v}
    (hq : Optimal G w q) (hp : Optimal G w p) :
    IntervalCharging.Convex (indices q p) := by
  intro a ha b hb c hac hcb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have hm : 0 < suffixSize p := by
    obtain ⟨j,hj,_⟩ := Finset.mem_image.mp ha'.2
    have := Finset.mem_range.mp hj
    omega
  have haQ : q.getVert a ∈ (segment p (suffixOffset p) p.length (offset_le p hm)).support := by
    simpa only [vertices_eq_segment p hm,List.mem_toFinset] using ha'.2
  have hbQ : q.getVert b ∈ (segment p (suffixOffset p) p.length (offset_le p hm)).support := by
    simpa only [vertices_eq_segment p hm,List.mem_toFinset] using hb'.2
  have hbl : b ≤ q.length := by have := Finset.mem_range.mp hb'.1; omega
  have hh := intersection_convex hG hq (optimal_segment hp _ _ (offset_le p hm))
    hac hcb hbl haQ hbQ
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩
  simpa only [vertices_eq_segment p hm,List.mem_toFinset] using hh

/-- The interval lemma now applies to the actual two-path intersection. -/
theorem heavy_pairedStarts {G : V → V → Prop} (hG : Acyclic G)
    {w : V → V → ℝ≥0} {s t u v : V} {q : DWalk s t} {p : DWalk u v}
    (hq : Optimal G w q) (hp : Optimal G w p) (σ : ℕ) (hσ : 8 ≤ σ)
    (hheavy : σ ≤ (q.support.toFinset ∩ vertices p).card) :
    (q.support.toFinset ∩ vertices p).card ≤
      2*(IntervalCharging.pairedStarts (indices q p) (σ/2)).card := by
  rw [← indices_card hq.2.1 p] at hheavy ⊢
  exact IntervalCharging.pairedStarts_heavy _ (indices_convex hG hq hp) σ hσ hheavy

end GreedyShortcuts.SuffixIntersections
