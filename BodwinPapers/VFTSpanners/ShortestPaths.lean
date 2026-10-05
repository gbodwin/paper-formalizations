import BodwinPapers.VFTSpanners.Distance
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

namespace BodwinPapers.VFTSpanners
open SimpleGraph Finset
open scoped ENNReal
variable {V : Type*}
attribute [local instance] Classical.propDecidable

/-- Removing terms of a sum of nonnegative edge weights cannot increase it. -/
theorem sublist_weight_le (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {l r : List (Sym2 V)} (h : l.Sublist r) : (l.map w).sum ≤ (r.map w).sum := by
  induction h with
  | slnil => simp
  | cons a h ih => simp only [List.map_cons, List.sum_cons]; linarith [hw a]
  | cons_cons a h ih => simp only [List.map_cons, List.sum_cons]; linarith

variable [DecidableEq V]

/-- Loop erasure preserves endpoints and does not increase nonnegative cost. -/
theorem walkWeight_bypass_le (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    walkWeight w p.bypass ≤ walkWeight w p :=
  sublist_weight_le w hw p.edges_bypass_sublist_edges

variable [Fintype V]

/-- Finite nonnegative weighted graphs have a minimum-weight fault-avoiding
walk whenever any such walk exists. This also covers zero-weight edges. -/
theorem exists_minimum_walk (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (F : Finset V) (u v : V)
    (hex : ∃ p : G.Walk u v, Avoids F p) :
    ∃ q : G.Walk u v, Avoids F q ∧
      ∀ p : G.Walk u v, Avoids F p → walkWeight w q ≤ walkWeight w p := by
  classical
  let P : Finset (G.Path u v) := univ.filter (fun p => Avoids F p.val)
  have hpath (p : G.Walk u v) (hp : Avoids F p) : p.toPath ∈ P := by
    exact mem_filter.mpr ⟨mem_univ _,fun x hx => hp x (p.support_toPath_subset_support hx)⟩
  have hnon : P.Nonempty := by
    obtain ⟨p,hp⟩ := hex
    exact ⟨p.toPath,hpath p hp⟩
  obtain ⟨q,hq,hmin⟩ := exists_min_image P (fun p => walkWeight w p.val) hnon
  refine ⟨q.val,(mem_filter.mp hq).2,?_⟩
  intro p hp
  exact (hmin p.toPath (hpath p hp)).trans (walkWeight_bypass_le w hw p)

theorem exists_walk_attaining_distance (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (F : Finset V) (u v : V)
    (hex : ∃ p : G.Walk u v, Avoids F p) :
    ∃ q : G.Walk u v, Avoids F q ∧
      faultDistance G w F u v = ENNReal.ofReal (walkWeight w q) := by
  obtain ⟨q,hq,hmin⟩ := exists_minimum_walk G w hw F u v hex
  refine ⟨q,hq,le_antisymm ?_ ?_⟩
  · exact iInf_le (fun p : {p : G.Walk u v // Avoids F p} =>
      ENNReal.ofReal (walkWeight w p.val)) ⟨q,hq⟩
  · exact le_iInf fun p => ENNReal.ofReal_le_ofReal (hmin p.val p.property)

/-- The walk-existence test used in `greedyEdges` is exactly a shortest-distance
test; it is not an assumption about shortest paths or a substitute algorithm. -/
theorem distance_le_iff_exists_walk (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (F : Finset V) (u v : V) (t : ℝ) (ht : 0 ≤ t) :
    faultDistance G w F u v ≤ ENNReal.ofReal t ↔
      ∃ p : G.Walk u v, Avoids F p ∧ walkWeight w p ≤ t := by
  classical
  constructor
  · intro hd
    have hex : ∃ p : G.Walk u v, Avoids F p := by
      by_contra hn
      have : IsEmpty {p : G.Walk u v // Avoids F p} :=
        ⟨fun p => hn ⟨p.val,p.property⟩⟩
      have htop : faultDistance G w F u v = ⊤ := by simp [faultDistance]
      rw [htop, top_le_iff] at hd
      exact ENNReal.ofReal_ne_top hd
    obtain ⟨q,hq,heq⟩ := exists_walk_attaining_distance G w hw F u v hex
    rw [heq] at hd
    exact ⟨q,hq,(ENNReal.ofReal_le_ofReal_iff ht).mp hd⟩
  · rintro ⟨p,hp,hcost⟩
    exact (iInf_le (fun p : {p : G.Walk u v // Avoids F p} =>
      ENNReal.ofReal (walkWeight w p.val)) ⟨p,hp⟩).trans (ENNReal.ofReal_le_ofReal hcost)

/-- Precise correspondence of the formal greedy test to Algorithm 1. -/
theorem covered_iff_distance (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (k f : ℕ) (e : Sym2 V) :
    Covered G w k f e ↔ ∀ u v, s(u,v) = e →
      ∀ F : Finset V, F.card ≤ f → u ∉ F → v ∉ F →
        faultDistance G w F u v ≤ ENNReal.ofReal ((k : ℝ)*w e) := by
  simp only [Covered, distance_le_iff_exists_walk G w hw _ _ _ _
    (mul_nonneg (Nat.cast_nonneg _) (hw e))]

end BodwinPapers.VFTSpanners
