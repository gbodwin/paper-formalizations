import LightSpanners.Greedy
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Basic.ENNReal.Real
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

namespace LightSpanners
open SimpleGraph Finset
open scoped ENNReal
variable {V : Type*}

noncomputable def weightedDistance (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (u v : V) : ℝ≥0∞ :=
  ⨅ p : G.Walk u v, ENNReal.ofReal (walkWeight w p)

theorem walkWeight_nonneg (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : 0 ≤ walkWeight w p := by
  induction p with
  | nil => simp
  | cons h p ih => simpa only [walkWeight_cons] using add_nonneg (hw _) ih

theorem sublist_weight_le (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {l r : List (Sym2 V)} (h : l.Sublist r) : (l.map w).sum ≤ (r.map w).sum := by
  induction h with
  | slnil => simp
  | cons a h ih => simp only [List.map_cons, List.sum_cons]; linarith [hw a]
  | cons_cons a h ih => simp only [List.map_cons, List.sum_cons]; linarith

theorem IsSpanner.distance_le {G H : SimpleGraph V} {w : Sym2 V → ℝ}
    {t : ℝ} (h : IsSpanner G H w t) (ht : 0 < t) (u v : V) :
    weightedDistance H w u v ≤ ENNReal.ofReal t * weightedDistance G w u v := by
  unfold weightedDistance
  rw [ENNReal.mul_iInf_of_ne (by simpa using ht) ENNReal.ofReal_ne_top]
  apply le_iInf
  intro p
  obtain ⟨q, hq⟩ := h.2 u v p
  calc
    _ ≤ ENNReal.ofReal (walkWeight w q) := iInf_le _ q
    _ ≤ ENNReal.ofReal (t * walkWeight w p) := ENNReal.ofReal_le_ofReal hq
    _ = _ := ENNReal.ofReal_mul ht.le

variable [DecidableEq V]

theorem walkWeight_bypass_le (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    walkWeight w p.bypass ≤ walkWeight w p :=
  sublist_weight_le w hw p.edges_bypass_sublist_edges

variable [Fintype V]

theorem exists_minimum_walk (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (u v : V) (hex : Nonempty (G.Walk u v)) :
    ∃ q : G.Walk u v, q.IsPath ∧ ∀ p : G.Walk u v, walkWeight w q ≤ walkWeight w p := by
  classical
  obtain ⟨p⟩ := hex
  obtain ⟨q, _, hmin⟩ := exists_min_image (univ : Finset (G.Path u v))
    (fun p => walkWeight w p.val) ⟨p.toPath, mem_univ _⟩
  exact ⟨q.val, q.property, fun p =>
    (hmin p.toPath (mem_univ _)).trans (walkWeight_bypass_le w hw p)⟩

theorem exists_walk_attaining_distance (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (u v : V) (hex : Nonempty (G.Walk u v)) :
    ∃ q : G.Walk u v, q.IsPath ∧
      weightedDistance G w u v = ENNReal.ofReal (walkWeight w q) := by
  obtain ⟨q, hq, hmin⟩ := exists_minimum_walk G w hw u v hex
  exact ⟨q, hq, le_antisymm (iInf_le _ q)
    (le_iInf fun p => ENNReal.ofReal_le_ofReal (hmin p))⟩

theorem distance_le_iff_exists_walk (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (u v : V) (t : ℝ) (ht : 0 ≤ t) :
    weightedDistance G w u v ≤ ENNReal.ofReal t ↔
      ∃ p : G.Walk u v, walkWeight w p ≤ t := by
  classical
  constructor
  · intro hd
    have hex : Nonempty (G.Walk u v) := by
      by_contra hn
      have : IsEmpty (G.Walk u v) := ⟨fun p => hn ⟨p⟩⟩
      have htop : weightedDistance G w u v = ⊤ := by simp [weightedDistance]
      rw [htop, top_le_iff] at hd
      exact ENNReal.ofReal_ne_top hd
    obtain ⟨q, _, heq⟩ := exists_walk_attaining_distance G w hw u v hex
    rw [heq] at hd
    exact ⟨q, (ENNReal.ofReal_le_ofReal_iff ht).mp hd⟩
  · rintro ⟨p, hp⟩
    exact (iInf_le _ p).trans (ENNReal.ofReal_le_ofReal hp)

/-- Positive stretch avoids the convention `0 * infinity = 0`. -/
theorem isSpanner_iff_distance (G H : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (t : ℝ) (ht : 0 < t) :
    IsSpanner G H w t ↔ H ≤ G ∧ ∀ u v,
      weightedDistance H w u v ≤ ENNReal.ofReal t * weightedDistance G w u v := by
  constructor
  · intro h
    exact ⟨h.1, h.distance_le ht⟩
  · rintro ⟨hsub, hd⟩
    refine ⟨hsub, fun u v p => ?_⟩
    apply (distance_le_iff_exists_walk H w hw u v _
      (mul_nonneg ht.le (walkWeight_nonneg w hw p))).mp
    rw [ENNReal.ofReal_mul ht.le]
    exact (hd u v).trans (mul_le_mul_right (iInf_le _ p) _)

theorem covered_iff_distance (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (t : ℝ) (ht : 0 ≤ t) (e : Sym2 V) :
    Covered G w t e ↔ ∀ u v, s(u,v) = e →
      weightedDistance G w u v ≤ ENNReal.ofReal (t * w e) := by
  simp only [Covered, distance_le_iff_exists_walk G w hw _ _ _ (mul_nonneg ht (hw e))]

omit [Fintype V] in
theorem greedy_distance_le (w : Sym2 V → ℝ) (t : ℝ) (ht : 1 ≤ t)
    (hw : ∀ e, 0 ≤ w e) (l : List (Sym2 V)) (hl : ∀ e ∈ l, ¬ e.IsDiag)
    (u v : V) :
    weightedDistance (edgeGraph (greedyEdges w t l)) w u v ≤
      ENNReal.ofReal t * weightedDistance (edgeGraph l.toFinset) w u v :=
  (greedy_isSpanner w t ht hw l hl).distance_le (by linarith) u v

end LightSpanners
