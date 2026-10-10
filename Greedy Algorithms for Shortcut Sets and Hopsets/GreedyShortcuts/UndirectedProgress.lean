import GreedyShortcuts.UndirectedGreedy

/-! The weighted comparison argument with unordered choices and budgets.
Symmetric reweighting keeps the comparison graph inside the undirected class. -/
namespace GreedyShortcuts.Undirected

open Finset DirectedPaths WeightedPaths
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem candidates_current (G : V → V → Prop) (hG : Symmetric G)
    {H : Finset (Sym2 V)} (hH : H ⊆ candidates G) :
    candidates (augment G (arcs H)) = candidates G := by
  unfold candidates
  rw [WeightedStateProgress.candidates_augment G (arcs H) (arcs_subset_candidates G hG hH)]

/-- With h comparison unordered edges, an actual unordered greedy choice
reduces potential by at least a 1/(4h) fraction. The factor four is explicit. -/
theorem state_progress (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (hw : ∀ s t, w s t = w t s)
    (H : Finset (Sym2 V)) (hH : H ⊆ candidates G) (h B β : ℕ) (hB : 2*B ≤ β)
    (hcompare : ∀ w' : V → V → ℝ≥0, (∀ s t, w' s t = w' t s) →
      ∃ J : Finset (Sym2 V), J ⊆ candidates (augment G (arcs H)) ∧ J.card ≤ h ∧
        ∀ s t, Reachable (augment G (arcs H)) s t →
          hopDistance (augment (augment G (arcs H)) (arcs J))
            (augmentWeight (augment G (arcs H)) w' (arcs J)) s t ≤ B)
    (hpos : 0 < potential G w β H) :
    ∃ e ∈ candidates G, potential G w β H ≤
      (4*h) * (potential G w β H - potential G w β (insert e H)) := by
  have hA := arcs_subset_candidates G hG hH
  have hG' := augment_symmetric G hG H
  obtain ⟨w',hw',_,hc⟩ := exists_symmetric_minhop_reweighting (augment G (arcs H))
    (augmentWeight G w (arcs H)) (augmentWeight_symmetric G w hG hw H)
  obtain ⟨J,hJ,hcard,hbound⟩ := hcompare w' hw'
  have hAJ := arcs_subset_candidates _ hG' hJ
  obtain ⟨d,hd,hdrop⟩ := WeightedStateProgress.transfer_comparison (augment G (arcs H))
    (augmentWeight G w (arcs H)) w' hc (arcs J) hAJ B β hB hbound
    (by simpa only [potential, WeightedStateProgress.potential_current G w β (arcs H) hA] using hpos)
  have heJ : s(d.1,d.2) ∈ J := (mem_arcs J d.1 d.2).mp hd
  have he : s(d.1,d.2) ∈ candidates G := by
    rw [← candidates_current G hG hH]
    exact hJ heJ
  have hdC : d ∈ DirectedPaths.candidates G := by
    rw [← WeightedStateProgress.candidates_augment G (arcs H) hA]
    exact hAJ hd
  rw [WeightedStateProgress.potential_current G w β (arcs H) hA,
    WeightedStateProgress.potential_current_insert G w β (arcs H) hA d] at hdrop
  have hmono := WeightedGreedy.potential_mono G w β (Finset.insert_subset hdC hA)
    (arcs_subset_candidates G hG (Finset.insert_subset he hH)) (insert_arc_subset H d)
  have hsize : 2 * (arcs J).card ≤ 4*h := by
    have ha := arcs_card J
    omega
  refine ⟨s(d.1,d.2),he,hdrop.trans ?_⟩
  exact Nat.mul_le_mul hsize (Nat.sub_le_sub_left hmono _)

end GreedyShortcuts.Undirected
