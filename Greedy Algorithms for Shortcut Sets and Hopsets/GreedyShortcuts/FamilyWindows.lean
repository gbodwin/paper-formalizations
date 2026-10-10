import GreedyShortcuts.FiniteWindows

/-! Instantiation of suffix-window incidence counting for any finite family
of finite vertex sequences. The graph/path application is separate. -/
namespace GreedyShortcuts.FamilyWindows

open Finset FiniteWindows
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

abbrev Slots (m : I → ℕ) := Σ i, Fin (m i)

def point (m : I → ℕ) (vertex : I → ℕ → V) (x : Slots m) : V := vertex x.1 x.2.val

def deg (m : I → ℕ) (vertex : I → ℕ → V) (v : V) : ℕ :=
  degree (Finset.univ : Finset (Slots m)) (point m vertex) v

def windowScore (m : I → ℕ) (vertex : I → ℕ → V) (b : ℕ)
    (x : Slots (fun i => m i + b - 1)) : ℕ :=
  score (m x.1) b (fun j => deg m vertex (vertex x.1 j)) x.2.val

theorem sum_slots (m : I → ℕ) (f : I → ℕ → ℕ) :
    (∑ x : Slots m, f x.1 x.2.val) = ∑ i, ∑ j ∈ Finset.range (m i), f i j := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact Fin.sum_univ_eq_sum_range (f i) (m i)

theorem window_count (m : I → ℕ) (b : ℕ) (hm : ∀ i, b ≤ m i) :
    Fintype.card (Slots (fun i => m i + b - 1)) ≤ 2 * Fintype.card (Slots m) := by
  simp only [Slots, Fintype.card_sigma, Fintype.card_fin, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => window_count_le (m i) b (hm i))

theorem window_total (m : I → ℕ) (vertex : I → ℕ → V) (b : ℕ) :
    (∑ x : Slots (fun i => m i + b - 1), windowScore m vertex b x) =
      b * ∑ x : Slots m, deg m vertex (point m vertex x) := by
  change (∑ x : Slots (fun i => m i + b - 1),
    score (m x.1) b (fun j => deg m vertex (vertex x.1 j)) x.2.val) = _
  rw [sum_slots (fun i => m i + b - 1)
    (fun i a => score (m i) b (fun j => deg m vertex (vertex i j)) a)]
  simp_rw [sum_scores]
  rw [← Finset.mul_sum]
  congr 1
  exact (sum_slots m (fun i j => deg m vertex (vertex i j))).symm

/-- One actual truncated window has incidence score proportional to the
number of all family positions divided by the number of possible vertices. -/
theorem exists_window (m : I → ℕ) (vertex : I → ℕ → V) (b : ℕ)
    (hb : 0 < b) (hm : ∀ i, b ≤ m i) (hslots : 0 < Fintype.card (Slots m)) :
    ∃ x : Slots (fun i => m i + b - 1),
      b * Fintype.card (Slots m) ≤ 2 * Fintype.card V * windowScore m vertex b x := by
  obtain ⟨x, _, hx⟩ := exists_high_score (Finset.univ : Finset (Slots m))
    (point m vertex) (Finset.univ : Finset (Slots (fun i => m i + b - 1)))
    (windowScore m vertex b) b hb (by simpa using hslots)
    (by simpa using window_count m b hm) (by rw [window_total]; rfl)
  exact ⟨x, by simpa using hx⟩

end GreedyShortcuts.FamilyWindows
