import LightEFTSpanners.Basic
import LightSpanners.Construction

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*} [DecidableEq V]

/-- Seeded Algorithm 1. The tail is processed first, so a nonincreasing input
list implements nondecreasing edge-weight order. The test quantifies all finite
fault sets; `test_restrict_faults` below proves equivalence to current-edge faults. -/
noncomputable def greedyEdges (seed : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) :
    List (Sym2 V) → Finset (Sym2 V)
  | [] => seed
  | e :: es => by
    classical
    exact let E := greedyEdges seed w t f es
      if FTCovered (edgeGraph E) w t f e then E else insert e E

theorem greedy_seed_subset (seed : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (f : ℕ) (l : List (Sym2 V)) : seed ⊆ greedyEdges seed w t f l := by
  classical
  induction l with
  | nil => exact subset_rfl
  | cons e es ih =>
    simp only [greedyEdges]
    split_ifs
    · exact ih
    · exact ih.trans (subset_insert _ _)

theorem greedy_subset (seed : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (f : ℕ) (l : List (Sym2 V)) : greedyEdges seed w t f l ⊆ seed ∪ l.toFinset := by
  classical
  induction l with
  | nil => simp [greedyEdges]
  | cons e es ih =>
    simp only [greedyEdges]
    split_ifs
    · exact ih.trans (by intro d hd; simpa using Or.inr hd)
    · intro d hd
      rcases mem_insert.mp hd with rfl | hd
      · simp
      · have hh := ih hd
        simp only [mem_union, List.mem_toFinset] at *
        rcases hh with hh | hh
        · exact Or.inl hh
        · exact Or.inr (List.mem_cons_of_mem e hh)

theorem greedy_covered (seed : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (f : ℕ) (ht : 1 ≤ t) (hw : ∀ e, 0 ≤ w e) (l : List (Sym2 V))
    (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    ∀ e ∈ l, FTCovered (edgeGraph (greedyEdges seed w t f l)) w t f e := by
  classical
  induction l with
  | nil => simp
  | cons e es ih =>
    have hi := ih (fun d hd => hl d (by simp [hd]))
    intro d hd
    simp only [greedyEdges]
    split_ifs with hc
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact hc
      · exact hi d hd
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact ftCovered_of_mem ht hw ((mem_edgeGraph _ _).mpr
          ⟨mem_insert_self _ _, hl d (by simp)⟩)
      · exact ftCovered_mono (edgeGraph_mono (subset_insert _ _)) (hi d hd)

/-- Theorem 18 with the sufficient edge inequality corrected to `≤`.
The seed can be arbitrary: optimal connectivity is needed only for lightness. -/
theorem greedy_isEFTSpanner (seed : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (f : ℕ) (ht : 1 ≤ t) (hw : ∀ e, 0 ≤ w e) (l : List (Sym2 V))
    (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    IsEFTSpanner (edgeGraph (seed ∪ l.toFinset))
      (edgeGraph (greedyEdges seed w t f l)) w t f := by
  apply ftCovered_edges_spanner (edgeGraph_mono (greedy_subset seed w t f l))
  intro e he
  obtain ⟨he, hnd⟩ := (mem_edgeGraph _ _).mp he
  rcases mem_union.mp he with he | he
  · exact ftCovered_of_mem ht hw ((mem_edgeGraph _ _).mpr
      ⟨greedy_seed_subset seed w t f l he, hnd⟩)
  · exact greedy_covered seed w t f ht hw l hl e (List.mem_toFinset.mp he)

/-- Normalization of faults to current graph edges does not alter the test. -/
theorem test_restrict_faults (E : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f : ℕ) (e : Sym2 V) : FTCovered (edgeGraph E) w t f e ↔
    ∀ F : Finset (Sym2 V), F ⊆ E → F.card ≤ f → e ∉ F →
      Covered (afterFaults (edgeGraph E) F) w t e := by
  classical
  constructor
  · intro h F _ hF heF
    exact h F hF heF
  · intro h F hF heF
    let F' := F ∩ E
    have hsub : F' ⊆ E := inter_subset_right
    have hcard : F'.card ≤ f := (card_le_card inter_subset_left).trans hF
    have heF' : e ∉ F' := fun he => heF (mem_inter.mp he).1
    have heq : afterFaults (edgeGraph E) F' = afterFaults (edgeGraph E) F := by
      apply SimpleGraph.edgeSet_injective
      ext d
      simp only [mem_afterFaults, mem_edgeGraph, F', mem_inter]
      tauto
    simpa only [heq] using h F' hsub hcard heF'

variable [Fintype V]
attribute [local instance] Classical.propDecidable

noncomputable def input (G Q : SimpleGraph V) (w : Sym2 V → ℝ) : List (Sym2 V) :=
  (LightSpanners.greedyInput G w).filter (fun e => e ∉ Q.edgeFinset)

@[simp] theorem mem_input (G Q : SimpleGraph V) (w : Sym2 V → ℝ) (e : Sym2 V) :
    e ∈ input G Q w ↔ e ∈ G.edgeFinset ∧ e ∉ Q.edgeFinset := by simp [input]

noncomputable def output (G Q : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) :
    SimpleGraph V := edgeGraph (greedyEdges Q.edgeFinset w t f (input G Q w))

theorem output_isEFTSpanner (G Q : SimpleGraph V) (hQ : Q ≤ G)
    (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) (ht : 1 ≤ t) (hw : ∀ e, 0 ≤ w e) :
    IsEFTSpanner G (output G Q w t f) w t f := by
  have hgraph : edgeGraph (Q.edgeFinset ∪ (input G Q w).toFinset) = G := by
    apply SimpleGraph.edgeSet_injective
    ext e
    simp only [mem_edgeGraph, mem_union, List.mem_toFinset, mem_input, mem_edgeFinset]
    constructor
    · rintro ⟨he,_⟩
      rcases he with he | ⟨he,_⟩
      · exact SimpleGraph.edgeSet_mono hQ he
      · exact he
    · intro he
      refine ⟨?_, G.not_isDiag_of_mem_edgeSet he⟩
      by_cases heQ : e ∈ Q.edgeSet
      · exact Or.inl heQ
      · exact Or.inr ⟨he,heQ⟩
  have h := greedy_isEFTSpanner Q.edgeFinset w t f ht hw (input G Q w)
    (fun e he => G.not_isDiag_of_mem_edgeFinset ((mem_input G Q w e).mp he).1)
  simpa only [hgraph, output] using h

end LightEFTSpanners
