import GreedyShortcuts.SuffixWindowPath
import GreedyShortcuts.GraphGreedy

/-! Lemma 3.2's high-score path for the actual active canonical demand family.
This statement applies to the current augmented graph, as its proof requires. -/
namespace GreedyShortcuts.CanonicalSuffixPath

open Finset DirectedPaths CanonicalSegments SuffixWindowPath
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def active (G : V → V → Prop) (β : ℕ) : Finset (V × V) := by
  classical
  exact (candidates G).filter (fun d => β < hopDist G d.1 d.2)

theorem active_reachable (G : V → V → Prop) (β : ℕ) (d : active G β) :
    Reachable G d.val.1 d.val.2 := by
  have hd := (Finset.mem_filter.mp d.property).1
  exact ((mem_candidates G d.val).mp hd).2

noncomputable def path (G : V → V → Prop) (β : ℕ) (d : active G β) : DWalk d.val.1 d.val.2 :=
  canonical G d.val.1 d.val.2 (active_reachable G β d)

theorem path_optimal (G : V → V → Prop) (β : ℕ) (d : active G β) :
    Optimal G (fun _ _ => 1) (path G β d) := canonical_optimal G _ _ _

theorem path_length (G : V → V → Prop) (β : ℕ) (d : active G β) :
    (path G β d).length = hopDist G d.val.1 d.val.2 :=
  (hopDist_eq G (active_reachable G β d)).symm

noncomputable def potential (G : V → V → Prop) (β : ℕ) : ℕ :=
  ∑ d ∈ candidates G, GraphGreedy.contribution β (hopDist G d.1 d.2)

theorem total_length (G : V → V → Prop) (β : ℕ) :
    (∑ d : active G β, (path G β d).length) = potential G β := by
  classical
  simp_rw [path_length]
  rw [Finset.sum_coe_sort (active G β) (fun d : V × V => hopDist G d.1 d.2)]
  simp only [active,Finset.sum_filter,potential,GraphGreedy.contribution]

/-- Actual suffix-incidence degree of an original vertex. Paths are simple,
so each demand contributes at most one occurrence to a vertex's degree. -/
noncomputable def degree (G : V → V → Prop) (β : ℕ) (v : V) : ℕ :=
  FamilyWindows.deg (fun d : active G β => suffixSize (path G β d))
    (fun d j => (path G β d).getVert (suffixOffset (path G β d)+j)) v

/-- A short canonical path with the required weighted degree, with explicit
constant and rounding. Acyclicity is needed later for the heavy/light proof,
not for this averaging step. -/
theorem exists_high_score_path (G : V → V → Prop) (β : ℕ) (hβ : 8 ≤ β)
    (hpos : 0 < potential G β) :
    ∃ (s t : V) (q : DWalk s t), Optimal G (fun _ _ => 1) q ∧
      q.length + 1 ≤ β/8 ∧
      β * potential G β ≤ 256 * Fintype.card V * ∑ v ∈ q.support.toFinset, degree G β v := by
  classical
  have hL : ∀ d : active G β, β < (path G β d).length := by
    intro d
    rw [path_length]
    exact (Finset.mem_filter.mp d.property).2
  obtain ⟨d,a,c,hac,hoff,hend,hshort,hscore⟩ := exists_suffix_window (path G β)
    (fun d => (path_optimal G β d).2.1) β hβ hL (by rw [total_length]; exact hpos)
  refine ⟨_,_,segment (path G β d) a c hac,optimal_segment (path_optimal G β d) a c hac,hshort,?_⟩
  simpa only [total_length,degree] using hscore

theorem potential_current_eq (G : V → V → Prop) (β : ℕ) (H : Finset (V × V))
    (hH : H ⊆ candidates G) : potential (augment G H) β = GraphGreedy.potential G β H := by
  have hc : candidates (augment G H) = candidates G := by
    ext d
    simp only [mem_candidates,reachable_augment_iff G H hH]
  simp only [potential,GraphGreedy.potential,hc]

/-- The high-score canonical path is in the current augmented graph G∪H,
correcting the original statement's use of the input graph G. -/
theorem exists_current_high_score_path (G : V → V → Prop) (β : ℕ) (hβ : 8 ≤ β)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (hpos : 0 < GraphGreedy.potential G β H) :
    ∃ (s t : V) (q : DWalk s t), Optimal (augment G H) (fun _ _ => 1) q ∧
      q.length + 1 ≤ β/8 ∧
      β * GraphGreedy.potential G β H ≤ 256 * Fintype.card V *
        ∑ v ∈ q.support.toFinset, degree (augment G H) β v := by
  have hh := exists_high_score_path (augment G H) β hβ
    (by simpa only [potential_current_eq G β H hH] using hpos)
  simpa only [potential_current_eq G β H hH] using hh

end GreedyShortcuts.CanonicalSuffixPath
