import OnlineReachabilityPreservers.OutputAverageDistinctCleaning

/-! Output-average cleaning through half cutoff five and full cutoff six. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

/-- For full bridges through size five, unique intersections allow both
width splits even when the original path orders can form cycles. -/
theorem listRegularizedPaths_fullFree_five_of_unique {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] {paths : I → List V}
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) 5)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (D L : ℕ) : BridgeFree (Before (listRegularizedPaths paths D L)) 5 := by
  let copies := splitListVertices paths D
  let pieces := splitListPaths copies L
  let parent (j : ListBlockIndex copies L) := j.fst
  have copyFree : BridgeFree (Before copies) 5 :=
    free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  have copySimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have copyUnique {a b x y} (different : a ≠ b) (ax : x ∈ copies a) (bx : x ∈ copies b)
      (ay : y ∈ copies a) (by' : y ∈ copies b) : x = y :=
    splitListVertices_unique simple (fun {_ _ _ _} => unique) different ax bx ay by'
  have steps {i x y} (step : Before pieces i x y) : Before copies (parent i) x y :=
    listBefore_of_sublist (paths := fun j => copies (parent j)) (cut := pieces)
      (copySimple (parent i)) List.filter_sublist step
  have together {i j q x y} (_ : parent i = parent j) (different : parent i ≠ parent q)
      (forward : Before copies (parent i) x y) (reverse : Before pieces q y x)
      (_ : x ∈ pieces i) (_ : y ∈ pieces j) : i = j := by
    have reverseOld := steps reverse
    exact (listBefore_ne forward (copyUnique different forward.1 reverseOld.2.1 forward.2.1 reverseOld.1)).elim
  intro k small
  exact ⟨fun b => (copyFree small).false
    (listBridge_after_opposite_safe_split_through_five parent (fun {_ _ _} => steps)
      (fun {_ _ _} => splitListPaths_disjoint)
      (fun _ {_ _ _ _} diff step other => no_parallel_list_steps copyFree.halfFree (by decide) diff step other)
      (fun {_ _ _ _ _} => together) (by omega) b)⟩

/-- At cutoffs of at most three, both width splits preserve half or full
exclusion on a restricted rectangle without any intersection condition. -/
theorem regularization_list_output_average_short {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : Bool) (allowed : localOrderAdmissible half k paths) (short : k ≤ 3)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      (∑ i, (paths i).length) ≤ 392*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  refine regularization_list_output_average_of_rectangle_splits paths simple half ?_ hn hp dense long
    (by omega) le_rfl
  intro A B D L
  have quarterSimple (i : B) : (restrictListPaths paths A B i).Nodup :=
    restrictListPath_nodup (simple i.val) A
  cases half
  · exact listRegularizedPaths_fullFree_short quarterSimple
      (restrictListPaths_fullFree simple allowed A B) short D L
  · exact listRegularizedPaths_halfFree_short quarterSimple
      (restrictListPaths_halfFree simple allowed A B) short D L

/-- At full cutoff five, pruning before the width splits gives
output-average caps and both original budgets. -/
theorem regularization_list_output_average_full_five {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : BridgeFree (Before paths) 5)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) 5 ∧
      (∑ i, (paths i).length) ≤ 392*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean :=
  regularization_list_output_average_of_pruned_rectangle_splits paths simple false allowed
    (by decide) (fun _ _ D L simple unique allowed =>
      listRegularizedPaths_fullFree_five_of_unique simple allowed (fun {_ _ _ _} => unique) D L)
    hn hp dense long

/-- Clean at every half cutoff through five and every full cutoff through
six with caps relative to the output averages. -/
theorem regularization_list_output_average_small_cutoffs {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : Bool) (allowed : localOrderAdmissible half k paths)
    (cutoff : k ≤ (if half then 5 else 6))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      (∑ i, (paths i).length) ≤ 392*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  by_cases short : k ≤ 3
  · exact regularization_list_output_average_short paths simple half allowed short hn hp dense long
  have upper : k ≤ 6 := by cases half <;> simp at cutoff <;> omega
  rcases (show k = 4 ∨ k = 5 ∨ k = 6 from by omega) with rfl | rfl | rfl
  · exact regularization_list_output_average_four paths simple half allowed hn hp dense long
  · cases half
    · exact regularization_list_output_average_full_five paths simple allowed hn hp dense long
    · exact regularization_list_output_average_half_five paths simple allowed hn hp dense long
  · cases half
    · exact regularization_list_output_average_six paths simple false allowed (by simp) hn hp dense long
    · simp at cutoff

/-- For each of these cutoffs, the unrestricted indexed maximum has a
constant-mass output-average witness within both original budgets. -/
theorem localOrderExtremal_output_average_small_cutoffs (n p k : ℕ)
    (half : Bool) (hn : 0 < n) (hp : 0 < p) (cutoff : k ≤ (if half then 5 else 6)) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        (∑ i, (paths i).length) ≤ 392*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,simple,allowed,maximal,dense,long⟩ := localOrderExtremal_isDense n p k half hn hp
  exact ⟨paths,simple,allowed,maximal,
    regularization_list_output_average_small_cutoffs paths simple half allowed cutoff hn hp dense long⟩

/-- The positive feasible literal maxima at these cutoffs have distinct,
nonempty witnesses with all four output-average caps. -/
theorem localOrderDistinctExtremal_output_average_small_cutoffs {n p k : ℕ}
    (half : Bool) (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ k) (cutoff : k ≤ (if half then 5 else 6))
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ localOrderAdmissible half k paths) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        (∑ i, (paths i).length) ≤ 7056*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,distinct,rows,allowed,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense half hp feasible
  let simple (i : Fin p) := (rows i).2
  obtain ⟨v,vFits,q,qFits,clean,injective,nonempty,cleanSimple,legal,mass,upper,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed (half := half)
      paths distinct (fun i => (rows i).1) simple allowed two hn hp dense
      (regularization_list_output_average_small_cutoffs paths simple half allowed cutoff hn hp dense)
  exact ⟨paths,distinct,rows,allowed,maximal,v,vFits,q,qFits,clean,injective,
    fun i => ⟨nonempty i,cleanSimple i⟩,legal,mass,upper,caps⟩

end OnlineReachabilityPreservers
