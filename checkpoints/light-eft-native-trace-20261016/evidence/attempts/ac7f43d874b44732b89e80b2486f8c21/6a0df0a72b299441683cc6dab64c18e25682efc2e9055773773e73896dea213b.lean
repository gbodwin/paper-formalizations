import LightEFTSpanners.NativeGreedySampling

namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Explicit position in the tail-first insertion history. The earlier selected
set is exactly the greedy output on suffix, not an arbitrary subset. Its
chronological rank is suffix.length: the number of already processed IDs. -/
structure InsertionTrace [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (f : ℕ) (seed : Finset E) (es : List E) (e : E) where
  prefix : List E
  suffix : List E
  decomposition : es = prefix ++ e :: suffix
  absent : e ∉ nativeGreedy G w t f seed suffix
  rejected : ¬ NativeCovered G w t f (nativeGreedy G w t f seed suffix) e

namespace InsertionTrace
variable [DecidableEq E] {G : Graph V E} {w : E → ℝ≥0} {t : ℝ≥0}
    {f : ℕ} {seed : Finset E} {es : List E} {e : E}
def rank (tr : InsertionTrace G w t f seed es e) : ℕ := tr.suffix.length
noncomputable def earlier (tr : InsertionTrace G w t f seed es e) : Finset E :=
  nativeGreedy G w t f seed tr.suffix

theorem seed_subset (tr : InsertionTrace G w t f seed es e) : seed ⊆ tr.earlier :=
  nativeGreedy_seed_subset G w t f seed tr.suffix

theorem rank_lt (tr : InsertionTrace G w t f seed es e) : tr.rank < es.length := by
  rw [tr.decomposition]
  simp [rank]
  omega

theorem witness (tr : InsertionTrace G w t f seed es e) :
    ∃ F, InsertionWitness G w t f tr.earlier e F :=
  failed_test_witness tr.absent tr.rejected
end InsertionTrace

theorem nativeGreedy_tail_subset [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (f : ℕ) (seed : Finset E) (e : E) (es : List E) :
    nativeGreedy G w t f seed es ⊆ nativeGreedy G w t f seed (e :: es) := by
  simp only [nativeGreedy]
  split
  · exact Subset.rfl
  · exact subset_insert _ _

theorem nativeGreedy_suffix_subset [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (f : ℕ) (seed : Finset E) (pre post : List E) :
    nativeGreedy G w t f seed post ⊆ nativeGreedy G w t f seed (pre ++ post) := by
  induction pre with
  | nil => exact Subset.rfl
  | cons e pre ih => exact ih.trans (nativeGreedy_tail_subset G w t f seed e (pre ++ post))

theorem InsertionTrace.earlier_subset [DecidableEq E] {G : Graph V E} {w : E → ℝ≥0}
    {t : ℝ≥0} {f : ℕ} {seed : Finset E} {es : List E} {e : E}
    (tr : InsertionTrace G w t f seed es e) : tr.earlier ⊆ nativeGreedy G w t f seed es := by
  rw [tr.decomposition]
  exact (nativeGreedy_tail_subset G w t f seed e tr.suffix).trans
    (nativeGreedy_suffix_subset G w t f seed tr.prefix (e :: tr.suffix))

/-- No original edge ID is invented by the construction. -/
theorem nativeGreedy_subset_input [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (f : ℕ) (seed : Finset E) (es : List E) :
    nativeGreedy G w t f seed es ⊆ seed ∪ es.toFinset := by
  induction es with
  | nil => simp [nativeGreedy]
  | cons e es ih =>
    intro d hd
    simp only [nativeGreedy] at hd
    split at hd
    · exact mem_union.mpr ((mem_union.mp (ih hd)).imp_right (fun h => by simp [h]))
    · rcases mem_insert.mp hd with rfl | hd
      · simp
      · exact mem_union.mpr ((mem_union.mp (ih hd)).imp_right (fun h => by simp [h]))

/-- Actual input containment, including a possibly empty candidate list. -/
theorem nativeGreedy_input_containment [Fintype E] [DecidableEq E]
    (G : Graph V E) (w : E → ℝ≥0) (t : ℝ≥0) (f : ℕ) (seed : Finset E) (es : List E)
    (hs : seed ⊆ inputEdges G) (he : ∀ e ∈ es, e ∈ inputEdges G) :
    nativeGreedy G w t f seed es ⊆ inputEdges G := by
  intro e h
  rcases mem_union.mp (nativeGreedy_subset_input G w t f seed es h) with h | h
  · exact hs h
  · exact he e (List.mem_toFinset.mp h)

/-- Any nonseed selected ID in a finite set C admits a latest actual insertion.
All other C-edges were already selected then. The descending list order means
ascending chronological weight order, and bounds every nonseed C-edge. -/
theorem exists_latest_trace [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (f : ℕ) (seed : Finset E) (es : List E)
    (hsort : es.Pairwise (fun e d => w d ≤ w e)) (C : Finset E)
    (hC : C ⊆ nativeGreedy G w t f seed es) (hn : (C \ seed).Nonempty) :
    ∃ e ∈ C \ seed, ∃ tr : InsertionTrace G w t f seed es e,
      C.erase e ⊆ tr.earlier ∧ ∀ d ∈ C \ seed, w d ≤ w e := by
  induction es with
  | nil =>
    obtain ⟨e,he⟩ := hn
    exact False.elim ((mem_sdiff.mp he).2 (hC (mem_sdiff.mp he).1))
  | cons e es ih =>
    let A := nativeGreedy G w t f seed es
    by_cases hi : e ∈ A ∨ NativeCovered G w t f A e
    · have hCA : C ⊆ A := by simpa only [nativeGreedy,hi,ite_true] using hC
      obtain ⟨d,hd,tr,hrest,hweight⟩ := ih hsort.tail hCA
      refine ⟨d,hd,⟨e :: tr.prefix,tr.suffix,?_,tr.absent,tr.rejected⟩,hrest,hweight⟩
      simp [tr.decomposition]
    · have hCA : C ⊆ insert e A := by simpa only [nativeGreedy,hi,ite_false] using hC
      by_cases heC : e ∈ C
      · have heS : e ∉ seed := fun h => (not_or.mp hi).1
          (nativeGreedy_seed_subset G w t f seed es h)
        refine ⟨e,mem_sdiff.mpr ⟨heC,heS⟩,⟨[],es,rfl,(not_or.mp hi).1,(not_or.mp hi).2⟩,?_,?_⟩
        · intro d hd
          rcases mem_insert.mp (hCA (mem_of_mem_erase hd)) with h | h
          · exact False.elim ((ne_of_mem_erase hd) h)
          · exact h
        · intro d hd
          by_cases hde : d = e
          · simpa [hde]
          · have hdA : d ∈ A := (mem_insert.mp (hCA (mem_sdiff.mp hd).1)).resolve_left hde
            have hdL : d ∈ es := List.mem_toFinset.mp
              ((mem_union.mp (nativeGreedy_subset_input G w t f seed es hdA)).resolve_left (mem_sdiff.mp hd).2)
            exact (List.pairwise_cons.mp hsort).1 d hdL
      · have hCA' : C ⊆ A := fun d hd => (mem_insert.mp (hCA hd)).resolve_left
          (fun h => heC (h ▸ hd))
        obtain ⟨d,hd,tr,hrest,hweight⟩ := ih hsort.tail hCA'
        refine ⟨d,hd,⟨e :: tr.prefix,tr.suffix,?_,tr.absent,tr.rejected⟩,hrest,hweight⟩
        simp [tr.decomposition]

end LightEFTSpanners.NativeWeighted
