import LightEFTSpanners.NativeHostSampling

/-! Native, edge-identified greedy insertions and their actual rejection witnesses.
These are insertion-time blocking results, not a claim that raw sampled hosts
have full weighted girth. Seed-dominated cycles still need pruning. -/
namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

namespace Walk
noncomputable def edgeList {G : Graph V E} {H F : Finset E} :
    {u v : G.vertexSet} → Walk G H F u v → List E
  | _, _, .nil _ => []
  | _, _, .cons e _ _ _ p => e :: edgeList p

noncomputable def reverse {G : Graph V E} {H F : Finset E} :
    {u v : G.vertexSet} → Walk G H F u v → Walk G H F v u
  | _, _, .nil u => .nil u
  | _, _, .cons e hl he hf p => (reverse p).append (.cons e hl.symm he hf (.nil _))

@[simp] theorem weight_reverse {G : Graph V E} {H F : Finset E}
    {u v : G.vertexSet} (w : E → ℝ≥0) (p : Walk G H F u v) :
    p.reverse.weight w = p.weight w := by
  induction p with
  | nil => rfl
  | cons e hl he hf p ih => simp [reverse,weight,ih,add_comm]

theorem transfer_avoiding {G : Graph V E} {H F : Finset E}
    {u v : G.vertexSet} (w : E → ℝ≥0) (p : Walk G H ∅ u v)
    (h : ∀ e ∈ p.edgeList, e ∉ F) :
    ∃ r : Walk G H F u v, r.weight w = p.weight w := by
  induction p with
  | nil u => exact ⟨.nil u,rfl⟩
  | cons e hl he hf p ih =>
    obtain ⟨r,hr⟩ := ih (fun d hd => h d (List.mem_cons_of_mem e hd))
    exact ⟨.cons e hl he (h e (by simp [edgeList])) r,by simp [weight,hr]⟩
end Walk

/-- All endpoint orientations and every fault set in the original edge-ID universe. -/
def NativeCovered (G : Graph V E) (w : E → ℝ≥0) (t : ℝ≥0)
    (f : ℕ) (A : Finset E) (e : E) : Prop :=
  ∀ F : Finset E, F ⊆ A → F.card ≤ f → ∀ u v : G.vertexSet,
    G.IsLink e u.val v.val → ∃ p : Walk G A F u v, p.weight w ≤ t * w e

/-- A tail-first finite native construction. Already present IDs are ignored.
There is no assumed blocking or girth property in the insertion test. -/
noncomputable def nativeGreedy [DecidableEq E] (G : Graph V E)
    (w : E → ℝ≥0) (t : ℝ≥0) (f : ℕ) (seed : Finset E) : List E → Finset E
  | [] => seed
  | e :: es =>
    let A := nativeGreedy G w t f seed es
    if e ∈ A ∨ NativeCovered G w t f A e then A else insert e A

/-- The actual failed insertion test, retaining chronology and bad endpoints. -/
def InsertionWitness (G : Graph V E) (w : E → ℝ≥0) (t : ℝ≥0)
    (f : ℕ) (A : Finset E) (e : E) (F : Finset E) : Prop :=
  e ∉ A ∧ F ⊆ A ∧ F.card ≤ f ∧
    ∃ u v : G.vertexSet, G.IsLink e u.val v.val ∧
      ∀ p : Walk G A F u v, t * w e < p.weight w

theorem failed_test_witness {G : Graph V E} {w : E → ℝ≥0} {t : ℝ≥0}
    {f : ℕ} {A : Finset E} {e : E} (he : e ∉ A)
    (h : ¬ NativeCovered G w t f A e) : ∃ F, InsertionWitness G w t f A e F := by
  classical
  simp only [NativeCovered,not_forall] at h
  obtain ⟨F,h⟩ := h
  simp only [not_imp] at h
  obtain ⟨hFA,hFc,u,v,hl,hp⟩ := h
  refine ⟨F,he,hFA,hFc,u,v,hl,?_⟩
  intro p
  exact lt_of_not_ge (fun hh => hp ⟨p,hh⟩)

theorem nativeGreedy_seed_subset [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (f : ℕ) (seed : Finset E) (es : List E) :
    seed ⊆ nativeGreedy G w t f seed es := by
  induction es with
  | nil => exact Subset.rfl
  | cons e es ih =>
    simp only [nativeGreedy]
    split
    · exact ih
    · exact ih.trans (subset_insert _ _)

/-- Each genuinely new selected ID has a failed-test witness in its earlier
selected prefix; blockers are not postulated from cardinality/no-self alone. -/
theorem nativeGreedy_witness [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (f : ℕ) (seed : Finset E) (es : List E) :
    ∀ e ∈ nativeGreedy G w t f seed es, e ∉ seed →
      ∃ A F, A ⊆ nativeGreedy G w t f seed es ∧
        InsertionWitness G w t f A e F := by
  induction es with
  | nil => simp [nativeGreedy]
  | cons d es ih =>
    intro e he hs
    simp only [nativeGreedy] at he ⊢
    split at he ⊢
    · exact ih e he hs
    · rcases mem_insert.mp he with rfl | he
      · rename_i h
        obtain ⟨F,hF⟩ := failed_test_witness (not_or.mp h).1 (not_or.mp h).2
        exact ⟨_,F,subset_insert _ _,hF⟩
      · obtain ⟨A,F,hA,hF⟩ := ih e he hs
        exact ⟨A,F,hA.trans (subset_insert _ _),hF⟩

/-- Rejection forbids a short surviving detour in either endpoint orientation. -/
theorem InsertionWitness.detour_lt {G : Graph V E} {w : E → ℝ≥0} {t : ℝ≥0}
    {f : ℕ} {A F : Finset E} {e : E} (h : InsertionWitness G w t f A e F)
    {x y : G.vertexSet} (hl : G.IsLink e x.val y.val) (p : Walk G A F x y) :
    t * w e < p.weight w := by
  obtain ⟨_,_,_,u,v,huv,hbad⟩ := h
  rcases hl.eq_and_eq_or_eq_and_eq huv with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · have hx' : x = u := Subtype.ext hx
    have hy' : y = v := Subtype.ext hy
    subst x; subst y
    exact hbad p
  · have hx' : x = v := Subtype.ext hx
    have hy' : y = u := Subtype.ext hy
    subst x; subst y
    simpa using hbad p.reverse

/-- Every short earlier detour hits the actual failed-test fault set. Together
with the new edge this blocks the corresponding insertion-time cycle. -/
theorem InsertionWitness.blocks_detour {G : Graph V E} {w : E → ℝ≥0} {t : ℝ≥0}
    {f : ℕ} {A F : Finset E} {e : E} (h : InsertionWitness G w t f A e F)
    {x y : G.vertexSet} (hl : G.IsLink e x.val y.val) (p : Walk G A ∅ x y)
    (hp : p.weight w ≤ t * w e) : ∃ d ∈ p.edgeList, d ∈ F := by
  classical
  by_contra hn
  have ha : ∀ d ∈ p.edgeList, d ∉ F := by simpa using hn
  obtain ⟨r,hr⟩ := p.transfer_avoiding w ha
  exact (not_lt_of_ge (hr.trans_le hp)) (h.detour_lt hl r)

/-- Loops cannot be newly bought: the empty walk always covers their demand. -/
theorem InsertionWitness.not_loop {G : Graph V E} {w : E → ℝ≥0} {t : ℝ≥0}
    {f : ℕ} {A F : Finset E} {e : E} (h : InsertionWitness G w t f A e F)
    (x : G.vertexSet) : ¬ G.IsLink e x.val x.val := by
  intro hl
  have hh := h.detour_lt hl (.nil x)
  exact (not_lt_of_ge (zero_le _)) hh

/-- A two-edge cycle uses two distinct original IDs. A short earlier parallel
ID must itself be a blocker, even though it has the same endpoint pair. -/
theorem InsertionWitness.parallel_blocked {G : Graph V E} {w : E → ℝ≥0} {t : ℝ≥0}
    {f : ℕ} {A F : Finset E} {e d : E} (h : InsertionWitness G w t f A e F)
    {x y : G.vertexSet} (he : G.IsLink e x.val y.val) (hd : G.IsLink d x.val y.val)
    (hdA : d ∈ A) (hw : w d ≤ t * w e) : d ≠ e ∧ d ∈ F := by
  refine ⟨fun hh => h.1 (hh ▸ hdA),?_⟩
  by_contra hf
  have hh := h.detour_lt he (.cons d hd hdA hf (.nil y))
  exact (not_lt_of_ge hw) (by simpa [Walk.weight] using hh)

end LightEFTSpanners.NativeWeighted
