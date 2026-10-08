import LinearDistancePreservers.FavorableCut
import LinearDistancePreservers.InducedMatchings
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite

/-! The induced-matching extremal number in the normalization used by the
paper: maximum edges of a graph partitionable into at most `|V|` induced
matchings. A finite edge set contains one orientation of each undirected edge.
This avoids confusing it with mathlib's triangle-count normalization. -/
namespace LinearDistancePreservers
open Finset
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V] [DecidableEq V]

def Span (E : Finset (V × V)) (u v : V) : Prop := (u,v) ∈ E ∨ (v,u) ∈ E

def Separated (G : V → V → Prop) (e f : V × V) : Prop :=
  ∀ a, (a = e.1 ∨ a = e.2) → ∀ b, (b = f.1 ∨ b = f.2) → a ≠ b ∧ ¬ G a b

structure InducedPartition (E : Finset (V × V)) (label : V × V → I) : Prop where
  loopless : ∀ e ∈ E, e.1 ≠ e.2
  oriented : ∀ e ∈ E, Prod.swap e ∉ E
  induced : ∀ e ∈ E, ∀ f ∈ E, label e = label f → e ≠ f → Separated (Span E) e f

noncomputable def matchingNumber (V : Type*) [Fintype V] [DecidableEq V] : ℕ :=
  (univ : Finset (Finset (V × V))).sup fun E =>
    if ∃ label : V × V → V, InducedPartition E label then E.card else 0

theorem InducedPartition.card_le {E : Finset (V × V)} {label : V × V → V}
    (h : InducedPartition E label) : E.card ≤ matchingNumber V := by
  classical
  have := Finset.le_sup (f := fun E : Finset (V × V) =>
    if ∃ label : V × V → V, InducedPartition E label then E.card else 0) (mem_univ E)
  have hex : ∃ label : V × V → V, InducedPartition E label := ⟨label, h⟩
  simpa only [if_pos hex, matchingNumber] using this

theorem InducedPartition.mono {E F : Finset (V × V)} {label : V × V → I}
    (h : InducedPartition E label) (hFE : F ⊆ E) : InducedPartition F label where
  loopless e he := h.loopless e (hFE he)
  oriented e he hf := h.oriented e (hFE he) (hFE hf)
  induced e he f hf hl hn a ha b hb := by
    have hs := h.induced e (hFE he) f (hFE hf) hl hn a ha b hb
    exact ⟨hs.1, fun hh => hs.2 (hh.elim (fun x => Or.inl (hFE x)) (fun x => Or.inr (hFE x)))⟩

theorem LazyEdges.class_separated {G : V → V → Prop} {depth : V → ℕ}
    (T : LazyEdges V G depth) (c : V → Bool) (r : Fin 3) {e f : V × V}
    (he : T.InClass c r e) (hf : T.InClass c r f) (hne : e ≠ f) :
    Separated (LazyEdges.Cut (G := G) c) e f := by
  obtain ⟨_, _, h11, h22, h12, h21, g11, g12, g21, g22⟩ :=
    T.class_is_induced_matching c r he hf hne
  intro a ha b hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact ⟨h11, g11⟩
  · exact ⟨h12, g12⟩
  · exact ⟨h21, g21⟩
  · exact ⟨h22, g22⟩

/-- Any cut-oriented set of edges assigned to the three residue classes
of `|V|` lazy trees has at most `3 * matchingNumber V` edges. Assignment
chooses one tree for each edge, so overlaps do not get counted twice. -/
theorem lazy_partition_bound {G : V → V → Prop} (hG : Symmetric G)
    (depth : V → V → ℕ) (T : ∀ s, LazyEdges V G (depth s))
    (E : Finset (V × V)) (c : V → Bool) (owner : V × V → V)
    (he : ∀ e ∈ E, (T (owner e)).edge e.1 e.2 ∧ c e.1 = false ∧ c e.2 = true) :
    E.card ≤ 3 * matchingNumber V := by
  classical
  let residue (e : V × V) : Fin 3 := ⟨depth (owner e) e.1 % 3, Nat.mod_lt _ (by decide)⟩
  let F (r : Fin 3) := E.filter fun e => residue e = r
  have hpart (r : Fin 3) : InducedPartition (F r) owner := by
    have hcut : ∀ e ∈ F r, LazyEdges.Cut (G := G) c e.1 e.2 := by
      intro e hem
      have h := he e (mem_filter.mp hem).1
      exact ⟨(T (owner e)).adjacent _ _ h.1, by simp [h.2.1, h.2.2]⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e hem hEq
      exact (hcut e hem).2 (congrArg c hEq)
    · intro e hem hswap
      have hc := (he e (mem_filter.mp hem).1).2
      have hc' := (he e.swap (mem_filter.mp hswap).1).2
      simp only [Prod.fst_swap, Prod.snd_swap] at hc'
      rw [hc.1] at hc'
      cases hc'.2
    · intro e hem f hfm hl hn
      have hclass (e : V × V) (hem : e ∈ F r) : (T (owner e)).InClass c r e := by
        have h := he e (mem_filter.mp hem).1
        exact ⟨h.1, h.2.1, h.2.2, congrArg Fin.val (mem_filter.mp hem).2⟩
      have hf := hclass f hfm
      rw [← hl] at hf
      have hs := (T (owner e)).class_separated c r (hclass e hem) hf hn
      intro a ha b hb
      have hab := hs a ha b hb
      refine ⟨hab.1, ?_⟩
      rintro (hab' | hba')
      · exact hab.2 (hcut (a,b) hab')
      · have hba := hcut (b,a) hba'
        exact hab.2 ⟨hG hba.1, Ne.symm hba.2⟩
  calc
    E.card = ∑ r : Fin 3, (F r).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _r : Fin 3, matchingNumber V := sum_le_sum (fun r _ => (hpart r).card_le)
    _ = _ := by simp

end LinearDistancePreservers
