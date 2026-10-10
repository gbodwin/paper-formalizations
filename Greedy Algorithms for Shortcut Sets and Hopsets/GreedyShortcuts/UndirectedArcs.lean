import GreedyShortcuts.SymmetricWeights
import GreedyShortcuts.WeightedBenchmark

/-! Unordered hopedge sets and their two directed realizations. Cardinality
counts unordered edges once; all metric arguments use the exact arc realization. -/
namespace GreedyShortcuts.Undirected

open Finset DirectedPaths WeightedPaths
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def arcs (H : Finset (Sym2 V)) : Finset (V × V) :=
  H.image Quot.out ∪ H.image (fun e => e.out.swap)

noncomputable def forget (A : Finset (V × V)) : Finset (Sym2 V) :=
  A.image (fun e => s(e.1,e.2))

theorem mem_arcs (H : Finset (Sym2 V)) (s t : V) :
    (s,t) ∈ arcs H ↔ s(s,t) ∈ H := by
  classical
  constructor
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨e,he,heq⟩ := Finset.mem_image.mp he
      have ho : s(e.out.1,e.out.2) = e := e.out_eq
      rw [heq] at ho
      simpa only [ho] using he
    · obtain ⟨e,he,heq⟩ := Finset.mem_image.mp he
      have ho : s(e.out.2,e.out.1) = e := Sym2.eq_swap.trans e.out_eq
      have hs := congrArg Prod.fst heq
      have ht := congrArg Prod.snd heq
      simp only [Prod.fst_swap,Prod.snd_swap] at hs ht
      rw [hs,ht] at ho
      rw [ho]
      exact he
  · intro he
    have ho : s((Quot.out s(s,t)).1,(Quot.out s(s,t)).2) = s(s,t) := Quot.out_eq _
    rcases Sym2.eq_iff.mp ho with h | h
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨s(s,t),he,Prod.ext h.1 h.2⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨s(s,t),he,Prod.ext h.2 h.1⟩

@[simp] theorem arcs_empty : arcs (∅ : Finset (Sym2 V)) = ∅ := by simp [arcs]

theorem arcs_symm (H : Finset (Sym2 V)) {s t : V} (h : (s,t) ∈ arcs H) : (t,s) ∈ arcs H := by
  rw [mem_arcs] at h ⊢
  simpa only [Sym2.eq_swap] using h

theorem arcs_mono : Monotone (arcs (V := V)) := by
  intro H J h e he
  exact (mem_arcs J e.1 e.2).mpr (h ((mem_arcs H e.1 e.2).mp he))

theorem arcs_card (H : Finset (Sym2 V)) : (arcs H).card ≤ 2*H.card := by
  have hc := Finset.card_union_le (H.image Quot.out) (H.image fun e => e.out.swap)
  have h₁ := Finset.card_image_le (s := H) (f := Quot.out)
  have h₂ := Finset.card_image_le (s := H) (f := fun e => e.out.swap)
  unfold arcs
  omega

@[simp] theorem arcs_insert (e : Sym2 V) (H : Finset (Sym2 V)) :
    arcs (insert e H) = arcs {e} ∪ arcs H := by
  ext ⟨u,v⟩
  simp [mem_arcs]

@[simp] theorem arcs_pair (s t : V) : arcs {s(s,t)} = {(s,t),(t,s)} := by
  ext ⟨u,v⟩
  simp only [mem_arcs, Finset.mem_singleton, Sym2.eq_iff, Finset.mem_insert, Prod.mk.injEq]

@[simp] theorem forget_arcs (H : Finset (Sym2 V)) : forget (arcs H) = H := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ s t =>
    constructor
    · intro he
      obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp he
      rw [mem_arcs] at hp
      simpa only [heq] using hp
    · intro he
      exact Finset.mem_image.mpr ⟨(s,t),(mem_arcs H s t).mpr he,rfl⟩

theorem augment_symmetric (G : V → V → Prop) (hG : Symmetric G) (H : Finset (Sym2 V)) :
    Symmetric (augment G (arcs H)) := by
  intro s t h
  exact h.elim (fun h => Or.inl (hG h)) (fun h => Or.inr (arcs_symm H h))

theorem augmentWeight_symmetric (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (hw : ∀ s t, w s t = w t s) (H : Finset (Sym2 V)) :
    ∀ s t, augmentWeight G w (arcs H) s t = augmentWeight G w (arcs H) t s := by
  intro s t
  by_cases he : (s,t) ∈ arcs H
  · simp only [augmentWeight, if_pos he, if_pos (arcs_symm H he), distance_symm G w hG hw s t]
  · have ht : (t,s) ∉ arcs H := fun h => he (arcs_symm H h)
    simp only [augmentWeight, if_neg he, if_neg ht, hw s t]

noncomputable def candidates (G : V → V → Prop) : Finset (Sym2 V) := forget (DirectedPaths.candidates G)

theorem candidate_reverse (G : V → V → Prop) (hG : Symmetric G) {s t : V}
    (h : (s,t) ∈ DirectedPaths.candidates G) : (t,s) ∈ DirectedPaths.candidates G := by
  obtain ⟨hne,hr⟩ := (mem_candidates G (s,t)).mp h
  exact (mem_candidates G (t,s)).mpr ⟨hne.symm,reachable_symm hG hr⟩

theorem arcs_subset_candidates (G : V → V → Prop) (hG : Symmetric G)
    {H : Finset (Sym2 V)} (hH : H ⊆ candidates G) : arcs H ⊆ DirectedPaths.candidates G := by
  intro e he
  have hh := hH ((mem_arcs H e.1 e.2).mp he)
  obtain ⟨p,hp,hpe⟩ := Finset.mem_image.mp hh
  rcases Sym2.eq_iff.mp hpe with hh | hh
  · have hEq : p = e := Prod.ext hh.1 hh.2
    simpa only [hEq] using hp
  · have hEq : p.swap = e := Prod.ext hh.2 hh.1
    have hh := candidate_reverse G hG hp
    change p.swap ∈ DirectedPaths.candidates G at hh
    simpa only [hEq] using hh

end GreedyShortcuts.Undirected
