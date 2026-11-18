import Mathlib.Data.Finset.Sum
import OnlineReachabilityPreservers.Basic

/-! The terminal incidence lower bounds used in Section 5. -/

namespace OnlineReachabilityPreservers

open Finset Relation

variable {V : Type*} [DecidableEq V]

private theorem source_incident {H : Arcs V} {s t : V} (hne : s ≠ t) (reach : Reach H s t) :
    s ∈ H.image Prod.fst := by
  rcases reach.cases_head with eq | ⟨v, he, _⟩
  · exact (hne eq).elim
  · exact mem_image.mpr ⟨(s, v), he, rfl⟩

private theorem sink_incident {H : Arcs V} {s t : V} (hne : s ≠ t) (reach : Reach H s t) :
    t ∈ H.image Prod.snd := by
  rcases reach.cases_tail with eq | ⟨v, _, he⟩
  · exact (hne eq.symm).elim
  · exact mem_image.mpr ⟨(v, t), he, rfl⟩

/-- Lemma 20. Every solution to p distinct non-self demands has at least √p edges. -/
theorem lemma20_opt_squared (P : Finset (V × V)) (H : Arcs V)
    (nonself : ∀ d ∈ P, d.1 ≠ d.2) (preserved : ∀ d ∈ P, Reach H d.1 d.2) :
    P.card ≤ H.card ^ 2 := by
  calc
    _ ≤ ((H.image Prod.fst) ×ˢ (H.image Prod.snd)).card := by
      apply card_le_card
      intro d hd
      exact mem_product.mpr ⟨source_incident (nonself d hd) (preserved d hd),
        sink_incident (nonself d hd) (preserved d hd)⟩
    _ ≤ H.card ^ 2 := by
      rw [card_product, pow_two]
      exact Nat.mul_le_mul card_image_le card_image_le

variable [Fintype V]

/-- Lemma 22. Every nontrivial hit reveals a new source–hub or hub–sink
connection, and every terminal in such a charge meets an edge of any offline solution. -/
theorem lemma22_hub_count (D : List (V × V)) (S : Finset V) (Z : Arcs V)
    (H : ℕ → Arcs V) (mono : Monotone H) (hub : Fin D.length → V)
    (inS : ∀ i, hub i ∈ S)
    (nontrivial : ∀ i : Fin D.length, ¬ Reach (H i) (D.get i).1 (D.get i).2)
    (served : ∀ i : Fin D.length, Reach (H (i.1 + 1)) (D.get i).1 (hub i) ∧
      Reach (H (i.1 + 1)) (hub i) (D.get i).2)
    (solution : ∀ i : Fin D.length, Reach Z (D.get i).1 (D.get i).2) :
    D.length ≤ 2 * S.card * Z.card := by
  let charge (i : Fin D.length) : (V × V) ⊕ (V × V) :=
    if (D.get i).1 ∈ reaches (H i) (hub i)
    then Sum.inr (hub i, (D.get i).2)
    else Sum.inl ((D.get i).1, hub i)
  have injective : Function.Injective charge := by
    have different (i j : Fin D.length) (hij : i < j) : charge i ≠ charge j := by
      have hsub : H (i.1 + 1) ⊆ H j := mono (by exact hij)
      intro he
      unfold charge at he
      split at he <;> split at he
      · rename_i hi hj
        have eq := Sum.inr.inj he
        have hr := reach_mono hsub (served i).2
        rw [Prod.mk.inj eq |>.1, Prod.mk.inj eq |>.2] at hr
        exact nontrivial j ((mem_reaches.mp hj).trans hr)
      · cases he
      · cases he
      · rename_i hi hj
        have eq := Sum.inl.inj he
        have hr := reach_mono hsub (served i).1
        rw [Prod.mk.inj eq |>.1, Prod.mk.inj eq |>.2] at hr
        exact hj (mem_reaches.mpr hr)
    intro i j eq
    rcases lt_trichotomy i j with h | h | h
    · exact (different i j h eq).elim
    · exact h
    · exact (different j i h eq.symm).elim
  let A := Z.image Prod.fst ×ˢ S
  let B := S ×ˢ Z.image Prod.snd
  have support : (univ : Finset (Fin D.length)).image charge ⊆ A.disjSum B := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    have hne : (D.get i).1 ≠ (D.get i).2 := by
      intro eq
      exact nontrivial i (eq ▸ ReflTransGen.refl)
    unfold charge
    split
    · exact mem_disjSum.mpr (Or.inr ⟨(hub i, (D.get i).2), mem_product.mpr
        ⟨inS i, sink_incident hne (solution i)⟩, rfl⟩)
    · exact mem_disjSum.mpr (Or.inl ⟨((D.get i).1, hub i), mem_product.mpr
        ⟨source_incident hne (solution i), inS i⟩, rfl⟩)
  calc
    D.length = ((univ : Finset (Fin D.length)).image charge).card := by
      rw [card_image_of_injective _ injective]
      simp
    _ ≤ (A.disjSum B).card := card_le_card support
    _ = (Z.image Prod.fst).card * S.card + S.card * (Z.image Prod.snd).card := by
      simp [A, B]
    _ ≤ Z.card * S.card + S.card * Z.card :=
      Nat.add_le_add (Nat.mul_le_mul_right _ card_image_le) (Nat.mul_le_mul_left _ card_image_le)
    _ = 2 * S.card * Z.card := by ring

end OnlineReachabilityPreservers
