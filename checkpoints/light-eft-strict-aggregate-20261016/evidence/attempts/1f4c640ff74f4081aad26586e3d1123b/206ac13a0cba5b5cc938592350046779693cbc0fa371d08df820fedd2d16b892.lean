import LightEFTSpanners.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/-! Explicit sparse fault-connectivity certificates in complete bipartite graphs.
A clean hub on each side exists because every failed cross edge touches only
one hub on that side. No connectivity or packing oracle is assumed. -/
namespace LightEFTSpanners.HubPreserver
open SimpleGraph Finset
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- Each cross edge identifies both endpoints uniquely. -/
theorem cross_injective : Function.Injective
    (fun p : L×R => (s(Sum.inl p.1,Sum.inr p.2) : Sym2 (L⊕R))) := by
  intro p q h
  rcases p with ⟨a,b⟩; rcases q with ⟨c,d⟩
  rcases Sym2.eq_iff.mp h with h | h
  · simp only [Sum.inl.injEq,Sum.inr.injEq] at h
    rcases h with ⟨rfl,rfl⟩; rfl
  · simp at h

/-- If fewer failures occur than left hubs, one left hub has no failed cross
edge incident to it, even when the supplied fault set includes nonedges. -/
theorem exists_clean_left (A : Finset L) (F : Finset (Sym2 (L⊕R)))
    (hcard : F.card < A.card) :
    ∃ a ∈ A, ∀ b : R, s(Sum.inl a,Sum.inr b) ∉ F := by
  classical
  by_contra! hh
  have hex : ∀ a : A, ∃ b : R, s(Sum.inl a.val,Sum.inr b) ∈ F := fun a => hh a.val a.property
  choose b hb using hex
  have hinj : Function.Injective (fun a : A => s(Sum.inl a.val,Sum.inr (b a))) := by
    intro a a' he
    have hp : (a.val,b a) = (a'.val,b a') := cross_injective he
    exact Subtype.ext (congrArg Prod.fst hp)
  have hsub : A.attach.image (fun a : A => s(Sum.inl a.val,Sum.inr (b a))) ⊆ F := by
    intro e he
    obtain ⟨a,_,rfl⟩ := mem_image.mp he
    exact hb a
  have hc := card_le_card hsub
  rw [card_image_of_injective _ hinj,card_attach] at hc
  omega

/-- Symmetric clean-hub selection on the right. -/
theorem exists_clean_right (B : Finset R) (F : Finset (Sym2 (L⊕R)))
    (hcard : F.card < B.card) :
    ∃ b ∈ B, ∀ a : L, s(Sum.inl a,Sum.inr b) ∉ F := by
  classical
  by_contra! hh
  have hex : ∀ b : B, ∃ a : L, s(Sum.inl a,Sum.inr b.val) ∈ F := fun b => hh b.val b.property
  choose a ha using hex
  have hinj : Function.Injective (fun b : B => s(Sum.inl (a b),Sum.inr b.val)) := by
    intro b b' he
    have hp : (a b,b.val) = (a b',b'.val) := cross_injective he
    exact Subtype.ext (congrArg Prod.snd hp)
  have hsub : B.attach.image (fun b : B => s(Sum.inl (a b),Sum.inr b.val)) ⊆ F := by
    intro e he
    obtain ⟨b,_,rfl⟩ := mem_image.mp he
    exact ha b
  have hc := card_le_card hsub
  rw [card_image_of_injective _ hinj,card_attach] at hc
  omega

def graph (A : Finset L) (B : Finset R) : SimpleGraph (L⊕R) where
  Adj u v := match u,v with
    | Sum.inl a,Sum.inr b => a ∈ A ∨ b ∈ B
    | Sum.inr b,Sum.inl a => a ∈ A ∨ b ∈ B
    | _,_ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> simp⟩
  loopless := ⟨by intro u; cases u <;> simp⟩

@[simp] theorem graph_cross (A : Finset L) (B : Finset R) (a : L) (b : R) :
    (graph A B).Adj (Sum.inl a) (Sum.inr b) ↔ a∈A ∨ b∈B := Iff.rfl

theorem graph_le (A : Finset L) (B : Finset R) : graph A B ≤ completeBipartiteGraph L R := by
  intro u v h
  cases u <;> cases v <;> simp_all [graph]

/-- The hub certificate actually stays connected under every allowed fault set. -/
theorem afterFaults_connected (A : Finset L) (B : Finset R)
    (F : Finset (Sym2 (L⊕R))) (hA : F.card < A.card) (hB : F.card < B.card) :
    (afterFaults (graph A B) F).Connected := by
  classical
  obtain ⟨a,ha,haclean⟩ := exists_clean_left A F hA
  obtain ⟨b,hb,hbclean⟩ := exists_clean_right B F hB
  have left (x : L) : (afterFaults (graph A B) F).Adj (Sum.inl x) (Sum.inr b) :=
    deleteEdges_adj.mpr ⟨Or.inr hb,hbclean x⟩
  have right (y : R) : (afterFaults (graph A B) F).Adj (Sum.inl a) (Sum.inr y) :=
    deleteEdges_adj.mpr ⟨Or.inl ha,haclean y⟩
  have reach (v : L⊕R) : (afterFaults (graph A B) F).Reachable v (Sum.inl a) := by
    cases v with
    | inl x => exact (left x).reachable.trans (right b).reachable.symm
    | inr y => exact (right y).reachable.symm
  letI : Nonempty (L⊕R) := ⟨Sum.inl a⟩
  exact ⟨fun u v => (reach u).trans (reach v).symm⟩

theorem isFTPreserver (A : Finset L) (B : Finset R) (f : ℕ)
    (hA : f < A.card) (hB : f < B.card) :
    IsFTConnectivityPreserver (completeBipartiteGraph L R) (graph A B) f := by
  refine ⟨graph_le A B,?_⟩
  intro F hF u v
  constructor
  · intro _
    exact (afterFaults_connected A B F (hF.trans_lt hA) (hF.trans_lt hB)).preconnected u v
  · exact Reachable.mono (afterFaults_mono (graph_le A B) F)

end LightEFTSpanners.HubPreserver
