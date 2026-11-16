import LightEFTSpanners.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The actual clique-cloud construction in the corrected Theorem 34.
The order on the core vertices chooses one orientation of each tree edge;
consequently the sparse certificate uses two matchings, not three. -/
namespace LightEFTSpanners.CorrectedCloud
open SimpleGraph

/-- Replace every core vertex by a clique and every core edge by a complete
bipartite bundle. -/
def graph {m : ℕ} (G : SimpleGraph (Fin m)) (p : ℕ) :
    SimpleGraph (Fin m × Fin p) where
  Adj a b := (a.1 = b.1 ∧ a.2 ≠ b.2) ∨ G.Adj a.1 b.1
  symm := ⟨by
    intro a b h
    rcases h with ⟨hbase,hindex⟩ | hcore
    · exact Or.inl ⟨hbase.symm,hindex.symm⟩
    · exact Or.inr hcore.symm⟩
  loopless := ⟨by intro a h; rcases h with h | h <;> simp_all⟩

/-- Identity and one cyclic shift on the canonically oriented core edge. -/
def MatchingPair {m p : ℕ} (a b : Fin m × Fin p) : Prop :=
  a.2 = b.2 ∨
    (a.1 < b.1 ∧ finRotate p a.2 = b.2) ∨
    (b.1 < a.1 ∧ finRotate p b.2 = a.2)

theorem matchingPair_symm {m p : ℕ} {a b : Fin m × Fin p}
    (h : MatchingPair a b) : MatchingPair b a := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

/-- All internal cliques and two cyclic matchings per core tree edge. -/
def certificate {m : ℕ} (T : SimpleGraph (Fin m)) (p : ℕ) :
    SimpleGraph (Fin m × Fin p) where
  Adj a b := (a.1 = b.1 ∧ a.2 ≠ b.2) ∨
    (T.Adj a.1 b.1 ∧ MatchingPair a b)
  symm := ⟨by
    intro a b h
    rcases h with ⟨hbase,hindex⟩ | ⟨hcore,hmatch⟩
    · exact Or.inl ⟨hbase.symm,hindex.symm⟩
    · exact Or.inr ⟨hcore.symm,matchingPair_symm hmatch⟩⟩
  loopless := ⟨by intro a h; rcases h with h | h <;> simp_all⟩

@[simp] theorem graph_adj {m p : ℕ} (G : SimpleGraph (Fin m))
    (a b : Fin m × Fin p) :
    (graph G p).Adj a b ↔ (a.1=b.1 ∧ a.2≠b.2) ∨ G.Adj a.1 b.1 := Iff.rfl

@[simp] theorem certificate_adj {m p : ℕ} (T : SimpleGraph (Fin m))
    (a b : Fin m × Fin p) :
    (certificate T p).Adj a b ↔ (a.1=b.1 ∧ a.2≠b.2) ∨
      (T.Adj a.1 b.1 ∧ MatchingPair a b) := Iff.rfl

theorem certificate_le {m p : ℕ} {G T : SimpleGraph (Fin m)}
    (hTG : T ≤ G) : certificate T p ≤ graph G p := by
  intro a b h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (hTG h.1)

theorem internal_adj {m p : ℕ} (T : SimpleGraph (Fin m)) (u : Fin m)
    {i j : Fin p} (hij : i≠j) : (certificate T p).Adj (u,i) (u,j) :=
  Or.inl ⟨rfl,hij⟩

theorem identity_adj {m p : ℕ} {T : SimpleGraph (Fin m)}
    {u v : Fin m} (huv : T.Adj u v) (i : Fin p) :
    (certificate T p).Adj (u,i) (v,i) :=
  Or.inr ⟨huv,Or.inl rfl⟩

theorem shift_adj {m p : ℕ} {T : SimpleGraph (Fin m)}
    {u v : Fin m} (huv : T.Adj u v) (horder : u<v) (i : Fin p) :
    (certificate T p).Adj (u,i) (v,finRotate p i) :=
  Or.inr ⟨huv,Or.inr (Or.inl ⟨horder,rfl⟩)⟩

end LightEFTSpanners.CorrectedCloud
