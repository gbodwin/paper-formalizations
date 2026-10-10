import LightEFTSpanners.ParallelSubdivision
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset
variable {V I : Type*} (C : SimpleGraph V)

/-- Project an actual subdivision subgraph using only complete two-half-edge
paths. A dangling half-edge contributes no original edge. -/
def coreProjection (T : SimpleGraph (Vertex (I:=I) C)) : SimpleGraph V where
  Adj a b := a≠b ∧ ∃ (d : C.edgeSet) (j : I),
    T.Adj (Sum.inl a) (Sum.inr (d,j)) ∧ T.Adj (Sum.inr (d,j)) (Sum.inl b)
  symm := ⟨by rintro a b ⟨hne,d,j,ha,hb⟩; exact ⟨hne.symm,d,j,hb.symm,ha.symm⟩⟩
  loopless := ⟨by rintro a ⟨hne,_⟩; exact hne rfl⟩

/-- Complete subdivided paths project to genuine original edges. -/
theorem coreProjection_le {T : SimpleGraph (Vertex (I:=I) C)}
    (hT : T≤graph C) : coreProjection C T≤C := by
  rintro a b ⟨hne,d,j,ha,hb⟩
  have ha' : a∈(d:Sym2 V) := hT ha
  have hb' : b∈(d:Sym2 V) := hT hb
  have hd : (d:Sym2 V)=s(a,b) := (Sym2.mem_and_mem_iff hne).mp ⟨ha',hb'⟩
  exact (mem_edgeSet C).mp (hd ▸ d.2)

/-- A core-to-core walk in a subdivision subgraph projects to actual
reachability. Reversing at the same endpoint is a stationary projected step. -/
theorem walk_coreProjection {T : SimpleGraph (Vertex (I:=I) C)}
    (hT : T≤graph C) {u v : V} (p : T.Walk (Sum.inl u) (Sum.inl v)) :
    (coreProjection C T).Reachable u v := by
  suffices ∀ n : ℕ, ∀ u : V, ∀ p : T.Walk (Sum.inl u) (Sum.inl v),
      p.length=n → (coreProjection C T).Reachable u v from this p.length u p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u p hlen
    cases p with
    | nil => exact Reachable.refl _
    | @cons x y z hxy p =>
      cases y with
      | inl b => exact False.elim (hT hxy)
      | inr d =>
        cases p with
        | @cons x y z hdy p =>
          cases y with
          | inr e => exact False.elim (hT hdy)
          | inl b =>
            have hlt : p.length<n := by
              simp only [Walk.length_cons] at hlen
              omega
            have hr := ih p.length hlt b p rfl
            by_cases heq : u=b
            · subst b; exact hr
            · exact (show (coreProjection C T).Adj u b from
                ⟨heq,d.1,d.2,hxy,hdy⟩).reachable.trans hr

/-- Trimming the projection to a native spanning forest preserves all actual
core reachabilities while only removing original edges. -/
theorem exists_core_forest {T : SimpleGraph (Vertex (I:=I) C)}
    (hT : T≤graph C) : ∃ F : SimpleGraph V,
    F≤coreProjection C T ∧ F≤C ∧ F.IsAcyclic ∧
      ∀ u v, T.Reachable (Sum.inl u) (Sum.inl v) → F.Reachable u v := by
  obtain ⟨F,hF,hacyc,hreach⟩ := (coreProjection C T).exists_isAcyclic_reachable_eq_le
  refine ⟨F,hF,hF.trans (coreProjection_le C hT),hacyc,?_⟩
  intro u v ⟨p⟩
  rw [hreach]
  exact walk_coreProjection C hT p
end LightEFTSpanners.ParallelSubdivision
