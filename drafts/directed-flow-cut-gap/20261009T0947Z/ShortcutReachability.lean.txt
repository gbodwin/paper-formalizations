import DirectedFlowCutGap.ShortcutContraction

/-!
# Shortcut edges as finite restricted reachability

A shortcut does not require enumerating simple paths. For fixed surviving
endpoints, retain original edges whose tail is the source or a removed vertex,
and whose head is the target or a removed vertex. A path in this graph has only
removed internal vertices. Unequal endpoints exclude the zero-length path and
match the frozen loopless shortcut construction exactly.

This is the semantic bridge for subsequent Boolean-array reachability code;
no running-time claim is made by this module itself.
-/

namespace DirectedFlowCutGap.ShortcutReachability

variable {V : Type*} [DecidableEq V]

def restricted (G : Digraph V) (S : Finset V) (s t : V) : Digraph V where
  Adj u v := G.Adj u v ∧ (u=s ∨ u∈S) ∧ (v=t ∨ v∈S)

/-- A witness with removed interiors is a path in the restricted graph. -/
def restrictPath {G : Digraph V} {S : Finset V} {s t : V}
    (p : SimplePath G s t) (hS : p.internalVertices ⊆ S) :
    SimplePath (restricted G S s t) s t where
  edgeLength := p.edgeLength
  vertex := p.vertex
  source_eq := p.source_eq
  target_eq := p.target_eq
  injective := p.injective
  adjacent i := by
    refine ⟨p.adjacent i,?_,?_⟩
    · by_cases hs : p.vertex i.castSucc=s
      · exact Or.inl hs
      · apply Or.inr
        apply hS
        apply (p.mem_internalVertices _).mpr
        refine ⟨⟨i.castSucc,rfl⟩,hs,?_⟩
        intro ht
        have he := p.injective (ht.trans p.target_eq.symm)
        have hv := congrArg Fin.val he
        simp only [Fin.val_castSucc,Fin.val_last] at hv
        omega
    · by_cases ht : p.vertex i.succ=t
      · exact Or.inl ht
      · apply Or.inr
        apply hS
        apply (p.mem_internalVertices _).mpr
        refine ⟨⟨i.succ,rfl⟩,?_,ht⟩
        intro hs
        have he := p.injective (hs.trans p.source_eq.symm)
        have hv := congrArg Fin.val he
        simp only [Fin.val_succ,Fin.val_zero] at hv
        omega

/-- Forgetting restrictions retains the exact vertex sequence. -/
def forgetPath {G : Digraph V} {S : Finset V} {s t : V}
    (p : SimplePath (restricted G S s t) s t) : SimplePath G s t where
  edgeLength := p.edgeLength
  vertex := p.vertex
  source_eq := p.source_eq
  target_eq := p.target_eq
  injective := p.injective
  adjacent i := (p.adjacent i).1

theorem restricted_internal {G : Digraph V} {S : Finset V} {s t : V}
    (p : SimplePath (restricted G S s t) s t) : (forgetPath p).internalVertices ⊆ S := by
  intro v hv
  obtain ⟨⟨i,hi⟩,hs,ht⟩ := ((forgetPath p).mem_internalVertices v).mp hv
  have hib : i.val < p.edgeLength+1 := i.isLt
  have hi' : i.val < p.edgeLength := by
    by_contra h
    have he : i=Fin.last p.edgeLength := Fin.ext (by simp; omega)
    exact ht (hi.symm.trans ((congrArg p.vertex he).trans p.target_eq))
  let j : Fin p.edgeLength := ⟨i.val,hi'⟩
  have hj : j.castSucc=i := Fin.ext rfl
  have hadj := (p.adjacent j).2.1
  change p.vertex j.castSucc=s ∨ p.vertex j.castSucc∈S at hadj
  rw [hj] at hadj
  change p.vertex i=v at hi
  rw [hi] at hadj
  exact hadj.resolve_left hs

omit [DecidableEq V] in
private theorem positive_of_ne {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (h : s≠t) : 0 < p.edgeLength := by
  by_contra hn
  have hz : p.edgeLength=0 := by omega
  have hi : (0 : Fin (p.edgeLength+1))=Fin.last p.edgeLength :=
    Fin.ext (by simp [hz])
  exact h (p.source_eq.symm.trans ((congrArg p.vertex hi).trans p.target_eq))

/-- Exact finite shortcut semantics, suitable for a proved reachability
algorithm on the concrete restricted adjacency matrix. -/
theorem shortcut_iff_restricted {G : Digraph V} {S : Finset V}
    (s t : ShortcutContraction.Survivor S) :
    (ShortcutContraction.graph G S).Adj s t ↔
      s.val≠t.val ∧ Nonempty (SimplePath (restricted G S s.val t.val) s.val t.val) := by
  constructor
  · intro h
    have hne : s.val≠t.val := by
      intro he
      have hst : s=t := Subtype.ext he
      subst t
      exact ShortcutContraction.not_adj_self G S s h
    obtain ⟨p,_,hS⟩ := h
    exact ⟨hne,⟨restrictPath p hS⟩⟩
  · rintro ⟨hne,⟨p⟩⟩
    exact ⟨forgetPath p,positive_of_ne (forgetPath p) hne,restricted_internal p⟩

end DirectedFlowCutGap.ShortcutReachability
