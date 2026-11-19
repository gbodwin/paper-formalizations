import OnlineReachabilityPreservers.Basic

/-! Reachability is invariant under embeddings of the vertex type. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Mapping the edges along an injection preserves and reflects reachability between mapped vertices. -/
theorem reach_relabel {V W : Type*} {G : Arcs V} (f : V ↪ W) {a b : V} :
    Reach (G.map (f.prodMap f)) (f a) (f b) ↔ Reach G a b := by
  constructor
  · have recover (w : W) (reach : Reach (G.map (f.prodMap f)) (f a) w) :
        ∃ v, f v = w ∧ Reach G a v := by
      induction reach with
      | refl => exact ⟨a, rfl, .refl⟩
      | @tail z y _ edge ih =>
        obtain ⟨v, eq, path⟩ := ih
        obtain ⟨e, member, same⟩ := mem_map.mp edge
        have first : e.1 = v := f.injective ((congrArg Prod.fst same).trans eq.symm)
        exact ⟨e.2, congrArg Prod.snd same, path.tail (by rwa [← first])⟩
    intro path
    obtain ⟨v, eq, h⟩ := recover (f b) path
    exact f.injective eq ▸ h
  · intro path
    induction path with
    | refl => exact .refl
    | tail _ edge ih => exact ih.tail (mem_map_of_mem _ edge)

end OnlineReachabilityPreservers
