import LightEFTSpanners.NativeForestPacking

namespace LightEFTSpanners.EvenSplitting
open MultigraphCuts SimpleGraph
variable {V W E : Type*} [Fintype E]

/-- An injective native vertex map preserves the exact fault threshold in
both directions. Image cuts pull back to the original cut as sets of edge IDs. -/
theorem faultConnected_of_injective_map (G : Graph V E) (f : V → W)
    (hf : Function.Injective f) {k : ℕ} {x y : G.vertexSet}
    (h : FaultConnected (G.map f) k (mapVertex G f x) (mapVertex G f y)) :
    FaultConnected G k x y := by
  apply faultConnected_of_cut_lower
  intro S hx hy
  have hy' : f y.val∉f '' S := by
    rintro ⟨z,hz,hzy⟩
    exact hy (hf hzy ▸ hz)
  have hc := faultConnected_le_cut (G.map f) h (f '' S) ⟨x.val,hx,rfl⟩ hy'
  rw [edgeCut_map,Set.preimage_image_eq _ hf] at hc
  exact hc

/-- Injective vertex relabeling preserves the genuine forest-packing goal.
The returned members still use original edge identities, and actual member
connections are lifted rather than inferred from an abstract quotient oracle. -/
theorem forestPacking_of_injective_map (G : Graph V E) (f : V → W)
    (hf : Function.Injective f) (k : ℕ) (hp : HasNativeForestPacking (G.map f) k) :
    HasNativeForestPacking G k := by
  obtain ⟨A,hA,hd,hj⟩ := hp
  have htd : Pairwise (fun (_ _ : Fin k) => Disjoint (∅:Set E) ∅) := by intro _ _ _; simp
  have hi (c : Fin k) (e : E) (h : e∈(∅:Set E)) :
      ∃ u v,G.IsLink e u v ∧ f u=f v := False.elim h
  have hc (c : Fin k) (x y : G.vertexSet) (h : f x.val=f y.val) :
      (G.restrict (∅:Set E)).toSimpleGraph.Reachable x y := by
    have hxy : x=y := Subtype.ext (hf h)
    subst y; exact Reachable.rfl
  obtain ⟨B,hB,hBd,hBj⟩ := lift_quotient_forest_family G f A (fun _ => ∅)
    (fun c => (hA c).1) (fun c => (hA c).2) hd htd hi hc
  refine ⟨B,fun c => (hB c).2,hBd,?_⟩
  intro c x y h
  have hr := hj c (mapVertex G f x) (mapVertex G f y) (faultConnected_map G f h)
  obtain ⟨_,_,hr'⟩ := hBj c x y ⟨(mapVertex G f x).property,(mapVertex G f y).property,hr⟩
  exact hr'
end LightEFTSpanners.EvenSplitting
