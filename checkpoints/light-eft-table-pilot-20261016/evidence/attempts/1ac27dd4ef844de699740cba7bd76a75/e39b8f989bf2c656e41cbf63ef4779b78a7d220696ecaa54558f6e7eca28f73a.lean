import LightEFTSpanners.NativeEdgeLevels

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- If an actual last-color edge is separated by the next least-color
refinement, the selected color is one of the earlier colors. The returned
color is exactly the minimum splitting color, not an arbitrary witness. -/
theorem exists_earlier_splitting_color (G : Graph V E) {k : ℕ}
    (color : E → Fin (k+1)) (R : Setoid G.vertexSet) {e : E}
    (hcolor : color e=Fin.last k)
    (hin : edgeInside G R e)
    (hnext : ¬edgeInside G
      (refinementStep (fun c => (G.restrict {d | color d=c}).toSimpleGraph) R) e) :
    let H : Fin (k+1) → SimpleGraph G.vertexSet := fun c => (G.restrict {d | color d=c}).toSimpleGraph
    ∃ (h : (splitColors H R).Nonempty) (c : Fin k),
      c.castSucc=(splitColors H R).min' h ∧
      refinementStep H R=componentRefinement (H c.castSucc) R ∧
      ¬edgeInside G (componentRefinement (H c.castSucc) R) e := by
  classical
  intro H
  have hsplit : (splitColors H R).Nonempty := by
    by_contra hn
    have heq : refinementStep H R=R := by simp only [refinementStep,dite_eq_right hn]
    exact hnext ((congrArg (fun S => edgeInside G S e) heq).mpr hin)
  let c0 := (splitColors H R).min' hsplit
  have hstep : refinementStep H R=componentRefinement (H c0) R := by
    simp only [refinementStep,dite_eq_left hsplit,c0]
  have hc0 : c0≠Fin.last k := by
    intro hlast
    obtain ⟨u,v,huv,hR⟩ := hin
    have hr : (blockGraph (H (Fin.last k)) R).Reachable u v := by
      by_cases huvEq : u=v
      · rw [huvEq]
      · exact (show (blockGraph (H (Fin.last k)) R).Adj u v from
          ⟨⟨huvEq,e,⟨hcolor,huv⟩⟩,hR⟩).reachable
    have hedge : edgeInside G (componentRefinement (H c0) R) e := by
      refine ⟨u,v,huv,?_⟩
      change (blockGraph (H c0) R).Reachable u v
      simpa only [hlast] using hr
    exact hnext ((congrArg (fun S => edgeInside G S e) hstep).mpr hedge)
  obtain ⟨c,hc⟩ := Fin.eq_castSucc_of_ne_last hc0
  refine ⟨hsplit,c,hc,?_,?_⟩
  · simpa only [hc] using hstep
  · intro hh
    exact hnext ((congrArg (fun S => edgeInside G S e) hstep).mpr (by simpa only [hc] using hh))
end LightEFTSpanners.MultigraphCuts
