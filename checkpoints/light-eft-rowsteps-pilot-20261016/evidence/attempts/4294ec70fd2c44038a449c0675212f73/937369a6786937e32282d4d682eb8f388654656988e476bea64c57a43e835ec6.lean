import LightEFTSpanners.NativeLevelExchangePreservation

namespace LightEFTSpanners.MultigraphCuts
variable {V E C : Type*}
attribute [local instance] Classical.propDecidable

/-- Swap the colors of exactly two original edge identities. -/
noncomputable def exchangedColor (color : E → C) (e d : E) (x : E) : C :=
  if x=e then color d else if x=d then color e else color x

/-- The earlier color gains e and loses d, with no parallel identities merged. -/
theorem exchangedColor_first (color : E → C) {e d : E} (hdiff : color e≠color d) :
    {x | exchangedColor color e d x=color d}=
      insert e ({x | color x=color d}\{d}) := by
  ext x
  by_cases hxe : x=e <;> by_cases hxd : x=d <;> simp_all [exchangedColor]

/-- The last color loses e and gains d. -/
theorem exchangedColor_last (color : E → C) {e d : E} (hdiff : color e≠color d) :
    {x | exchangedColor color e d x=color e}=
      insert d ({x | color x=color e}\{e}) := by
  ext x
  by_cases hxe : x=e <;> by_cases hxd : x=d <;> simp_all [exchangedColor,Ne.symm hdiff]

theorem exchangedColor_other (color : E → C) (e d : E) {c : C}
    (he : c≠color e) (hd : c≠color d) :
    {x | exchangedColor color e d x=c}={x | color x=c} := by
  ext x
  by_cases hxe : x=e <;> by_cases hxd : x=d <;> simp_all [exchangedColor,Ne.symm he,Ne.symm hd]

/-- Native restriction and original-identity deletion agree exactly with the
corresponding edge-set difference; actual vertices are unchanged. -/
theorem native_delete_restrict (G : Graph V E) (F D : Set E) :
    (G.restrict F).deleteEdges D=G.restrict (F\D) := by
  have hcomp : Graph.Compatible ((G.restrict F).deleteEdges D) (G.restrict (F\D)) :=
    Graph.Compatible.of_le_le (G:=G)
      (Graph.deleteEdges_le.trans Graph.restrict_le) Graph.restrict_le
  refine Graph.Compatible.ext rfl ?_ hcomp
  ext e
  simp only [Graph.edgeSet_deleteEdges,Graph.edgeSet_restrict,Set.mem_sdiff,Set.mem_inter_iff]
  tauto
/-- The actual earlier-color subgraph after the swap is precisely its original
subgraph with e inserted and d deleted. This equality retains original edge IDs. -/
theorem exchanged_first_graph (G : Graph V E) (color : E → C) {e d : E}
    (hdiff : color e≠color d) :
    G.restrict {x | exchangedColor color e d x=color d}=
      (G.restrict (insert e {x | color x=color d})).deleteEdges {d} := by
  rw [native_delete_restrict,exchangedColor_first color hdiff]
  congr 1
  have hed : e≠d := fun h => hdiff (congrArg color h)
  ext x
  by_cases hxe : x=e <;> by_cases hxd : x=d <;> simp_all

/-- The actual last-color subgraph after the swap is precisely the old one
with d inserted and e deleted. -/
theorem exchanged_last_graph (G : Graph V E) (color : E → C) {e d : E}
    (hdiff : color e≠color d) :
    G.restrict {x | exchangedColor color e d x=color e}=
      (G.restrict (insert d {x | color x=color e})).deleteEdges {e} := by
  rw [native_delete_restrict,exchangedColor_last color hdiff]
  congr 1
  have hde : d≠e := fun h => hdiff (congrArg color h.symm)
  ext x
  by_cases hxe : x=e <;> by_cases hxd : x=d <;> simp_all
/-- Every old within-stage colored connection survives the concrete swap once
both actual replacement routes and exact split boundaries are supplied. -/
theorem exchangedColor_preserves_stages (G : Graph V E) (color : E → C)
    {e d : E} (hdiff : color e≠color d)
    (R : ℕ → Setoid G.vertexSet) (hR : Antitone R) (me md : ℕ)
    (hext : ¬edgeInside G (R (me+1)) e)
    (hdxt : ¬edgeInside G (R (md+1)) d)
    (eroute : ∀ u v : G.vertexSet,G.IsLink e u.val v.val →
      (blockGraph (G.restrict {x | exchangedColor color e d x=color e}).toSimpleGraph (R me)).Reachable u v)
    (droute : ∀ u v : G.vertexSet,G.IsLink d u.val v.val →
      (blockGraph (G.restrict {x | exchangedColor color e d x=color d}).toSimpleGraph (R md)).Reachable u v)
    (c : C) (i : ℕ) {a b : G.vertexSet}
    (hr : (blockGraph (G.restrict {x | color x=c}).toSimpleGraph (R i)).Reachable a b) :
    (blockGraph (G.restrict {x | exchangedColor color e d x=c}).toSimpleGraph (R i)).Reachable a b := by
  by_cases hce : c=color e
  · subst c
    apply native_level_exchange_preserves_all_stages G _ _ e R hR me ?_ hext eroute i hr
    rw [exchangedColor_last color hdiff]
    exact Set.subset_insert _ _
  · by_cases hcd : c=color d
    · subst c
      apply native_level_exchange_preserves_all_stages G _ _ d R hR md ?_ hdxt droute i hr
      rw [exchangedColor_first color hdiff]
      exact Set.subset_insert _ _
    · have hp := congrArg (fun S : Set E =>
        (blockGraph (G.restrict S).toSimpleGraph (R i)).Reachable a b)
        (exchangedColor_other color e d hce hcd)
      exact hp.mpr hr
/-- Once the changed earlier color is certified, the literal two-identity
swap preserves the entire family of earlier spanning trees. Other earlier
colors keep exactly the same native original-edge subgraph. -/
theorem exchanged_earlier_trees (G : Graph V E) {k : ℕ}
    (color : E → Fin (k+1)) {e d : E} (c0 : Fin k)
    (he : color e=Fin.last k) (hd : color d=c0.castSucc)
    (hchanged : (∀ q∈(G.restrict {x | exchangedColor color e d x=c0.castSucc}).edgeSet,
      (G.restrict {x | exchangedColor color e d x=c0.castSucc}).IsBridge q) ∧
      (G.restrict {x | exchangedColor color e d x=c0.castSucc}).toSimpleGraph.Connected)
    (htrees : ∀ c : Fin k,(∀ q∈(G.restrict {x | color x=c.castSucc}).edgeSet,
      (G.restrict {x | color x=c.castSucc}).IsBridge q) ∧
      (G.restrict {x | color x=c.castSucc}).toSimpleGraph.Connected) :
    ∀ c : Fin k,(∀ q∈(G.restrict {x | exchangedColor color e d x=c.castSucc}).edgeSet,
      (G.restrict {x | exchangedColor color e d x=c.castSucc}).IsBridge q) ∧
      (G.restrict {x | exchangedColor color e d x=c.castSucc}).toSimpleGraph.Connected := by
  intro c
  by_cases hc : c=c0
  · subst c
    exact hchanged
  · have hce : c.castSucc≠color e := by
      rw [he]
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castSucc,Fin.val_last] at hv
      exact c.isLt.ne hv
    have hcd : c.castSucc≠color d := by
      rw [hd]
      intro hh
      exact hc (Fin.ext (congrArg (fun x : Fin (k+1) => x.val) hh))
    have hp := congrArg (fun S : Set E =>
      (∀ q∈(G.restrict S).edgeSet,(G.restrict S).IsBridge q) ∧
        (G.restrict S).toSimpleGraph.Connected) (exchangedColor_other color e d hce hcd)
    exact hp.mpr (htrees c)
end LightEFTSpanners.MultigraphCuts
