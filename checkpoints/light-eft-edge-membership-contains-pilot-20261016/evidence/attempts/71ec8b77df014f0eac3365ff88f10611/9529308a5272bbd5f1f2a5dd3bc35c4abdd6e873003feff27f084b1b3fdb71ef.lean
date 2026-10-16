import LightEFTSpanners.NativeBridgeSemantics

namespace LightEFTSpanners.MultigraphCuts
open Finset symmDiff
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Any finite set of native bridges is itself an actual cut, by symmetric
difference of the singleton bridge cuts. No path/cycle theorem is assumed. -/
theorem finite_bridges_isEdgeCut (G : Graph V E) (F : Finset E)
    (hb : ∀ e∈F,G.IsBridge e) : G.IsEdgeCut (F:Set E) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅,by ext e; simp [Graph.edgeCut]⟩
  | @insert e F he ih =>
    have hF := ih (fun d hd => hb d (mem_insert_of_mem hd))
    have hsym := (hb e (mem_insert_self e F)).symmDiff hF
    have heq : ({e}:Set E) ∆ (F:Set E)=(insert e F:Set E) := by
      ext d
      simp only [Set.mem_symmDiff,Set.mem_singleton_iff,mem_coe,Set.mem_insert_iff]
      by_cases hd : d=e
      · subst d; simp [he]
      · simp [hd]
    simpa only [heq,coe_insert] using hsym

/-- A finite cut whose other edges are all bridges makes its remaining edge a
bridge too. This is the exact parity-of-cuts fact needed to retain cycles when
all bridge identities are discarded. -/
theorem bridge_of_cut_other_bridges [Fintype E] (G : Graph V E) (S : Set V)
    {e : E} (he : e∈G.edgeCut S)
    (hb : ∀ d∈G.edgeCut S,d≠e → G.IsBridge d) : G.IsBridge e := by
  classical
  let F := (G.edgeCut S).toFinset.erase e
  have hF : G.IsEdgeCut (F:Set E) := finite_bridges_isEdgeCut G F (by
    intro d hd
    obtain ⟨hne,hd⟩ := mem_erase.mp hd
    exact hb d (Set.mem_toFinset.mp hd) hne)
  have hC : G.IsEdgeCut (G.edgeCut S) := ⟨S,rfl⟩
  have hsym := hC.symmDiff hF
  have heq : G.edgeCut S ∆ (F:Set E)={e} := by
    ext d
    simp only [Set.mem_symmDiff,mem_coe,F,mem_erase,Set.mem_toFinset,Set.mem_singleton_iff]
    by_cases hd : d=e
    · subst d; simp [he]
    · simp [hd]
  change G.IsEdgeCut {e}
  rwa [heq] at hsym

/-- The actual original nonbridge identities, retaining all actual vertices. -/
noncomputable def nonbridgeCore (G : Graph V E) : Graph V E :=
  G.restrict {e | ¬G.IsBridge e}

/-- Removing all bridge identities does not turn a nonbridge into a bridge.
The finite-edge assumption controls the cut symmetric-difference argument. -/
theorem nonbridgeCore_has_no_bridges [Fintype E] (G : Graph V E)
    {e : E} (he : e∈(nonbridgeCore G).edgeSet) : ¬(nonbridgeCore G).IsBridge e := by
  rintro ⟨S,hS⟩
  have heC : e∈G.edgeCut S := by
    have hm : e∈(nonbridgeCore G).edgeCut S := by rw [hS]; exact Set.mem_singleton e
    obtain ⟨u,v,hlink,hu,hv⟩ := hm
    exact ⟨u,v,hlink.2,hu,hv⟩
  have hebridge : G.IsBridge e := bridge_of_cut_other_bridges G S heC (by
    intro d hd hde
    by_contra hnb
    have hdC : d∈(nonbridgeCore G).edgeCut S := by
      obtain ⟨u,v,hlink,hu,hv⟩ := hd
      exact ⟨u,v,⟨hnb,hlink⟩,hu,hv⟩
    have hde' : d=e := by simpa only [hS,Set.mem_singleton_iff] using hdC
    exact hde hde')
  exact he.2 hebridge

/-- Every nonbridge edge has an alternate actual route consisting solely of
other nonbridge identities. This supplies the source's minimum-level cycle
containment without silently collapsing a parallel two-edge cycle. -/
theorem nonbridge_alternate_route_in_core [Fintype E] (G : Graph V E)
    {e : E} {u v : V} (he : G.IsLink e u v) (hnb : ¬G.IsBridge e) :
    ((nonbridgeCore G).deleteEdges {e}).toSimpleGraph.Reachable
      ⟨u,he.left_mem⟩ ⟨v,he.right_mem⟩ := by
  have hlink : (nonbridgeCore G).IsLink e u v := ⟨hnb,he⟩
  by_contra hn
  exact nonbridgeCore_has_no_bridges G hlink.edge_mem
    ((bridge_iff_not_reachable_delete (nonbridgeCore G) hlink).mpr hn)
end LightEFTSpanners.MultigraphCuts
