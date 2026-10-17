import LightEFTSpanners.NativeEdgeLevels
import LightEFTSpanners.NativeNonbridgeCore

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- A genuinely minimum-level native cycle edge exists whenever some
nonbridge crosses the terminal partition. Its alternate path is constructed
inside its own level block using the actual nonbridge core. This keeps parallel
two-edge cycles and does not assume a cycle or a replacement path. -/
theorem exists_minimum_cycle_level (G : Graph V E)
    (R : ℕ → Setoid G.vertexSet) (hR : Antitone R) (hzero : R 0=⊤) (N : ℕ)
    (hfinite : ∃ e∈G.edgeSet,¬G.IsBridge e ∧ ¬edgeInside G (R N) e) :
    ∃ e∈G.edgeSet,¬G.IsBridge e ∧ edgeLevel G R N e<N ∧
      edgeInside G (R (edgeLevel G R N e)) e ∧
      ¬edgeInside G (R (edgeLevel G R N e+1)) e ∧
      (∀ d∈G.edgeSet,¬G.IsBridge d → edgeLevel G R N e≤edgeLevel G R N d) ∧
      (∀ a b : G.vertexSet,G.IsLink e a.val b.val →
        (blockGraph (G.deleteEdges {e}).toSimpleGraph (R (edgeLevel G R N e))).Reachable a b) := by
  classical
  have hinitial : ∀ e∈G.edgeSet,edgeInside G (R 0) e := by
    intro e he
    obtain ⟨u,v,huv⟩ := Graph.exists_isLink_of_mem_edgeSet he
    exact ⟨⟨u,huv.left_mem⟩,⟨v,huv.right_mem⟩,huv,by rw [hzero]; trivial⟩
  let S : Finset E := univ.filter (fun e => e∈G.edgeSet ∧ ¬G.IsBridge e)
  obtain ⟨d,hd,hnd,hdlast⟩ := hfinite
  have hdS : d∈S := mem_filter.mpr ⟨mem_univ _,hd,hnd⟩
  obtain ⟨e,heS,hmin⟩ := S.exists_min_image (edgeLevel G R N) ⟨d,hdS⟩
  obtain ⟨_,heG,hne⟩ := mem_filter.mp heS
  have hminimum : ∀ c∈G.edgeSet,¬G.IsBridge c → edgeLevel G R N e≤edgeLevel G R N c := by
    intro c hc hnc
    exact hmin c (mem_filter.mpr ⟨mem_univ _,hc,hnc⟩)
  have hlt : edgeLevel G R N e<N :=
    (hminimum d hd hnd).trans_lt (finite_edgeLevel_boundary G R N (hinitial d hd) hdlast).1
  have hein := (mem_filter.mp (edgeLevel_mem G R N (hinitial e heG))).2
  have helast : ¬edgeInside G (R N) e := by
    intro hh
    have hm : N∈internalStages G R N e := mem_filter.mpr ⟨mem_range.mpr (by omega),hh⟩
    have hmax := le_max' (internalStages G R N e) N hm
    have hnonempty := internalStages_nonempty G R N (hinitial e heG)
    have hlevel : edgeLevel G R N e=(internalStages G R N e).max' hnonempty := by
      simp only [edgeLevel,dite_eq_left hnonempty]
    rw [← hlevel] at hmax
    omega
  have hboundary := finite_edgeLevel_boundary G R N (hinitial e heG) helast
  refine ⟨e,heG,hne,hlt,hein,hboundary.2.2,hminimum,?_⟩
  intro a b heab
  have hr := nonbridge_alternate_route_in_core G heab hne
  apply hr.mono
  intro x y hxy
  obtain ⟨hxyne,c,⟨hnc,hc⟩,hce⟩ := hxy
  have hcstage := (mem_filter.mp (edgeLevel_mem G R N (hinitial c hc.edge_mem))).2
  have hcinside := edgeInside_mono G (hR (hminimum c hc.edge_mem hnc)) hcstage
  exact ⟨⟨hxyne,c,hc,hce⟩,(edgeInside_iff G _ hc).mp hcinside⟩
end LightEFTSpanners.MultigraphCuts
