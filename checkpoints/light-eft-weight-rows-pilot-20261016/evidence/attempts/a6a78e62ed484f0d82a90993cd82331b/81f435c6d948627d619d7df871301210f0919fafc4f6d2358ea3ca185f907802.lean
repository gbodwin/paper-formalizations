import LightEFTSpanners.NativeTreeExchange
import LightEFTSpanners.NativeMinimumCycleLevel
import LightEFTSpanners.NativeEdgeLevelTransport

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

omit [Fintype E] in
/-- The inserted edge is a genuine nonbridge: the original connected tree
supplies a route after deleting exactly that new identity. -/
theorem inserted_edge_nonbridge (G : Graph V E) (F : Finset E) {e : E}
    (heF : e∉F) (hc : (G.restrict (F:Set E)).toSimpleGraph.Connected)
    {a b : G.vertexSet} (he : G.IsLink e a.val b.val) :
    ¬(G.restrict ((insert e F:Finset E):Set E)).IsBridge e := by
  let H := G.restrict ((insert e F:Finset E):Set E)
  have heH : H.IsLink e a.val b.val := ⟨mem_insert_self _ _,he⟩
  intro hb
  apply (bridge_iff_not_reachable_delete H heH).mp hb
  apply (hc.preconnected a b).mono
  intro x y hxy
  obtain ⟨hne,d,hd,hl⟩ := hxy
  refine ⟨hne,d,⟨mem_insert_of_mem hd,hl⟩,?_⟩
  intro hde
  exact heF (by simpa only [Set.mem_singleton_iff.mp hde,mem_coe] using hd)

omit [Fintype E] in
/-- A tree cannot create a new within-block route merely by inserting and then
removing the same original edge identity. -/
theorem no_block_route_delete_insert (G : Graph V E) (F : Finset E)
    (R : Setoid G.vertexSet) {e : E} {a b : G.vertexSet}
    (hn : ¬(blockGraph (G.restrict (F:Set E)).toSimpleGraph R).Reachable a b) :
    ¬(blockGraph ((G.restrict ((insert e F:Finset E):Set E)).deleteEdges {e}).toSimpleGraph R).Reachable a b := by
  intro hr
  apply hn
  apply hr.mono
  intro x y hxy
  obtain ⟨⟨hne,d,⟨hd,hl⟩,hde⟩,hR⟩ := hxy
  have hdF : d∈F := (mem_insert.mp hd).resolve_left (by simpa only [Set.mem_singleton_iff] using hde)
  exact ⟨⟨hne,d,hdF,hl⟩,hR⟩

/-- Construct the source exchange edge from an actual tree and a partition
block that separates the new edge's endpoints in that tree. The witness is a
strictly earlier finite-level nonbridge, its replacement route is genuinely
inside its own level block, and deleting it after insertion gives a true native
spanning tree. Neither the exchange edge nor either replacement route is an
input. The finite terminal here is the original edge's internal stage m. -/
theorem exists_lower_tree_exchange (G : Graph V E) [Finite G.vertexSet]
    (F : Finset E) (hF : (F:Set E)⊆G.edgeSet) {e : E}
    (he : e∈G.edgeSet) (heF : e∉F)
    (hforest : ∀ q∈(G.restrict (F:Set E)).edgeSet,(G.restrict (F:Set E)).IsBridge q)
    (hconn : (G.restrict (F:Set E)).toSimpleGraph.Connected)
    (R : ℕ → Setoid G.vertexSet) (hR : Antitone R) (hzero : R 0=⊤) (m : ℕ)
    (hein : edgeInside G (R m) e)
    (hn : ∀ a b : G.vertexSet,G.IsLink e a.val b.val →
      ¬(blockGraph (G.restrict (F:Set E)).toSimpleGraph (R m)).Reachable a b) :
    let H := G.restrict ((insert e F:Finset E):Set E)
    ∃ d∈F,d≠e ∧ ¬H.IsBridge d ∧ edgeLevel H R m d<m ∧
      edgeInside H (R (edgeLevel H R m d)) d ∧
      (∀ a b : G.vertexSet,H.IsLink d a.val b.val →
        (blockGraph (H.deleteEdges {d}).toSimpleGraph (R (edgeLevel H R m d))).Reachable a b) ∧
      (∀ q∈(H.deleteEdges {d}).edgeSet,(H.deleteEdges {d}).IsBridge q) ∧
      (H.deleteEdges {d}).toSimpleGraph.Connected ∧
      Nat.card (H.deleteEdges {d}).edgeSet=F.card := by
  classical
  intro H
  obtain ⟨a,b,heab,heR⟩ := hein
  have hen := inserted_edge_nonbridge G F heF hconn heab
  have heH : H.IsLink e a.val b.val := ⟨mem_insert_self _ _,heab⟩
  have hexternal := exists_external_nonbridge_of_no_block_route H (R m) heH hen
    (no_block_route_delete_insert G F (R m) (hn a b heab))
  obtain ⟨d,hdH,hnd,hdlt,hdin,hdnext,hmin,hroute⟩ :=
    exists_minimum_cycle_level H R hR hzero m hexternal
  have hde : d≠e := by
    intro hh
    subst d
    have hm : m∈internalStages H R m e := mem_filter.mpr
      ⟨mem_range.mpr (by omega),a,b,heH,heR⟩
    have hh := le_max' (internalStages H R m e) m hm
    have hnon : (internalStages H R m e).Nonempty := ⟨m,hm⟩
    have hlev : edgeLevel H R m e=(internalStages H R m e).max' hnon := by
      simp only [edgeLevel,dite_eq_left hnon]
    rw [←hlev] at hh
    omega
  have hdF : d∈F := (mem_insert.mp hdH.2).resolve_left hde
  obtain ⟨hbf,hc,hcard⟩ := native_tree_exchange G F hF he heF hdF hforest hconn hnd
  exact ⟨d,hdF,hde,hnd,hdlt,hdin,hroute,hbf,hc,hcard⟩
/-- The constructed exchange uses exactly the original graph's global finite
level function, not a different level hidden by restriction or truncation. -/
theorem exists_lower_tree_exchange_global (G : Graph V E) [Finite G.vertexSet]
    (F : Finset E) (hF : (F:Set E)⊆G.edgeSet) {e : E}
    (he : e∈G.edgeSet) (heF : e∉F)
    (hforest : ∀ q∈(G.restrict (F:Set E)).edgeSet,(G.restrict (F:Set E)).IsBridge q)
    (hconn : (G.restrict (F:Set E)).toSimpleGraph.Connected)
    (R : ℕ → Setoid G.vertexSet) (hR : Antitone R) (hzero : R 0=⊤)
    (m N : ℕ) (hmN : m≤N) (hein : edgeInside G (R m) e)
    (hn : ∀ a b : G.vertexSet,G.IsLink e a.val b.val →
      ¬(blockGraph (G.restrict (F:Set E)).toSimpleGraph (R m)).Reachable a b) :
    let H := G.restrict ((insert e F:Finset E):Set E)
    ∃ d∈F,d≠e ∧ ¬H.IsBridge d ∧ edgeLevel G R N d<m ∧
      edgeInside H (R (edgeLevel G R N d)) d ∧
      (∀ a b : G.vertexSet,H.IsLink d a.val b.val →
        (blockGraph (H.deleteEdges {d}).toSimpleGraph (R (edgeLevel G R N d))).Reachable a b) ∧
      (∀ q∈(H.deleteEdges {d}).edgeSet,(H.deleteEdges {d}).IsBridge q) ∧
      (H.deleteEdges {d}).toSimpleGraph.Connected ∧
      Nat.card (H.deleteEdges {d}).edgeSet=F.card := by
  classical
  intro H
  obtain ⟨d,hdF,hde,hnd,hdlt,hdin,hroute,hbf,hc,hcard⟩ :=
    exists_lower_tree_exchange G F hF he heF hforest hconn R hR hzero m hein hn
  have hdset : d∈((insert e F:Finset E):Set E) := mem_insert_of_mem hdF
  have houtH := not_inside_terminal_of_level_lt H R m hdlt
  have houtG : ¬edgeInside G (R m) d := by
    change ¬edgeInside (G.restrict ((insert e F:Finset E):Set E)) (R m) d at houtH
    simpa only [edgeInside_restrict_iff G _ (R m) hdset] using houtH
  have hlevel : edgeLevel G R N d=edgeLevel H R m d := by
    rw [edgeLevel_truncate G R hR hmN houtG]
    exact (edgeLevel_restrict G _ R m hdset).symm
  refine ⟨d,hdF,hde,hnd,?_⟩
  rw [hlevel]
  exact ⟨hdlt,hdin,hroute,hbf,hc,hcard⟩
end LightEFTSpanners.MultigraphCuts
