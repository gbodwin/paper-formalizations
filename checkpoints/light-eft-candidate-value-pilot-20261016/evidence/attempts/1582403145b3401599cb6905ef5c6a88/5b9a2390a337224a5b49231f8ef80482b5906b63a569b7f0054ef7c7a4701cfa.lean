import LightEFTSpanners.NativeColorExchange
import LightEFTSpanners.NativeLowerExchange

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E C : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

omit [Fintype E] in
/-- Equality of the actual swapped color class with the constructed tree
exchange, even when the color function also labels unused ambient identities. -/
theorem exchanged_graph_eq_tree_exchange (G : Graph V E) (color : E → C)
    (F : Finset E) {e d : E} (hF : ∀ x∈G.edgeSet,x∈F ↔ color x=color d)
    (hdiff : color e≠color d) :
    G.restrict {x | exchangedColor color e d x=color d}=
      (G.restrict ((insert e F:Finset E):Set E)).deleteEdges {d} := by
  have hcomp : Graph.Compatible (G.restrict {x | exchangedColor color e d x=color d})
      ((G.restrict ((insert e F:Finset E):Set E)).deleteEdges {d}) :=
    Graph.Compatible.of_le_le (G:=G) Graph.restrict_le
      (Graph.deleteEdges_le.trans Graph.restrict_le)
  refine Graph.Compatible.ext rfl ?_ hcomp
  ext x
  by_cases hxG : x∈G.edgeSet
  · have hFx := hF x hxG
    have hed : e≠d := fun h => hdiff (congrArg color h)
    by_cases hxe : x=e <;> by_cases hxd : x=d <;>
      simp_all [Graph.edgeSet_restrict,Graph.edgeSet_deleteEdges,exchangedColor]
  · simp only [Graph.edgeSet_restrict,Graph.edgeSet_deleteEdges,Set.mem_inter_iff,
      Set.mem_sdiff,hxG,false_and]

/-- The actual lower-level exchange supplies the changed color's true native
spanning tree and its within-level replacement route. A concrete color function
is returned; the changed class is not identified only by a schematic bound. -/
theorem exists_actual_colored_tree_exchange (G : Graph V E) [Finite G.vertexSet]
    (color : E → C) (F : Finset E) (hF : (F:Set E)⊆G.edgeSet) (c : C)
    (hclass : ∀ x∈G.edgeSet,x∈F ↔ color x=c) {e : E}
    (he : e∈G.edgeSet) (hecolor : color e≠c)
    (hforest : ∀ q∈(G.restrict (F:Set E)).edgeSet,(G.restrict (F:Set E)).IsBridge q)
    (hconn : (G.restrict (F:Set E)).toSimpleGraph.Connected)
    (R : ℕ → Setoid G.vertexSet) (hR : Antitone R) (hzero : R 0=⊤)
    (m N : ℕ) (hmN : m≤N) (hein : edgeInside G (R m) e)
    (hn : ∀ a b : G.vertexSet,G.IsLink e a.val b.val →
      ¬(blockGraph (G.restrict (F:Set E)).toSimpleGraph (R m)).Reachable a b) :
    ∃ d∈F,color d=c ∧ d≠e ∧ edgeLevel G R N d<m ∧
      ¬edgeInside G (R (edgeLevel G R N d+1)) d ∧
      (∀ q∈(G.restrict {x | exchangedColor color e d x=c}).edgeSet,
        (G.restrict {x | exchangedColor color e d x=c}).IsBridge q) ∧
      (G.restrict {x | exchangedColor color e d x=c}).toSimpleGraph.Connected ∧
      (∀ a b : G.vertexSet,G.IsLink d a.val b.val →
        (blockGraph (G.restrict {x | exchangedColor color e d x=c}).toSimpleGraph
          (R (edgeLevel G R N d))).Reachable a b) := by
  classical
  have heF : e∉F := fun heF => hecolor ((hclass e he).mp heF)
  obtain ⟨d,hdF,hde,hnd,hdlt,hdin,hroute,hbf,hc,hcard⟩ :=
    exists_lower_tree_exchange_global G F hF he heF hforest hconn R hR hzero m N hmN hein hn
  have hdG : d∈G.edgeSet := hF hdF
  have hdcolor : color d=c := (hclass d hdG).mp hdF
  have hdiff : color e≠color d := by simpa only [hdcolor] using hecolor
  have hEq := exchanged_graph_eq_tree_exchange G color F
    (by simpa only [hdcolor] using hclass) hdiff
  have hset : {x | exchangedColor color e d x=color d}=
      {x | exchangedColor color e d x=c} := by rw [hdcolor]
  have hEqc := (congrArg G.restrict hset).symm.trans hEq
  have htree : (∀ q∈(G.restrict {x | exchangedColor color e d x=c}).edgeSet,
      (G.restrict {x | exchangedColor color e d x=c}).IsBridge q) ∧
      (G.restrict {x | exchangedColor color e d x=c}).toSimpleGraph.Connected := by
    have hp := congrArg (fun K : Graph V E =>
      (∀ q∈K.edgeSet,K.IsBridge q) ∧ K.toSimpleGraph.Connected) hEqc
    exact hp.mpr ⟨hbf,hc⟩
  have hdin0 : edgeInside G (R 0) d := by
    obtain ⟨u,v,huv⟩ := Graph.exists_isLink_of_mem_edgeSet hdG
    exact ⟨⟨u,huv.left_mem⟩,⟨v,huv.right_mem⟩,huv,by rw [hzero]; trivial⟩
  have houtN := not_inside_terminal_of_level_lt G R N (hdlt.trans_le hmN)
  have hdnext := (finite_edgeLevel_boundary G R N hdin0 houtN).2.2
  refine ⟨d,hdF,hdcolor,hde,hdlt,hdnext,htree.1,htree.2,?_⟩
  intro a b hdab
  have hdH : (G.restrict ((insert e F:Finset E):Set E)).IsLink d a.val b.val :=
    ⟨mem_insert_of_mem hdF,hdab⟩
  apply (hroute a b hdH).mono
  intro x y hxy
  obtain ⟨⟨hne,q,⟨hq,hl⟩,hqd⟩,hRxy⟩ := hxy
  have hnew : exchangedColor color e d q=c := by
    rcases mem_insert.mp hq with rfl | hqF
    · simp only [exchangedColor,ite_true,hdcolor]
    · have hqcolor := (hclass q hl.edge_mem).mp hqF
      have hqe : q≠e := fun hh => heF (hh ▸ hqF)
      have hqd' : q≠d := by simpa only [Set.mem_singleton_iff] using hqd
      simp only [exchangedColor,ite_eq_right hqe,ite_eq_right hqd',hqcolor]
  exact ⟨⟨hne,q,hnew,hl⟩,hRxy⟩
end LightEFTSpanners.MultigraphCuts
