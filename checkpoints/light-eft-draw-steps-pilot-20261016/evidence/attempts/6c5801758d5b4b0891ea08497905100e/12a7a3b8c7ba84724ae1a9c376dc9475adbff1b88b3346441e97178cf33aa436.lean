import LightEFTSpanners.NativeExchangeImprovement
import LightEFTSpanners.NativeColoredExchange

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- The finite color class consists of actual original identities only. -/
noncomputable def actualColorClass (G : Graph V E) {C : Type*} (color : E → C) (c : C) : Finset E :=
  univ.filter (fun e => e∈G.edgeSet ∧ color e=c)

theorem mem_actualColorClass (G : Graph V E) {C : Type*} (color : E → C) (c : C) (e : E) :
    e ∈ actualColorClass G color c ↔ e∈G.edgeSet ∧ color e=c := by
  classical
  simp [actualColorClass]

theorem actualColorClass_graph (G : Graph V E) {C : Type*} (color : E → C) (c : C) :
    G.restrict (actualColorClass G color c : Set E)=G.restrict {e | color e=c} := by
  have hcomp : Graph.Compatible (G.restrict (actualColorClass G color c : Set E))
      (G.restrict {e | color e=c}) := Graph.Compatible.of_le_le Graph.restrict_le Graph.restrict_le
  refine Graph.Compatible.ext rfl ?_ hcomp
  ext e
  simp [actualColorClass]

theorem actualColorClass_simpleGraph (G : Graph V E) {C : Type*} (color : E → C) (c : C) :
    (G.restrict (actualColorClass G color c : Set E)).toSimpleGraph =
      (G.restrict {e | color e=c}).toSimpleGraph := by
  ext a b
  constructor
  · rintro ⟨hne,e,he,hl⟩
    exact ⟨hne,e,((mem_actualColorClass G color c e).mp he).2,hl⟩
  · rintro ⟨hne,e,he,hl⟩
    exact ⟨hne,e,(mem_actualColorClass G color c e).mpr ⟨hl.edge_mem,he⟩,hl⟩

/-- Construct the actual lower-level exchange and use its real replacement
routes to improve the recomputed signature, while retaining every earlier
native spanning tree. The inputs are local source-countercase facts. -/
theorem exists_improving_native_exchange (G : Graph V E) [Fintype G.vertexSet]
    {k B : ℕ} (color : E → Fin (k+1)) (ht : earlierColorTrees G color)
    (c : Fin k) {e : E} (he : color e=Fin.last k) (m : ℕ) (hm : m < B)
    (hin : edgeInside G (nativePartitionAt G color m) e)
    (hext : ¬edgeInside G (nativePartitionAt G color (m+1)) e)
    (hpriority : nativePriorityAt G color m=c.castSucc.val)
    (hout : ¬edgeInside G (componentRefinement (G.restrict {x | color x=c.castSucc}).toSimpleGraph
      (nativePartitionAt G color m)) e)
    (eroute : ∀ a b : G.vertexSet,G.IsLink e a.val b.val →
      (blockGraph ((G.restrict {x | color x=Fin.last k}).deleteEdges {e}).toSimpleGraph
        (nativePartitionAt G color m)).Reachable a b) :
    ∃ d∈G.edgeSet,earlierColorTrees G (exchangedColor color e d) ∧
      nativeRefinementSignature G B color < nativeRefinementSignature G B (exchangedColor color e d) := by
  classical
  let F := actualColorClass G color c.castSucc
  have hF : (F:Set E)⊆G.edgeSet := by
    intro x hx
    exact ((mem_actualColorClass G color c.castSucc x).mp hx).1
  have hclass : ∀ x∈G.edgeSet,x∈F ↔ color x=c.castSucc := by
    intro x hx
    rw [mem_actualColorClass]
    exact and_iff_right hx
  have htree : (∀ q∈(G.restrict (F:Set E)).edgeSet,(G.restrict (F:Set E)).IsBridge q) ∧
      (G.restrict (F:Set E)).toSimpleGraph.Connected := by
    have hh := congrArg (fun K : Graph V E => (∀ q∈K.edgeSet,K.IsBridge q) ∧ K.toSimpleGraph.Connected)
      (actualColorClass_graph G color c.castSucc)
    exact hh.mpr (ht c)
  have hcolor : color e≠c.castSucc := by
    rw [he]
    intro hh
    have hv := congrArg Fin.val hh
    have hc := c.isLt
    simp only [Fin.val_last,Fin.val_castSucc] at hv
    omega
  have heG : e∈G.edgeSet := by obtain ⟨a,b,hl,_⟩ := hin; exact hl.edge_mem
  have hanti : Antitone (nativePartitionAt G color) := color_refinement_iterates_antitone _ ⊤
  have hn : ∀ a b : G.vertexSet,G.IsLink e a.val b.val →
      ¬(blockGraph (G.restrict (F:Set E)).toSimpleGraph (nativePartitionAt G color m)).Reachable a b := by
    intro a b hl hr
    apply hout
    refine ⟨a,b,hl,?_⟩
    change (blockGraph (G.restrict (actualColorClass G color c.castSucc : Set E)).toSimpleGraph
      (nativePartitionAt G color m)).Reachable a b at hr
    rw [actualColorClass_simpleGraph] at hr
    exact hr
  obtain ⟨d,hdF,hdcolor,hde,hdlevel,hdxt,hbf,hconn,hdr⟩ :=
    exists_actual_colored_tree_exchange G color F hF c.castSucc hclass heG hcolor htree.1 htree.2
      (nativePartitionAt G color) hanti rfl m m le_rfl hin hn
  have hdiff : color e≠color d := by simpa only [hdcolor] using hcolor
  have er : ∀ a b : G.vertexSet,G.IsLink e a.val b.val →
      (blockGraph (G.restrict {x | exchangedColor color e d x=color e}).toSimpleGraph
        (nativePartitionAt G color m)).Reachable a b := by
    intro a b hl
    apply (eroute a b hl).mono
    intro x y hxy
    obtain ⟨⟨hne,q,⟨hqc,hql⟩,hqe⟩,hR⟩ := hxy
    have hqd : q≠d := by intro hh; subst q; exact hcolor (he.trans (hqc.symm.trans hdcolor))
    have hqe' : q≠e := by simpa only [Set.mem_singleton_iff] using hqe
    have hnew : exchangedColor color e d q=color e := by
      simp only [exchangedColor,ite_eq_right hqe',ite_eq_right hqd,he]
      exact hqc
    exact ⟨⟨hne,q,hnew,hql⟩,hR⟩
  have dr : ∀ a b : G.vertexSet,G.IsLink d a.val b.val →
      (blockGraph (G.restrict {x | exchangedColor color e d x=color d}).toSimpleGraph
        (nativePartitionAt G color (edgeLevel G (nativePartitionAt G color) m d))).Reachable a b := by
    rw [hdcolor]
    exact hdr
  refine ⟨d,hF hdF,exchanged_earlier_trees G color c he hdcolor ⟨hbf,hconn⟩ ht,?_⟩
  apply exchangedColor_strict_signature G color hdiff m
    (edgeLevel G (nativePartitionAt G color) m d) hm hext hdxt er dr
  · simpa only [hdcolor] using hpriority
  · exact hin
  · rw [hdcolor]
    exact hout
end LightEFTSpanners.MultigraphCuts
