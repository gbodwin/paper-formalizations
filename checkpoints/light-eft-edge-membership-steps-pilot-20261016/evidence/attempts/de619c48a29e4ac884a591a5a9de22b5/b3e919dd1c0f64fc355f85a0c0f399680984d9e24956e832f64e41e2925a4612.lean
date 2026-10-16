import LightEFTSpanners.NativeImprovingExchange
import LightEFTSpanners.NativeRefinementCycleWitness
import LightEFTSpanners.NativeSplitColor

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- The source's disconnected-last-color countercase produces an actual
admissible coloring with strictly larger finite signature. The common horizon
is the proved quadratic actual-vertex bound, not a supplied stabilization time. -/
theorem exists_improving_native_countercase (G : Graph V E) [Fintype G.vertexSet]
    {k : ℕ} (color : E → Fin (k+1)) (hp : TreePartitionCriterion G (k+1))
    (ht : earlierColorTrees G color) {a b : G.vertexSet}
    (hnot : ¬(G.restrict {e | color e=Fin.last k}).toSimpleGraph.Reachable a b) :
    ∃ other : E → Fin (k+1),earlierColorTrees G other ∧
      nativeRefinementSignature G (Nat.card G.vertexSet*Nat.card G.vertexSet) color <
        nativeRefinementSignature G (Nat.card G.vertexSet*Nat.card G.vertexSet) other := by
  classical
  let R := nativePartitionAt G color
  let L := G.restrict {e | color e=Fin.last k}
  obtain ⟨N,hN,e,heL,hnb,hm,hin,hext,hmin,hroute⟩ :=
    exists_refinement_cycle_witness G color hp ht hnot
  have he : color e=Fin.last k := heL.2
  let m := edgeLevel L R N e
  have hinG : edgeInside G (R m) e := (edgeInside_restrict_iff G _ _ he).mp hin
  have hextG : ¬edgeInside G (R (m+1)) e := by
    intro hi
    exact hext ((edgeInside_restrict_iff G _ _ he).mpr hi)
  have hextstep : ¬edgeInside G
      (refinementStep (fun c => (G.restrict {x | color x=c}).toSimpleGraph) (R m)) e := by
    simpa only [R,nativePartitionAt_succ] using hextG
  obtain ⟨hsplit,c,hc,hstep,hout⟩ := exists_earlier_splitting_color G color (R m) he hinG hextstep
  have hpriority : nativePriorityAt G color m=c.castSucc.val := by
    change refinementPriority (fun c => (G.restrict {x | color x=c}).toSimpleGraph) (R m)=c.castSucc.val
    unfold refinementPriority
    rw [dite_eq_left hsplit,←hc]
  have eroute : ∀ u v : G.vertexSet,G.IsLink e u.val v.val →
      (blockGraph (L.deleteEdges {e}).toSimpleGraph (R m)).Reachable u v := by
    intro u v hl
    exact hroute u v ⟨he,hl⟩
  obtain ⟨d,hdG,htnew,hlt⟩ := exists_improving_native_exchange G color ht c he m
    (hm.trans_le hN) hinG hextG hpriority hout eroute
  exact ⟨exchangedColor color e d,htnew,hlt⟩

/-- In the genuinely maximized decomposition every pair is connected in the
last color. The contradiction is derived from constructed edges and routes. -/
theorem maximal_native_last_reachable (G : Graph V E) [Fintype G.vertexSet]
    {k : ℕ} (color : E → Fin (k+1)) (hp : TreePartitionCriterion G (k+1))
    (ht : earlierColorTrees G color)
    (hmax : ∀ other : E → Fin (k+1),earlierColorTrees G other →
      nativeRefinementSignature G (Nat.card G.vertexSet*Nat.card G.vertexSet) other ≤
        nativeRefinementSignature G (Nat.card G.vertexSet*Nat.card G.vertexSet) color)
    (a b : G.vertexSet) :
    (G.restrict {e | color e=Fin.last k}).toSimpleGraph.Reachable a b := by
  by_contra hnot
  obtain ⟨other,htother,hlt⟩ := exists_improving_native_countercase G color hp ht hnot
  exact (not_lt_of_ge (hmax other htother)) hlt
end LightEFTSpanners.MultigraphCuts
