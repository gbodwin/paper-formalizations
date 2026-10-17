import LightEFTSpanners.NativePartitionLabels
import LightEFTSpanners.NativeMinimumCycleLevel
import LightEFTSpanners.NativeTerminalDensity

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- From the source's actual colored decomposition, construct the real
least-color refinement sequence and a minimum finite-level last-color cycle
edge, with an actual same-color replacement route inside its level block.
Finite labels and all connected-fiber hypotheses are discharged internally.
The first colors being trees and the last being disconnected are precisely the
inductive countercase; no full packing or maximality conclusion is assumed. -/
theorem exists_refinement_cycle_witness (G : Graph V E) [Finite G.vertexSet]
    {k : ℕ} (color : E → Fin (k+1)) (hp : TreePartitionCriterion G (k+1))
    (ht : ∀ c : Fin k,
      (∀ e∈(G.restrict {e | color e=c.castSucc}).edgeSet,
        (G.restrict {e | color e=c.castSucc}).IsBridge e) ∧
      (G.restrict {e | color e=c.castSucc}).toSimpleGraph.Connected)
    {a b : G.vertexSet}
    (hnot : ¬(G.restrict {e | color e=Fin.last k}).toSimpleGraph.Reachable a b) :
    let H : Fin (k+1) → SimpleGraph G.vertexSet := fun c => (G.restrict {e | color e=c}).toSimpleGraph
    let R : ℕ → Setoid G.vertexSet := fun n => (refinementStep H)^[n] ⊤
    let L := G.restrict {e | color e=Fin.last k}
    ∃ N≤Nat.card G.vertexSet*Nat.card G.vertexSet,∃ e∈L.edgeSet,
      ¬L.IsBridge e ∧ edgeLevel L R N e<N ∧
      edgeInside L (R (edgeLevel L R N e)) e ∧
      ¬edgeInside L (R (edgeLevel L R N e+1)) e ∧
      (∀ d∈L.edgeSet,¬L.IsBridge d → edgeLevel L R N e≤edgeLevel L R N d) ∧
      (∀ u v : G.vertexSet,L.IsLink e u.val v.val →
        (blockGraph (L.deleteEdges {e}).toSimpleGraph (R (edgeLevel L R N e))).Reachable u v) := by
  classical
  let : Nonempty G.vertexSet := ⟨a⟩
  intro H R L
  obtain ⟨N,hN,m,f,hsurj,hker,hc⟩ := exists_native_terminal_labels G color
  obtain ⟨d,u,v,hd,hcolor,hdiff,hnb,_⟩ :=
    terminal_last_color_crossing_nonbridge G f hsurj color hp hc ht hnot
  have hdL : L.IsLink d u v := ⟨hcolor,hd⟩
  have hcross : ¬edgeInside L (R N) d := by
    intro hin
    have hr := (edgeInside_iff L (R N) (a:=⟨u,hdL.left_mem⟩) (b:=⟨v,hdL.right_mem⟩) hdL).mp hin
    have hsame : f u=f v :=
      (congrArg (fun S : Setoid G.vertexSet => S.r ⟨u,hd.left_mem⟩ ⟨v,hd.right_mem⟩) hker).mpr hr
    exact hdiff hsame
  have hanti : Antitone R := color_refinement_iterates_antitone H ⊤
  have hzero : R 0=⊤ := rfl
  obtain ⟨e,he,hne,hle,hin,hnext,hmin,hroute⟩ :=
    exists_minimum_cycle_level L R hanti hzero N ⟨d,hdL.edge_mem,hnb,hcross⟩
  exact ⟨N,hN,e,he,hne,hle,hin,hnext,hmin,hroute⟩
end LightEFTSpanners.MultigraphCuts
