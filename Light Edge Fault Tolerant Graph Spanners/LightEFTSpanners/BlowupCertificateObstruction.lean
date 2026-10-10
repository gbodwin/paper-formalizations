import LightEFTSpanners.Basic
import LightSpanners.TreeReduction
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Tactic

/-! A six-vertex obstruction to the *denominator certificate used in the proof*
of Theorem34. This does not assert that the main lower-bound theorem is false. -/
namespace LightEFTSpanners.BlowupCertificateObstruction
open SimpleGraph LightSpanners Finset

abbrev Base := Fin 3
abbrev Cloud := Fin 2
abbrev Vertex := Base × Cloud

def blowup (J : SimpleGraph Base) : SimpleGraph Vertex where
  Adj u v := J.Adj u.1 v.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u => J.loopless.irrefl u.1⟩

abbrev baseGraph : SimpleGraph Base := ⊤
abbrev baseTree : SimpleGraph Base := starGraph 1
abbrev G : SimpleGraph Vertex := blowup baseGraph
abbrev Q : SimpleGraph Vertex := blowup baseTree
abbrev u : Vertex := (0,0)
abbrev v : Vertex := (2,0)
def faults : Finset (Sym2 Vertex) := {s(u,(1,0)),s(u,(1,1))}

theorem baseTree_mst : IsMinimumSpanningTree baseGraph baseTree (fun _ => 1) := by
  apply minimumSpanningTree_of_bottleneck (isTree_starGraph 1) le_top
  intro x y _
  obtain ⟨p⟩ := (isTree_starGraph (1:Base)).connected x y
  exact ⟨p,by intros; rfl⟩

theorem base_weighted_girth : WeightedGirthAbove baseGraph (fun _ => 1) 2 := by
  intro a p hp e he
  have hlen := hp.three_le_length
  have hw : walkWeight (fun _ => (1:ℝ)) p = p.length := by simp [walkWeight]
  rw [hw]
  norm_num
  exact_mod_cast hlen

theorem vertex_count : Fintype.card Vertex=6 := by decide

theorem faults_card : faults.card=2 := by decide

theorem faults_are_input_edges : ∀ e∈faults,e∈G.edgeSet := by
  intro e he
  simp only [faults,mem_insert,mem_singleton] at he
  rcases he with rfl | rfl <;> simp [G,blowup,baseGraph,u]

theorem certificate_subgraph : Q ≤ G := by
  intro x y h
  exact (show baseTree ≤ baseGraph from le_top) h

theorem source_edge_survives : (afterFaults G faults).Adj u v := by
  simp [afterFaults,deleteEdges_adj,G,blowup,baseGraph,u,v,faults,Sym2.eq_iff]

theorem certificate_isolated : (afterFaults Q faults).IsIsolated u := by
  intro z
  rcases z with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    simp [afterFaults,deleteEdges_adj,Q,blowup,baseTree,starGraph_adj,u,faults,Sym2.eq_iff]

theorem certificate_not_reachable : ¬ (afterFaults Q faults).Reachable u v := by
  rintro ⟨p⟩
  have hn := p.nil_of_isIsolated_of_mem_support certificate_isolated p.start_mem_support
  have he := hn.eq
  norm_num [u,v] at he

/-- c=2, f=1 gives q=cf=2 and p=ceil(sqrt(q+1))=2.
The complete bipartite blowup of the actual base MST fails q-fault preservation. -/
theorem mst_blowup_not_two_fault_preserver :
    ¬ IsFTConnectivityPreserver G Q 2 := by
  intro h
  exact certificate_not_reachable
    ((h.2 faults (by rw [faults_card]) u v).mp source_edge_survives.reachable)
end LightEFTSpanners.BlowupCertificateObstruction
