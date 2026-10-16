import LightSpanners.Greedy
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Kruskal's forest, its bottleneck paths, and containment in the spanner.
Minimum total weight is proved in `MinimumTree`. -/
namespace LightSpanners
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V]

def EdgeConnected (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  ∀ u v, s(u,v) = e → G.Reachable u v

omit [DecidableEq V] in
theorem edgeConnected_mono {G H : SimpleGraph V} (h : G ≤ H) {e : Sym2 V}
    (he : EdgeConnected G e) : EdgeConnected H e :=
  fun u v huv => (he u v huv).mono h

omit [DecidableEq V] in
theorem covered_edgeConnected {G : SimpleGraph V} {w : Sym2 V → ℝ} {t : ℝ}
    {e : Sym2 V} (h : Covered G w t e) : EdgeConnected G e := by
  intro u v huv
  obtain ⟨p, _⟩ := h u v huv
  exact p.reachable

noncomputable def kruskalEdges : List (Sym2 V) → Finset (Sym2 V)
  | [] => ∅
  | e :: es => by
    classical
    exact let K := kruskalEdges es
      if EdgeConnected (edgeGraph K) e then K else insert e K

theorem kruskalEdges_subset (l : List (Sym2 V)) : kruskalEdges l ⊆ l.toFinset := by
  classical
  induction l with
  | nil => simp [kruskalEdges]
  | cons e es ih =>
    simp only [kruskalEdges]
    split_ifs
    · exact ih.trans (by simp)
    · exact insert_subset (by simp) (ih.trans (by simp))

theorem kruskal_edgeConnected (l : List (Sym2 V)) (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    ∀ e ∈ l, EdgeConnected (edgeGraph (kruskalEdges l)) e := by
  classical
  induction l with
  | nil => simp
  | cons e es ih =>
    have hi := ih (fun d hd => hl d (by simp [hd]))
    intro d hd
    simp only [kruskalEdges]
    split_ifs with hc
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact hc
      · exact hi d hd
    · rcases List.mem_cons.mp hd with rfl | hd
      · intro u v huv
        apply Adj.reachable
        apply (mem_edgeSet _).mp
        rw [huv]
        exact (mem_edgeGraph _ _).mpr ⟨mem_insert_self _ _, hl d (by simp)⟩
      · exact edgeConnected_mono (edgeGraph_mono (subset_insert _ _)) (hi d hd)

theorem kruskal_reachable (l : List (Sym2 V)) (hl : ∀ e ∈ l, ¬ e.IsDiag)
    {u v : V} (h : (edgeGraph l.toFinset).Reachable u v) :
    (edgeGraph (kruskalEdges l)).Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | @cons u v z huv p ih =>
    have he := (mem_edgeGraph _ _).mp ((mem_edgeSet _).mpr huv)
    exact (kruskal_edgeConnected l hl s(u,v) (List.mem_toFinset.mp he.1) u v rfl).trans ih

theorem kruskal_reachable_iff (l : List (Sym2 V)) (hl : ∀ e ∈ l, ¬ e.IsDiag)
    (u v : V) : (edgeGraph (kruskalEdges l)).Reachable u v ↔
      (edgeGraph l.toFinset).Reachable u v :=
  ⟨fun h => h.mono (edgeGraph_mono (kruskalEdges_subset l)), kruskal_reachable l hl⟩

theorem edgeGraph_insert (E : Finset (Sym2 V)) (u v : V) :
    edgeGraph (insert s(u,v) E) = edgeGraph E ⊔ SimpleGraph.edge u v := by
  rw [edgeGraph, coe_insert, Set.insert_eq, fromEdgeSet_union, sup_comm]
  rfl

theorem kruskal_acyclic (l : List (Sym2 V)) : (edgeGraph (kruskalEdges l)).IsAcyclic := by
  classical
  induction l with
  | nil => simp [kruskalEdges, edgeGraph]
  | cons e es ih =>
    simp only [kruskalEdges]
    split_ifs with hc
    · exact ih
    · induction e using Sym2.inductionOn with
      | hf u v =>
        rw [edgeGraph_insert]
        apply ih.sup_edge_of_not_reachable
        intro hreach
        apply hc
        intro a b hab
        rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hreach
        · exact hreach.symm

theorem kruskal_subset_greedy (w : Sym2 V → ℝ) (t : ℝ) (l : List (Sym2 V))
    (hl : ∀ e ∈ l, ¬ e.IsDiag) : kruskalEdges l ⊆ greedyEdges w t l := by
  classical
  induction l with
  | nil => simp [kruskalEdges, greedyEdges]
  | cons e es ih =>
    have htail : ∀ d ∈ es, ¬ d.IsDiag := fun d hd => hl d (by simp [hd])
    have hi := ih htail
    simp only [kruskalEdges, greedyEdges]
    split_ifs with hk hg hg
    · exact hi
    · exact hi.trans (subset_insert _ _)
    · exfalso
      apply hk
      intro u v huv
      exact kruskal_reachable es htail
        ((covered_edgeConnected hg u v huv).mono (edgeGraph_mono (greedyEdges_subset w t es)))
    · exact insert_subset_insert e hi

theorem kruskal_isTree (l : List (Sym2 V)) (hl : ∀ e ∈ l, ¬ e.IsDiag)
    (hconn : (edgeGraph l.toFinset).Connected) :
    (edgeGraph (kruskalEdges l)).IsTree := by
  let := hconn.nonempty
  exact ⟨⟨fun u v => kruskal_reachable l hl (hconn u v)⟩, kruskal_acyclic l⟩

theorem kruskal_bottleneck (w : Sym2 V → ℝ) (l : List (Sym2 V))
    (hl : ∀ e ∈ l, ¬ e.IsDiag)
    (hs : l.Pairwise (fun a b => w b ≤ w a)) :
    ∀ e ∈ l, ∀ u v, s(u,v) = e →
      ∃ p : (edgeGraph (kruskalEdges l)).Walk u v, p.IsPath ∧
        ∀ d ∈ p.edges, w d ≤ w e := by
  classical
  induction l with
  | nil => simp
  | cons e es ih =>
    obtain ⟨hmax, hs⟩ := List.pairwise_cons.mp hs
    have hi := ih (fun d hd => hl d (by simp [hd])) hs
    by_cases hc : EdgeConnected (edgeGraph (kruskalEdges es)) e
    · have heq : kruskalEdges (e :: es) = kruskalEdges es := by simp [kruskalEdges, hc]
      rw [heq]
      intro d hd u v huv
      rcases List.mem_cons.mp hd with rfl | hd
      · obtain ⟨p⟩ := hc u v huv
        refine ⟨p.bypass, p.bypass_isPath, fun f hf => ?_⟩
        have hmem := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet
          (p.edges_bypass_sublist_edges.subset hf))
        exact hmax f (List.mem_toFinset.mp (kruskalEdges_subset es hmem.1))
      · exact hi d hd u v huv
    · have heq : kruskalEdges (e :: es) = insert e (kruskalEdges es) := by
        simp [kruskalEdges, hc]
      rw [heq]
      intro d hd u v huv
      rcases List.mem_cons.mp hd with rfl | hd
      · have hadj : (edgeGraph (insert d (kruskalEdges es))).Adj u v := by
          apply (mem_edgeSet _).mp
          rw [huv]
          exact (mem_edgeGraph _ _).mpr ⟨mem_insert_self _ _, hl d (by simp)⟩
        refine ⟨hadj.toWalk, ?_, ?_⟩
        · exact Walk.IsPath.nil.cons (by simpa using hadj.ne)
        · intro f hf
          have : f = d := by simpa [SimpleGraph.Adj.toWalk, huv] using hf
          simp [this]
      · obtain ⟨p, hp, hweight⟩ := hi d hd u v huv
        let hsub := edgeGraph_mono (subset_insert e (kruskalEdges es))
        exact ⟨p.mapLe hsub, hp.mapLe hsub, fun f hf => hweight f (by simpa using hf)⟩

end LightSpanners
