import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sublists
import OnlineReachabilityPreservers.SteinerHubs

/-! Local directed cuts and capacities for thin demands. -/

namespace OnlineReachabilityPreservers

open Finset Relation

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Edges with both endpoints in the reachability interval of the demand. -/
def intervalArcs (G : Arcs V) (d : V × V) : Arcs V :=
  G.filter fun e => e.1 ∈ reachInterval G d ∧ e.2 ∈ reachInterval G d

theorem intervalArcs_subset (G : Arcs V) (d : V × V) : intervalArcs G d ⊆ G :=
  filter_subset _ _

/-- A feasible path in any input subgraph stays within the demand's reachability interval. -/
theorem reach_intervalArcs {G H : Arcs V} (sub : H ⊆ G) {d : V × V}
    (h : Reach H d.1 d.2) : Reach (H ∩ intervalArcs G d) d.1 d.2 := by
  have aux {v : V} (first : Reach H d.1 v) (last : Reach H v d.2) :
      Reach (H ∩ intervalArcs G d) d.1 v := by
    induction first with
    | refl => exact .refl
    | @tail u v first edge ih =>
      have fromU := last.head edge
      have hu := mem_reachInterval.mpr ⟨reach_mono sub first,reach_mono sub fromU⟩
      have hv := mem_reachInterval.mpr ⟨reach_mono sub (first.tail edge),reach_mono sub last⟩
      exact (ih fromU).tail (mem_inter.mpr ⟨edge,mem_filter.mpr ⟨sub edge,hu,hv⟩⟩)
  exact aux h .refl

/-- The arcs leaving a source side. -/
def outgoingCut (G : Arcs V) (W : Finset V) : Arcs V :=
  G.filter fun e => e.1 ∈ W ∧ e.2 ∉ W

omit [Fintype V] in
theorem outgoingCut_subset (G : Arcs V) (W : Finset V) : outgoingCut G W ⊆ G :=
  filter_subset _ _

omit [Fintype V] in
theorem cut_crossing {G : Arcs V} {s t : V} (walk : Reach G s t)
    {W : Finset V} (hs : s ∈ W) (ht : t ∉ W) : (outgoingCut G W).Nonempty := by
  induction walk with
  | refl => exact (ht hs).elim
  | @tail u v _ edge ih =>
    by_cases hu : u ∈ W
    · exact ⟨(u,v),mem_filter.mpr ⟨edge,hu,ht⟩⟩
    · exact ih hu

theorem intervalCut_hits_solution {G Z : Arcs V} (sub : Z ⊆ G) {d : V × V}
    (walk : Reach Z d.1 d.2) {W : Finset V} (hs : d.1 ∈ W) (ht : d.2 ∉ W) :
    (Z ∩ outgoingCut (intervalArcs G d) W).Nonempty := by
  obtain ⟨e,he⟩ := cut_crossing (reach_intervalArcs sub walk) hs ht
  obtain ⟨hh,hW⟩ := mem_filter.mp he
  obtain ⟨hZ,hI⟩ := mem_inter.mp hh
  exact ⟨e,mem_inter.mpr ⟨hZ,mem_filter.mpr ⟨hI,hW⟩⟩⟩

/-- Every source side in the reachable interval, enumerated in a fixed order. -/
def intervalCutSides (G : Arcs V) (d : V × V) : List (Finset V) :=
  (((reachInterval G d).sort (· ≤ ·)).sublists.map List.toFinset).filter
    (fun W => decide (d.1 ∈ W ∧ d.2 ∉ W))

theorem mem_intervalCutSides {G : Arcs V} {d : V × V} {W : Finset V} :
    W ∈ intervalCutSides G d ↔ W ⊆ reachInterval G d ∧ d.1 ∈ W ∧ d.2 ∉ W := by
  let U := reachInterval G d
  simp only [intervalCutSides,List.mem_filter,decide_eq_true_eq,List.mem_map,List.mem_sublists]
  constructor
  · rintro ⟨⟨l,hl,rfl⟩,hW⟩
    refine ⟨fun x hx => (mem_sort (r := (· ≤ ·))).mp (hl.subset (List.mem_toFinset.mp hx)),hW⟩
  · rintro ⟨hW,hs,ht⟩
    refine ⟨⟨W.sort (· ≤ ·),?_,sort_toFinset _ _⟩,hs,ht⟩
    apply List.sublist_of_subperm_of_sortedLE
    · apply List.subperm_of_subset (sort_nodup _ _)
      intro x hx
      simpa only [mem_sort] using hW ((mem_sort (r := (· ≤ ·))).mp hx)
    · exact (pairwise_sort _ _).sortedLE
    · exact (pairwise_sort _ _).sortedLE

/-- Edge loads are exponents. An edge of load x has capacity 2^x / |E(G)|. -/
abbrev CutLoads (V : Type*) := (V × V) → ℕ

def cutMass (E : Arcs V) (load : CutLoads V) : ℕ := ∑ e ∈ E, 2^(load e)

def loadTotal (E : Arcs V) (load : CutLoads V) : ℕ := ∑ e ∈ E, load e

/-- Find the first source side whose integer capacity is below |E(G)|. -/
def thinViolation (G : Arcs V) (d : V × V) (load : CutLoads V) : Option (Finset V) :=
  (intervalCutSides G d).find? fun W =>
    decide (cutMass (outgoingCut (intervalArcs G d) W) load < G.card)

def CutCovered (G : Arcs V) (d : V × V) (load : CutLoads V) : Prop :=
  ∀ W ⊆ reachInterval G d, d.1 ∈ W → d.2 ∉ W →
    G.card ≤ cutMass (outgoingCut (intervalArcs G d) W) load

theorem thinViolation_eq_none {G : Arcs V} {d : V × V} {load : CutLoads V} :
    thinViolation G d load = none ↔ CutCovered G d load := by
  simp only [thinViolation,List.find?_eq_none,decide_eq_true_eq,not_lt,CutCovered,mem_intervalCutSides]
  exact ⟨fun h W hs s t => h W ⟨hs,s,t⟩,fun h W ⟨hs,s,t⟩ => h W hs s t⟩

end OnlineReachabilityPreservers
