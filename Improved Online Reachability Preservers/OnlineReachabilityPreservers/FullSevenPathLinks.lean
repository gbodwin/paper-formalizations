import OnlineReachabilityPreservers.ShortReturnPieceComponents
import OnlineReachabilityPreservers.FullSevenWidthCleaning
import OnlineReachabilityPreservers.TwoStepReturnMatching

/-! Path grouping through full cutoff seven tracks the parents of returns. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

variable {I J V : Type*}

section Links

variable [DecidableEq V]

/-- Protect a comparison with a direct reverse or a two-step return
on two distinct rows other than the parent. -/
def fullSevenPathLink (rows : I → List V) (i : I) (x y : V) : Prop :=
  Before rows i x y ∧
    ((∃ j, Before rows j y x) ∨ ∃ a c z, TwoStepReturnAt rows i a c y x z)

/-- Each protected comparison has a backward return within two edges
of the unlabelled precedence graph. -/
theorem fullSevenPathLink_short_return [Fintype I] [Fintype V]
    {rows : I → List V} {i : I} {x y : V} (link : fullSevenPathLink rows i x y) :
    Before rows i x y ∧ y ∈ reachIn (listPiecePrecedenceGraph rows) x 2 := by
  let G := listPiecePrecedenceGraph rows
  refine ⟨link.1, ?_⟩
  rcases link.2 with ⟨r, reverse⟩ | ⟨a, c, z, path⟩
  · have edge : Edge G y x := listPiecePrecedenceGraph_edge.mpr ⟨r, reverse⟩
    exact reachIn_succ.mpr (Or.inr ⟨x, edge, target_mem_reachIn G x 1⟩)
  · have firstEdge : Edge G y z := listPiecePrecedenceGraph_edge.mpr ⟨a, path.into_return⟩
    have lastEdge : Edge G z x := listPiecePrecedenceGraph_edge.mpr ⟨c, path.cross.step⟩
    have one : z ∈ reachIn G x 1 :=
      reachIn_succ.mpr (Or.inr ⟨x, lastEdge, target_mem_reachIn G x 0⟩)
    exact reachIn_succ.mpr (Or.inr ⟨z, firstEdge, one⟩)

/-- Keeping the protected comparison endpoints together preserves
full exclusion through seven on disjoint order-preserving pieces. -/
theorem fullBridgeFree_of_full_seven_path_links [LinearOrder I]
    {rows : I → List V} {pieces : J → List V} {cutoff : ℕ} (parent : J → I)
    (free : BridgeFree (Before rows) cutoff) (short : cutoff ≤ 7)
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (together : ∀ {i j x y}, parent i = parent j → x ∈ pieces i → y ∈ pieces j →
      fullSevenPathLink rows (parent i) x y → i = j) :
    BridgeFree (Before pieces) cutoff := by
  refine fullBridgeFree_of_opposite_and_two_step_safe_split parent (fun {_ _ _} => steps)
    (fun {_ _ _} => disjoint) ?_ ?_ free short
  · intro i j q x y same _ before reverse onX onY
    exact together same onX onY ⟨before, Or.inl ⟨parent q, steps reverse⟩⟩
  · intro i j a c x y z apart same aOther cOther more onX onY old first last
    have route : TwoStepReturnAt rows (parent i) (parent a) (parent c) x y z :=
      ⟨⟨more, aOther.symm, cOther, (steps first).2.1, old.1, steps last⟩, steps first, old⟩
    have link : fullSevenPathLink rows (parent i) y x :=
      ⟨old, Or.inr ⟨parent a, parent c, z, route⟩⟩
    exact apart.symm (together same.symm onY onX (same ▸ link))

end Links

section Components

variable [LinearOrder V] [Fintype V]

/-- Symmetrize the protected comparison pairs on one parent row. -/
noncomputable def fullSevenPathLinkGraph (rows : I → List V) (i : I) : Arcs V := by
  classical
  exact univ.filter fun e => fullSevenPathLink rows i e.1 e.2 ∨ fullSevenPathLink rows i e.2 e.1

theorem fullSevenPathLinkGraph_edge {rows : I → List V} {i : I} {x y : V} :
    Edge (fullSevenPathLinkGraph rows i) x y ↔
      fullSevenPathLink rows i x y ∨ fullSevenPathLink rows i y x := by
  classical
  simp only [Edge, fullSevenPathLinkGraph, mem_filter, mem_univ, true_and]

/-- The connected protected group of one vertex within a parent row. -/
noncomputable def fullSevenPathLinkComponent (rows : I → List V) (i : I) (x : V) : Finset V :=
  linkedGroupComponent (rows i).toFinset (fullSevenPathLinkGraph rows i) x

/-- Every row has a width-bounded partition keeping its protected
comparisons together. -/
def HasCappedFullSevenPathPartition (rows : I → List V) (width : ℕ) : Prop :=
  ∀ i, ∃ groups, CappedPathPartition (rows i).toFinset (fullSevenPathLink rows i) width groups

/-- The protected groups fit exactly when such a partition exists. -/
theorem hasCappedFullSevenPathPartition_iff_component_room (rows : I → List V) (width : ℕ) :
    HasCappedFullSevenPathPartition rows width ↔
    ∀ i, ∀ x ∈ rows i, (fullSevenPathLinkComponent rows i x).card ≤ width := by
  have check (i : I) := cappedPathPartition_iff_component_room (rows i).toFinset
    (fullSevenPathLink rows i) (fullSevenPathLinkGraph rows i) width
    (fun {_ _} => fullSevenPathLinkGraph_edge)
    (fun {_ _} h => ⟨List.mem_toFinset.mpr h.1.1, List.mem_toFinset.mpr h.1.2.1⟩)
  constructor
  · intro byRow i x on
    exact (check i).mp (byRow i) x (List.mem_toFinset.mpr on)
  · intro room i
    exact (check i).mpr (fun x on => room i x (List.mem_toFinset.mp on))

variable [Fintype I]

/-- Keeping the row labels in the return test can only shrink the path
components compared with taking all returns of at most two steps. -/
theorem fullSevenPathLinkComponent_subset_radius_two (rows : I → List V) (i : I) (x : V) :
    fullSevenPathLinkComponent rows i x ⊆ shortReturnRowComponent rows 5 i x := by
  have edges : fullSevenPathLinkGraph rows i ⊆ shortReturnRowGraph rows 5 i := by
    intro e on
    rcases fullSevenPathLinkGraph_edge.mp on with one | other
    · exact shortReturnRowGraph_edge.mpr (Or.inl (fullSevenPathLink_short_return one))
    · exact shortReturnRowGraph_edge.mpr (Or.inr (fullSevenPathLink_short_return other))
  intro y on
  obtain ⟨inRow, same⟩ := mem_filter.mp on
  have paths := componentLabel_eq.mp same
  exact mem_filter.mpr ⟨inRow, componentLabel_eq.mpr
    ⟨reach_mono edges paths.1, reach_mono edges paths.2⟩⟩

end Components

end OnlineReachabilityPreservers
