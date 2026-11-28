import OnlineReachabilityPreservers.HalfFourAdjacentObstructions

/-! The literal row-count upper bound from half cutoff four. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private theorem arcsLinkingVertexToPair_union {V : Type*} [DecidableEq V]
    (arcs : Finset (V × V)) (x y z t : V) :
    arcsLinkingVertexToPair arcs x y z ∪ arcsLinkingVertexToPair arcs x y t =
      arcsBetweenPairs arcs x y z t := by
  ext e
  rcases e with ⟨u,v⟩
  simp only [mem_arcsBetweenPairs,arcsLinkingVertexToPair,mem_union,mem_filter,mem_insert,
    mem_singleton,Prod.mk.injEq]
  tauto

private theorem expanded_erase_pair_budget {n r : ℕ} (count : r+2 = n) :
    n*(n-1) = r*(r-1)+4*r+2 := by
  rw [← count]
  cases r with
  | zero => decide
  | succ a =>
    rw [show a+1+2-1 = a+2 by omega,show a+1-1 = a by omega]
    ring

/-- If every reciprocal pair has disjoint out-neighborhoods, and two
disjoint reciprocal pairs have at most three arcs between them, the
directed edge count exceeds the number of unordered pairs by at most one. -/
theorem directed_arcs_card_le_choose_add_one_of_reciprocal_pairs {V : Type*} [Fintype V] [DecidableEq V]
    (arcs : Finset (V × V)) (loopless : ∀ v, (v,v) ∉ arcs)
    (apart : ∀ {x y z : V}, (x,y) ∈ arcs → (y,x) ∈ arcs → (x,z) ∈ arcs → (y,z) ∉ arcs)
    (cross : ∀ {x y z t : V}, Function.Injective (![x,y,z,t] : Fin 4 → V) →
      (x,y) ∈ arcs → (y,x) ∈ arcs → (z,t) ∈ arcs → (t,z) ∈ arcs →
      (arcsBetweenPairs arcs x y z t).card ≤ 3) :
    arcs.card ≤ (Fintype.card V).choose 2+1 := by
  have bound (s : Finset V) : 2*(arcsOnVertices arcs s).card ≤ s.card*(s.card-1)+2 := by
    refine Finset.strongInductionOn (p := fun s => 2*(arcsOnVertices arcs s).card ≤ s.card*(s.card-1)+2) s ?_
    intro s smaller
    by_cases doubled : ∃ x y, (x,y) ∈ arcsOnVertices arcs s ∧ (y,x) ∈ arcsOnVertices arcs s
    · obtain ⟨x,y,xy,yx⟩ := doubled
      obtain ⟨xOn,yOn,xyArc⟩ := mem_arcsOnVertices.mp xy
      have yxArc := (mem_arcsOnVertices.mp yx).2.2
      have xyNe : x ≠ y := by rintro rfl; exact loopless _ xyArc
      let r := (s.erase x).erase y
      have count : r.card+2 = s.card := erase_pair_card_add_two xOn yOn xyNe
      have sub : r ⊂ s := Finset.ssubset_iff_subset_ne.mpr
        ⟨(erase_subset _ _).trans (erase_subset _ _),fun eq => by rw [eq] at count; omega⟩
      let links := arcsLinkingVertexToPair arcs x y
      have each (u : V) : (links u).card ≤ 2 :=
        at_most_two_links_to_bidirectional_pair @apart xyArc yxArc u
      have removed := arcsOnVertices_card_le_erase_pair arcs loopless s x y
      change (arcsOnVertices arcs s).card ≤ (arcsOnVertices arcs r).card+2+(r.biUnion links).card at removed
      rw [expanded_erase_pair_budget count]
      by_cases remains : ∃ u v, (u,v) ∈ arcsOnVertices arcs r ∧ (v,u) ∈ arcsOnVertices arcs r
      · obtain ⟨u,v,uv,vu⟩ := remains
        obtain ⟨uOn,vOn,uvArc⟩ := mem_arcsOnVertices.mp uv
        have vuArc := (mem_arcsOnVertices.mp vu).2.2
        have uvNe : u ≠ v := by rintro rfl; exact loopless _ uvArc
        have yu : y ≠ u := (mem_erase.mp uOn).1.symm
        have yv : y ≠ v := (mem_erase.mp vOn).1.symm
        have xu : x ≠ u := (mem_erase.mp (mem_erase.mp uOn).2).1.symm
        have xv : x ≠ v := (mem_erase.mp (mem_erase.mp vOn).2).1.symm
        have distinct : Function.Injective (![x,y,u,v] : Fin 4 → V) := by
          intro a b eq
          fin_cases a <;> fin_cases b <;> simp_all
        let remainder := (r.erase u).erase v
        have left : remainder.card+2 = r.card := erase_pair_card_add_two uOn vOn uvNe
        have cover : r.biUnion links ⊆ remainder.biUnion links ∪ (links u ∪ links v) := by
          intro edge on
          obtain ⟨w,wOn,present⟩ := mem_biUnion.mp on
          by_cases wu : w = u
          · subst w
            exact mem_union_right _ (mem_union_left _ present)
          by_cases wv : w = v
          · subst w
            exact mem_union_right _ (mem_union_right _ present)
          exact mem_union_left _ (mem_biUnion.mpr ⟨w,mem_erase.mpr ⟨wv,mem_erase.mpr ⟨wu,wOn⟩⟩,present⟩)
        have small : (remainder.biUnion links).card ≤ remainder.card*2 :=
          card_biUnion_le_card_mul remainder links 2 (fun w _ => each w)
        have across : (links u ∪ links v).card ≤ 3 := by
          change (arcsLinkingVertexToPair arcs x y u ∪ arcsLinkingVertexToPair arcs x y v).card ≤ 3
          rw [arcsLinkingVertexToPair_union]
          exact cross distinct xyArc yxArc uvArc vuArc
        have savings := (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add small across))
        have prior := smaller r sub
        omega
      · have exactLinks := card_biUnion_le_card_mul r links 2 (fun w _ => each w)
        have prior := arcsOnVertices_card_le_of_no_reciprocal arcs loopless r remains
        omega
    · exact (arcsOnVertices_card_le_of_no_reciprocal arcs loopless s doubled).trans (by omega)
  have twice := bound (univ : Finset V)
  rw [arcsOnVertices_univ,card_univ] at twice
  rw [Nat.choose_two_right]
  omega

/-- At half cutoff four or above, the adjacent steps number at most
one more than the unordered vertex pairs. -/
theorem halfFour_row_gaps_le_choose_add_one {I V : Type*}
    [LinearOrder I] [Fintype I] [Fintype V] [DecidableEq V]
    {rows : I → List V} {k : ℕ} (simple : ∀ i, (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) k) (four : 4 ≤ k) :
    (∑ i, ((rows i).length-1)) ≤ (Fintype.card V).choose 2+1 := by
  rw [← familyAdjacentComparisons_card simple free (by omega)]
  apply directed_arcs_card_le_choose_add_one_of_reciprocal_pairs (univ.biUnion (rowAdjacentComparisons rows))
  · intro v loop
    obtain ⟨_,on⟩ := mem_familyAdjacentComparisons.mp loop
    exact listBefore_ne (mem_rowAdjacentComparisons.mp on).1 rfl
  · intro x y z
    exact halfThree_adjacent_no_common_out free (by omega)
  · intro x y z t
    exact halfFour_adjacent_arcsBetweenPairs_le_three free four

/-- The indexed mass exceeds its nonempty row count by at most one
more than the number of unordered pairs of vertices. -/
theorem halfFour_mass_le_paths_add_choose_add_one {n p k : ℕ} {rows : Fin p → List (Fin n)}
    (valid : ∀ i, rows i ≠ [] ∧ (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) k) (four : 4 ≤ k) :
    (∑ i, (rows i).length) ≤ p+n.choose 2+1 := by
  have gaps := halfFour_row_gaps_le_choose_add_one (fun i => (valid i).2) free four
  have mass := rowMass_eq_gaps_add_count (fun i => (valid i).1)
  rw [Fintype.card_fin] at gaps mass
  omega

/-- The half-four bound for a literal nonempty distinct family adds
at most one singleton per original vertex to the consecutive-step count. -/
theorem literal_half_four_path_count_le_choose_add_one {n p k : ℕ} {rows : Fin p → List (Fin n)}
    (distinct : Function.Injective rows) (valid : ∀ i, rows i ≠ [] ∧ (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) k) (four : 4 ≤ k) :
    p ≤ n+n.choose 2+1 := by
  have gaps := halfFour_row_gaps_le_choose_add_one (fun i => (valid i).2) free four
  rw [Fintype.card_fin] at gaps
  have count := literal_path_count_le_vertices_add_gaps distinct (fun i => (valid i).1)
  omega

end OnlineReachabilityPreservers
