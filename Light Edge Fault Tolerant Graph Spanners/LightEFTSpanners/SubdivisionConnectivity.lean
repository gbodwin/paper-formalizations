import LightEFTSpanners.SubdivisionFaultProjection

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset
variable {V I : Type*} [Fintype V] [Fintype I] (C : SimpleGraph V)
attribute [local instance] Classical.propDecidable

/-- An actual disjoint color class receives fewer than k faults whenever the
total fault count is smaller than k times the number of colors. -/
theorem exists_color_below_budget (F : Finset (Sym2 (Vertex (I:=I) C))) (k : ℕ)
    (hF : F.card<k*Fintype.card I) :
    ∃ j : I,(F ∩ (colorGraph C j).edgeFinset).card<k := by
  classical
  by_contra! hh
  have hpair : (Set.univ : Set I).PairwiseDisjoint
      (fun j => F ∩ (colorGraph C j).edgeFinset) := by
    intro i hi j hj hij
    exact ((color_edgeFinsets_pairwise (I:=I) C) hi hj hij).mono
      inter_subset_right inter_subset_right
  have hsub : univ.biUnion (fun j => F ∩ (colorGraph C j).edgeFinset) ⊆ F := by
    intro e he
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp he
    exact (mem_inter.mp hj).1
  have hc := card_le_card hsub
  rw [card_biUnion (by simpa using hpair)] at hc
  have hlo : k*Fintype.card I ≤ ∑ j:I,(F ∩ (colorGraph C j).edgeFinset).card := by
    calc
      _ = ∑ _j:I,k := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun j _ => hh j)
  omega

/-- r parallel subdivisions multiply actual core edge-connectivity by r.
This is an explicit simple-graph realization of edge doubling, including all
finite fault sets and without an assumed path-packing or max-flow theorem. -/
theorem core_edge_connectivity {u v : V} {k : ℕ} (h : C.IsEdgeReachable k u v) :
    (graph (I:=I) C).IsEdgeReachable (k*Fintype.card I) (Sum.inl u) (Sum.inl v) := by
  classical
  intro s hs
  have hcard : s.toFinset.card<k*Fintype.card I := by
    rw [Set.encard_eq_coe_toFinset_card] at hs
    exact_mod_cast hs
  obtain ⟨j,hj⟩ := exists_color_below_budget C s.toFinset k hcard
  have hd : (badBaseEdges C s.toFinset j).card<k :=
    (badBaseEdges_card_le C s.toFinset j).trans_lt hj
  have hr : (afterFaults C (badBaseEdges C s.toFinset j)).Reachable u v := by
    apply h
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hd
  simpa only [afterFaults,Set.coe_toFinset] using projected_faults_lift C s.toFinset j hr
end LightEFTSpanners.ParallelSubdivision
