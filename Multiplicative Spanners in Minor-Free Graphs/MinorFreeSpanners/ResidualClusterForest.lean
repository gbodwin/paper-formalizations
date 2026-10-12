import MinorFreeSpanners.WeightedBranchingClusters

/-! Select the actual residual unit-edge forest on the original index type.
Vertices outside the residual are isolated, and every genuine branching core
is therefore wholly inside the residual. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset

def withinVertices {I : Type*} (Q : SimpleGraph I) (R : Set I) : SimpleGraph I where
  Adj i j := Q.Adj i j ∧ i∈R ∧ j∈R
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => Q.ne_of_adj h.1 rfl⟩

 theorem branchingCore_subset_residual {I : Type*} (H : SimpleGraph I)
    (R : Set I) (hR : ∀ i j,H.Adj i j → i∈R)
    (d : I → ℝ) (L D : ℝ) (S : Finset I) (hc : BranchingCore H d L D S) :
    ∀ v∈S,v∈R := by
  obtain ⟨x,N,hN,hadj,hNS⟩ := hc.2.1
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0<N.card by omega)
  have hxR := hR x y (hadj y hy)
  intro v hv
  obtain ⟨p,_⟩ := hc.1 v hv x (hNS (by simp))
  cases p with
  | nil => exact hxR
  | cons h _ => exact hR _ _ h

namespace ClusterFamily
variable {I V : Type*} {A G T : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem exists_residual_unit_forest (C : ClusterFamily (I := I) A w D)
    (R : Set I) (hT : T≤G) (hunit : ∀ e∈T.edgeSet,w e=1) :
    ∃ H : SimpleGraph I,H≤C.graph T ∧ H.IsAcyclic ∧
      H.Reachable=(withinVertices (C.graph T) R).Reachable ∧
      (∀ i j,H.Adj i j → i∈R) ∧
      (∀ i j,H.Adj i j → ∃ x∈C.branch i,
        ∃ y∈C.branch j,∃ _hxy : G.Adj x y,w s(x,y)≤1) := by
  obtain ⟨H,hH,hacyc,hreach⟩ :=
    (withinVertices (C.graph T) R).exists_isAcyclic_reachable_eq_le
  refine ⟨H,(fun _ _ h => (hH h).1),hacyc,hreach,
    (fun i j h => (hH h).2.1),?_⟩
  intro i j hij
  obtain ⟨_,x,hx,y,hy,hxy⟩ := (hH hij).1
  exact ⟨x,hx,y,hy,hT hxy,(hunit _ hxy).le⟩

end ClusterFamily
end MinorFreeSpanners
