import MinorFreeSpanners.ClusterGraph
import MinorFreeSpanners.ConnectedFinsetGrowth

/-! Actual host connectivity descends through a covering disjoint cluster
family, including edges whose endpoints stay inside one cluster. -/
namespace MinorFreeSpanners
open SimpleGraph
namespace ClusterFamily
variable {I V : Type*} [Fintype I] {A T : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem graph_connected_of_cover (C : ClusterFamily (I:=I) A w D)
    (hcover : ∀ x,∃ i,x∈C.branch i) (hT : T.Connected) :
    ConnectedWithin (C.graph T) Finset.univ := by
  classical
  have lift {x y : V} (p : T.Walk x y) :
      ∀ i,x∈C.branch i → ∀ j,y∈C.branch j → (C.graph T).Reachable i j := by
    induction p with
    | nil =>
      intro i hi j hj
      have he : i=j := by
        by_contra hn
        exact Set.disjoint_left.mp (C.disjoint i j hn) hi hj
      subst j
      exact .refl _
    | cons h p ih =>
      intro i hi j hj
      obtain ⟨k,hk⟩ := hcover _
      have hkj := ih k hk j hj
      by_cases he : i=k
      · simpa [he] using hkj
      · exact (show (C.graph T).Adj i k from ⟨he,_,hi,_,hk,h⟩).reachable.trans hkj
  intro i _ j _
  obtain ⟨x,hx⟩ := C.nonempty i
  obtain ⟨y,hy⟩ := C.nonempty j
  obtain ⟨p⟩ := hT.preconnected x y
  obtain ⟨q⟩ := lift p i hx j hy
  exact ⟨q,by simp⟩

end ClusterFamily
end MinorFreeSpanners
