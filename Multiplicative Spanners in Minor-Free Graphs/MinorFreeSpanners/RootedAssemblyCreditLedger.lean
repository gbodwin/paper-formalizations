import MinorFreeSpanners.RootedPathAssemblyResult

/-! The constructed long-path root output retains its original paid ledger.
Its selected-block and endpoint allocations are already spent; only the exact
future reserve survives for a later heavy-block absorption. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace RootedPathAssemblyResult
variable {I V : Type*} [Fintype I] {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
variable {C : ClusterFamily (I:=I) B w D₀} {hB : B≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {R : Finset I} {root : I}
variable {F : Finset (H.induce (R:Set I)).ConnectedComponent}
variable {port : (H.induce (R:Set I)).ConnectedComponent → I}
variable {d credit : I → ℝ} {M L c b a spare future : ℝ} {N : ℕ}

 theorem retained_root_credit_ledger (Q : RootedPathAssemblyResult C hB hT H hH R root F port
    d credit M L c b a spare future N) (hr : root∉R)
    (hrootcredit : c*(d root-1)+spare≤credit root) :
    (a*(F.biUnion Q.selected).card+(∑ t∈F,a*(Q.ends t).card))+c*Q.radius+future≤
      (∑ i∈insert root (F.biUnion Q.selected),credit i)+
        c*(∑ e∈C.connectorEdges hB hT Q.rootGraph Q.rootGraph_sub
          (insert root (F.biUnion Q.selected)),w e) := by
  classical
  have hnot : root∉F.biUnion Q.selected := by
    intro hi
    obtain ⟨t,ht,hi⟩ := Finset.mem_biUnion.mp hi
    have hmem : root∈ResidualComponents.block H R t := by
      rw [←(Q.partition t ht).cover]
      exact Finset.mem_biUnion.mpr ⟨Q.selected t,(Q.partition t ht).member,hi⟩
    exact hr (ResidualComponents.subset H R t hmem)
  rw [Finset.sum_insert hnot]
  have hp := Q.root_payment
  linarith

end RootedPathAssemblyResult
end MinorFreeSpanners
