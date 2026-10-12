import MinorFreeSpanners.WeightedResidualPathAssembly

/-! The full one-root constructed path assembly is retained as a dependent
result, so independently selected root fibers can be combined without losing
its original-host walks, exact remainder blocks or credit inequalities. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

structure RootedPathAssemblyResult {I V : Type*} [Fintype I]
    {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
    (C : ClusterFamily (I:=I) B w D₀) (hB : B≤G) (hT : T≤G)
    (H : SimpleGraph I) (hH : H≤C.graph T) (R : Finset I) (root : I)
    (F : Finset (H.induce (R:Set I)).ConnectedComponent)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (d credit : I → ℝ) (M L c b a spare future : ℝ) (N : ℕ) where
  blocks : (H.induce (R:Set I)).ConnectedComponent → Finset (Finset I)
  selected : (H.induce (R:Set I)).ConnectedComponent → Finset I
  ends : (H.induce (R:Set I)).ConnectedComponent → Finset I
  partition : ∀ t∈F,ResidualAttachmentPartition H R t d M L N (port t)
    (blocks t) (selected t) (ends t)
  output_nonempty : ∀ S∈insert (insert root (F.biUnion selected))
    ((F.biUnion blocks)\F.image selected),S.Nonempty
  output_disjoint : ∀ S∈insert (insert root (F.biUnion selected))
    ((F.biUnion blocks)\F.image selected),∀ U∈insert (insert root (F.biUnion selected))
    ((F.biUnion blocks)\F.image selected),S≠U → Disjoint S U
  output_cover : (insert (insert root (F.biUnion selected))
    ((F.biUnion blocks)\F.image selected)).biUnion id=
    insert root (F.biUnion (ResidualComponents.block H R))
  rootGraph : SimpleGraph I
  rootGraph_sub : rootGraph≤C.graph T
  radius : ℝ
  radius_lower : d root-1≤radius
  radius_upper : radius≤d root-1+2*(2*L+M)
  root_walks : ∀ x∈{x | ∃ i∈insert root (F.biUnion selected),x∈C.branch i},
    ∀ y∈{x | ∃ i∈insert root (F.biUnion selected),x∈C.branch i},
      ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈insert root (F.biUnion selected),z∈C.branch i) ∧
        walkWeight w p≤radius
  root_payment : c*radius+a*(F.biUnion selected).card+(∑ t∈F,a*(ends t).card)+future≤
    c*(d root-1)+spare+(∑ i∈F.biUnion selected,credit i)+
      c*(∑ e∈C.connectorEdges hB hT rootGraph rootGraph_sub (insert root (F.biUnion selected)),w e)
  large_payment : ∀ S∈(F.biUnion blocks)\F.image selected,N<S.card →
    ∃ radius : ℝ,0≤radius ∧ L-1≤radius ∧ radius≤2*L+M-1 ∧
      (∀ x∈{x | ∃ i∈S,x∈C.branch i},∀ y∈{x | ∃ i∈S,x∈C.branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈S,z∈C.branch i) ∧ walkWeight w p≤radius) ∧
      c*radius+a*S.card+c*b/2≤(∑ i∈S,credit i)+
        c*(∑ e∈C.connectorEdges hB hT H hH S,w e)

namespace RootedPathAssemblyResult
variable {I V : Type*} [Fintype I] {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
variable {C : ClusterFamily (I:=I) B w D₀} {hB : B≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {R : Finset I} {root : I}
variable {F : Finset (H.induce (R:Set I)).ConnectedComponent}
variable {port : (H.induce (R:Set I)).ConnectedComponent → I}
variable {d credit : I → ℝ} {M L c b a spare future : ℝ} {N : ℕ}

noncomputable def output (Q : RootedPathAssemblyResult C hB hT H hH R root F port
    d credit M L c b a spare future N) : Finset (Finset I) := by
  classical
  exact insert (insert root (F.biUnion Q.selected)) ((F.biUnion Q.blocks)\F.image Q.selected)

 theorem output_ne (Q : RootedPathAssemblyResult C hB hT H hH R root F port
    d credit M L c b a spare future N) : ∀ S∈Q.output,S.Nonempty := Q.output_nonempty

 theorem output_pairwise (Q : RootedPathAssemblyResult C hB hT H hH R root F port
    d credit M L c b a spare future N) :
    ∀ S∈Q.output,∀ U∈Q.output,S≠U → Disjoint S U := Q.output_disjoint

 theorem output_union (Q : RootedPathAssemblyResult C hB hT H hH R root F port
    d credit M L c b a spare future N) :
    Q.output.biUnion id=insert root (F.biUnion (ResidualComponents.block H R)) := Q.output_cover

end RootedPathAssemblyResult

 theorem exists_rooted_path_assembly_result {I V : Type*} [Fintype I]
    {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
    (C : ClusterFamily (I:=I) B w D₀) (hB : B≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (hforest : H.IsAcyclic) (R : Finset I) (root : I) (hr : root∉R)
    (F : Finset (H.induce (R:Set I)).ConnectedComponent)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (hport : ∀ t∈F,port t∈ResidualComponents.block H R t)
    (hbridge : ∀ t∈F,(C.graph T).Adj root (port t))
    (d credit : I → ℝ) (M L c b a spare future : ℝ) (N : ℕ)
    (hM : 0≤M) (hL : 0<L) (hroot : 1≤d root) (hc : 0≤c) (ha : 0≤a)
    (hdeg : ∀ i∈R,((H.neighborFinset i)∩R).card≤2)
    (hd : ∀ i∈R,2≤d i) (hdM : ∀ i∈R,d i≤M)
    (hm : ∀ t∈F,L≤∑ i∈ResidualComponents.block H R t,d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : B.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i-1)
    (hcredit : ∀ i∈R,c*(d i-1)≤credit i) (hbase : ∀ i∈R,c*b≤credit i)
    (hsize : 2*(2*L+M)≤N*b) (hhalf : 2*a≤c*b)
    (hdonor : 2*(N:ℝ)*a≤c*L/4) (hbudget : 5*(N:ℝ)*a+future≤spare)
    (hcost : (N+1:ℕ)*a≤c*b/2) :
    Nonempty (RootedPathAssemblyResult C hB hT H hH R root F port
      d credit M L c b a spare future N) := by
  obtain ⟨P,selected,ends,hpart,hne,hdis,hcover,⟨J,hJ,radius,hlo,hhi,hwalk,hpaid⟩,hlarge⟩ :=
    weighted_residual_path_assembly C hB hT hunit H hH hforest R root hr F port
      hport hbridge d credit M L c b a spare future N hM hL hroot hc ha hdeg hd hdM hm
      hdiam hcredit hbase hsize hhalf hdonor hbudget hcost
  exact ⟨⟨P,selected,ends,hpart,hne,hdis,hcover,J,hJ,radius,hlo,hhi,hwalk,hpaid,hlarge⟩⟩

end MinorFreeSpanners
