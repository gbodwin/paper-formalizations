import MinorFreeSpanners.BranchingCorePacking
import MinorFreeSpanners.VariableClusterWalkLift

/-! Actual bounded-diameter weighted branch unions from internally chosen
forest branching cores. The remaining large connected residuals are path-like. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem pathMass_add_one {I : Type*} {H : SimpleGraph I} (d : I → ℝ)
    {i j : I} (p : H.Walk i j) (hp : p.IsPath) :
    pathMass (fun i => d i+1) p=pathMass d p+p.length+1 := by
  classical
  simp [pathMass,Finset.sum_add_distrib,List.toFinset_card_of_nodup hp.support_nodup,
    Walk.length_support,add_assoc]

 theorem exists_weighted_branching_clusters {I V : Type*} [Fintype I]
    {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I := I) A w D) (hA : A≤G)
    (H : SimpleGraph I) (hH : H.IsAcyclic) (d : I → ℝ)
    (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤D)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ q : A.Walk x y,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i)
    (hbridge : ∀ i j,H.Adj i j → ∃ x∈C.branch i,∃ y∈C.branch j,
      ∃ _hxy : G.Adj x y,w s(x,y)≤1)
    (L : ℝ) (hD : 0≤D) (hLD : 3*(D+1)<L) :
    ∃ P : Finset (Finset I),∃ F : ClusterFamily (I := {S // S∈P}) G w (L+D),
      (∀ S∈P,BranchingCore H (fun i => d i+1) L (D+1) S) ∧
      (∀ S T,S∈P → T∈P → S≠T → Disjoint S T) ∧
      (∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i}) ∧
      (∀ W : Finset I,ConnectedWithin H W → Disjoint W (P.biUnion id) →
        (∃ a b,∃ p : H.Walk a b,p.IsPath ∧ (∀ v∈p.support,v∈W) ∧
          L≤pathMass (fun i => d i+1) p) →
        ∀ i∈W,((H.neighborFinset i)∩W).card≤2) := by
  classical
  obtain ⟨P,hcore,hdis,hres⟩ := exists_branching_core_packing H hH (fun i => d i+1)
    L (D+1) (by linarith) hLD (fun i => by have hh:=hd1 i;linarith)
    (fun i => by have hh:=hdD i;linarith)
  let F : ClusterFamily (I := {S // S∈P}) G w (L+D) := {
    branch := fun S => {x | ∃ i∈S.val,x∈C.branch i}
    nonempty := by
      intro S
      obtain ⟨i,N,_,_,hNS⟩ := (hcore S.val S.property).2.1
      obtain ⟨x,hx⟩ := C.nonempty i
      exact ⟨x,i,hNS (by simp),hx⟩
    disjoint := by
      intro S T hST
      apply Set.disjoint_left.mpr
      rintro x ⟨i,hi,hxi⟩ ⟨j,hj,hxj⟩
      have he : i=j := by
        by_contra hn
        exact Set.disjoint_left.mp (C.disjoint i j hn) hxi hxj
      subst j
      exact Finset.disjoint_left.mp (hdis S.val S.property T.val T.property
        (fun h => hST (Subtype.ext h))) hi hj
    connected := by
      rintro S x ⟨i,hi,hxi⟩ y ⟨j,hj,hyj⟩
      obtain ⟨p,hp⟩ := (hcore S.val S.property).1 i hi j hj
      let q := p.toPath
      have hqs : ∀ k∈q.val.support,k∈S.val := fun k hk => hp k (p.support_toPath_subset_support hk)
      have hm := (hcore S.val S.property).2.2.2 i j q.val q.property hqs
      obtain ⟨r,hrs,hrw⟩ := C.lift_path_variable hA H d hdiam hbridge q.val q.property
        {x | ∃ k∈S.val,x∈C.branch k} (fun k hk v hv => ⟨k,hqs k hk,hv⟩) hxi hyj
      rw [pathMass_add_one d q.val q.property] at hm
      exact ⟨r,hrs,by linarith⟩ }
  exact ⟨P,F,hcore,fun S T hS hT hne => hdis S hS T hT hne,fun _ => rfl,hres⟩

end MinorFreeSpanners
