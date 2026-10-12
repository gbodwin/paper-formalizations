import MinorFreeSpanners.WeightedFourArmClusters

/-! A finite carrier qualifies only when four actual threshold paths and an
actual original heavy edge witness it. Eligible original paths construct that
witness internally; the predicate contains no numeric credit conclusion. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

def WeightedInterior {I : Type*} {H : SimpleGraph I} (d : I → ℝ) (L : ℝ)
    {a b : I} (p : H.Walk a b) (x : I) : Prop :=
  ∃ hx : x∈p.support,L≤pathMass d (p.takeUntil x hx) ∧ L≤pathMass d (p.dropUntil x hx)

namespace ClusterFamily
variable {I V : Type*} {A : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

def FourArmCore (C : ClusterFamily (I := I) A w D) (H : SimpleGraph I)
    (d : I → ℝ) (L : ℝ) (B : SimpleGraph V) (S : Finset I) : Prop :=
  ∃ x y,∃ P : WeightedPathArms H (fun i => d i+1) L (D+1) x,
    ∃ Q : WeightedPathArms H (fun i => d i+1) L (D+1) y,
      Disjoint P.carrier Q.carrier ∧ S=P.carrier∪Q.carrier ∧
      ∃ a∈C.branch x,∃ b∈C.branch y,B.Adj a b

 theorem FourArmCore.nonempty (C : ClusterFamily (I := I) A w D)
    {H : SimpleGraph I} {d : I → ℝ} {L : ℝ} {B : SimpleGraph V} {S : Finset I}
    (h : C.FourArmCore H d L B S) : S.Nonempty := by
  obtain ⟨x,y,P,Q,_,rfl,_⟩ := h
  exact ⟨x,Finset.mem_union_left _ P.center_mem⟩

 theorem four_arm_core_of_paths (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) (B : SimpleGraph V)
    {u v s t x y : I} (p : H.Walk u v) (q : H.Walk s t)
    (hp : p.IsPath) (hq : q.IsPath)
    (hpq : Disjoint p.support.toFinset q.support.toFinset)
    (hx : WeightedInterior (fun i => d i+1) L p x)
    (hy : WeightedInterior (fun i => d i+1) L q y)
    (hL : 0<L) (hd : ∀ i∈p.support.toFinset∪q.support.toFinset,d i≤D)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) (hab : B.Adj a b) :
    ∃ S : Finset I,C.FourArmCore H d L B S ∧ S⊆p.support.toFinset∪q.support.toFinset := by
  classical
  obtain ⟨hxp,hxl,hxr⟩ := hx
  obtain ⟨hyq,hyl,hyr⟩ := hy
  obtain ⟨P,hP⟩ := exists_weighted_path_arms (fun i => d i+1) L (D+1) p hp hxp hL
    (fun i hi => by have h:=hd i (Finset.mem_union_left _ (List.mem_toFinset.mpr hi));linarith) hxl hxr
  obtain ⟨Q,hQ⟩ := exists_weighted_path_arms (fun i => d i+1) L (D+1) q hq hyq hL
    (fun i hi => by have h:=hd i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi));linarith) hyl hyr
  refine ⟨P.carrier∪Q.carrier,⟨x,y,P,Q,Finset.disjoint_of_subset_left hP
    (Finset.disjoint_of_subset_right hQ hpq),rfl,a,ha,b,hb,hab⟩,?_⟩
  exact Finset.union_subset_union hP hQ

 theorem FourArmCore.walks (C : ClusterFamily (I := I) A w D)
    {G : SimpleGraph V} (hA : A≤G) (H : SimpleGraph I) (d : I → ℝ) (L M : ℝ)
    (B : SimpleGraph V) (hB : B≤G) {S : Finset I} (h : C.FourArmCore H d L B S)
    (hd : ∀ i∈S,0≤d i+1)
    (hdiam : ∀ i a,a∈C.branch i → ∀ b,b∈C.branch i →
      ∃ p : A.Walk a b,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (hbridge : ∀ i j,H.Adj i j → ∃ a∈C.branch i,∃ b∈C.branch j,
      ∃ _hab : G.Adj a b,w s(a,b)≤1)
    (hM : 0≤M) (hweight : ∀ e∈B.edgeSet,w e≤M) :
    ∀ u,(∃ i∈S,u∈C.branch i) → ∀ v,(∃ i∈S,v∈C.branch i) →
      ∃ p : G.Walk u v,(∀ z∈p.support,∃ i∈S,z∈C.branch i) ∧
        walkWeight w p≤2*(L+D)+M := by
  obtain ⟨x,y,P,Q,_,rfl,a,ha,b,hb,hab⟩ := h
  exact C.four_arm_walks hA H d L M P Q hd hdiam hbridge ha hb (hB hab) hM (hweight _ hab)

end ClusterFamily
end MinorFreeSpanners
