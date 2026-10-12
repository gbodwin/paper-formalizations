import MinorFreeSpanners.SamePathCoreDichotomy
import MinorFreeSpanners.ShortCycleCorePacking
import MinorFreeSpanners.FourArmCorePacking

/-! Consecutive finite short-cycle and four-arm packings exclude every
far-to-far residual heavy edge, within one path or between disjoint paths.
Both families are selected internally from original graph witnesses. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem exists_path_core_partition [Fintype I] (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) (R : Finset I) :
    ∃ P Q : Finset (Finset I),
      (∀ S∈P,S⊆R ∧ C.ShortCycleCore H d L B S) ∧
      (∀ S∈Q,S⊆R ∧ C.FourArmCore H d L B S) ∧
      (∀ S∈P,∀ T∈P,S≠T → Disjoint S T) ∧
      (∀ S∈Q,∀ T∈Q,S≠T → Disjoint S T) ∧
      Disjoint (P.biUnion id) (Q.biUnion id) ∧
      ∀ S : Finset I,S⊆R → Disjoint S (P.biUnion id∪Q.biUnion id) →
        ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S := by
  classical
  obtain ⟨P,hP,hPP,hmaxP⟩ := C.exists_short_cycle_packing (B:=B) H d L R
  obtain ⟨Q,hQ,hQQ,hmaxQ⟩ := C.exists_four_arm_packing (B:=B) H d L (R\P.biUnion id)
  refine ⟨P,Q,hP,?_,hPP,hQQ,?_,?_⟩
  · intro S hS
    exact ⟨fun i hi => (Finset.mem_sdiff.mp ((hQ S hS).1 hi)).1,(hQ S hS).2⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨S,hS,hiS⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_sdiff.mp ((hQ S hS).1 hiS)).2 hi
  · intro S hSR hdis
    have hdP : Disjoint S (P.biUnion id) := Finset.disjoint_of_subset_right Finset.subset_union_left hdis
    have hdQ : Disjoint S (Q.biUnion id) := Finset.disjoint_of_subset_right Finset.subset_union_right hdis
    refine ⟨hmaxP S hSR hdP,hmaxQ S ?_ hdQ⟩
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hSR hi,fun h => Finset.disjoint_left.mp hdP hi h⟩

 theorem residual_same_path_edge_near_end (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) (R U : Finset I)
    (hmax : ∀ S : Finset I,S⊆R → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    {u v x y : I} (l : H.Walk x u) (m : H.Walk x y) (r : H.Walk y v)
    (hp : (l.reverse.append (m.append r)).IsPath) (hL : 0<L)
    (hR : (l.reverse.append (m.append r)).support.toFinset⊆R)
    (hU : Disjoint (l.reverse.append (m.append r)).support.toFinset U)
    (hd0 : ∀ i∈R,0≤d i+1) (hd : ∀ i∈R,d i≤D)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) (hab : B.Adj a b) :
    pathMass (fun i => d i+1) l<L ∨ pathMass (fun i => d i+1) r<L := by
  by_contra hn
  push Not at hn
  obtain ⟨S,hS,hcore⟩ := C.same_path_core_dichotomy H d L B l m r hp hL
    (fun i hi => hd0 i (hR (List.mem_toFinset.mpr hi)))
    (fun i hi => hd i (hR (List.mem_toFinset.mpr hi))) hn.1 hn.2 ha hb hab
  have hno := hmax S (hS.trans hR) (Finset.disjoint_of_subset_left hS hU)
  exact hcore.elim hno.1 hno.2

 theorem residual_distinct_paths_edge_near_end (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) (R U : Finset I)
    (hmax : ∀ S : Finset I,S⊆R → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    {u v s t x y : I} (p : H.Walk u v) (q : H.Walk s t)
    (hp : p.IsPath) (hq : q.IsPath)
    (hpq : Disjoint p.support.toFinset q.support.toFinset)
    (hR : p.support.toFinset∪q.support.toFinset⊆R)
    (hU : Disjoint (p.support.toFinset∪q.support.toFinset) U)
    (hL : 0<L) (hd : ∀ i∈R,d i≤D)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) (hab : B.Adj a b) :
    ¬WeightedInterior (fun i => d i+1) L p x ∨ ¬WeightedInterior (fun i => d i+1) L q y := by
  by_contra hn
  push Not at hn
  exact C.no_residual_four_arm_edge H d L R U (fun S hS hU => (hmax S hS hU).2)
    p q hp hq hpq hR hU hn.1 hn.2 hL hd ha hb hab

end ClusterFamily
end MinorFreeSpanners
