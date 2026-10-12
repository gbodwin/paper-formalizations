import MinorFreeSpanners.SelectedResidualInteriorTransport
import MinorFreeSpanners.ResidualInteriorEdgeExclusion

/-! The actual mixed component partition is tested against maximality of the
original small-cluster family. Expanded selected-root diameters never occur in
the short-cycle or four-arm predicates used to exclude an unpaid edge. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

attribute [-instance] instDecidableEqSum in
 theorem no_original_diameter_mixed_interior_edge (C : ClusterFamily (I:=I) A w D)
    (P : Finset (Finset I)) (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hK : K.IsAcyclic) (hH : H.IsAcyclic)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (d : I → ℝ) (radius : {S // S∈P} → ℝ) (L M : ℝ) (W U : Finset I)
    (hRW : Finset.univ\P.biUnion id⊆W) (hRU : Disjoint (Finset.univ\P.biUnion id) U)
    (hmax : ∀ S : Finset I,S⊆W → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    (N : ℕ)
    (port : (K.induce ((Finset.univ\selectedRoots P : Finset _):Set _)).ConnectedComponent → SelectedResidualIndex P)
    (blocks : (K.induce ((Finset.univ\selectedRoots P : Finset _):Set _)).ConnectedComponent → Finset (Finset (SelectedResidualIndex P)))
    (selected ends : (K.induce ((Finset.univ\selectedRoots P : Finset _):Set _)).ConnectedComponent → Finset (SelectedResidualIndex P))
    (hpart : ∀ t,ResidualAttachmentPartition K (Finset.univ\selectedRoots P) t
      (mixedEffectiveDiameter d radius) M L N (port t) (blocks t) (selected t) (ends t))
    (hL : 0<L) (hd0 : ∀ i∈W,0≤d i+1) (hd : ∀ i∈W,d i≤D)
    {t q : (K.induce ((Finset.univ\selectedRoots P : Finset _):Set _)).ConnectedComponent}
    {S T : Finset (SelectedResidualIndex P)} (hS : S∈blocks t) (hT : T∈blocks q)
    (hSN : S.card≤N) (hTN : T.card≤N)
    {x y : {i // i∉P.biUnion id}} (hx : Sum.inr x∈S) (hy : Sum.inr y∈T)
    (hxE : Sum.inr x∉ends t) (hyE : Sum.inr y∉ends q)
    {a b : V} (ha : a∈C.branch x.val) (hb : b∈C.branch y.val) : ¬B.Adj a b := by
  classical
  have hnonneg : ∀ i∈(Finset.univ\selectedRoots P : Finset _),0≤mixedEffectiveDiameter d radius i := by
    intro i hi
    cases i with
    | inl S => exact ((Finset.mem_sdiff.mp hi).2 (by simp [selectedRoots])).elim
    | inr i => exact hd0 i.val (hRW (Finset.mem_sdiff.mpr ⟨mem_univ _,i.property⟩))
  have hpaths (t : (K.induce ((Finset.univ\selectedRoots P : Finset _):Set _)).ConnectedComponent) :
      ∃ a b,∃ p : H.Walk a b,p.IsPath ∧
        p.support.toFinset⊆originalResidualIndices P (ResidualComponents.block K (Finset.univ\selectedRoots P) t) ∧
        ∀ S∈blocks t,S.card≤N → ∀ i : {i // i∉P.biUnion id},
          Sum.inr i∈S → Sum.inr i∉ends t → WeightedInterior (fun i => d i+1) L p i.val := by
    obtain ⟨u,v,p,hp,hps,hpi⟩ := (hpart t).interior_path hK hnonneg
    have hW : ∀ j∈ResidualComponents.block K (Finset.univ\selectedRoots P) t,j∉selectedRoots P :=
      fun j hj => (Finset.mem_sdiff.mp (ResidualComponents.subset K _ t hj)).2
    obtain ⟨a,b,r,hr,hrs,hri⟩ := selected_residual_interior_path_transport P K H hK hH hres d radius L
      (ResidualComponents.block K (Finset.univ\selectedRoots P) t) hW p hp
      (fun j hj => hps ▸ List.mem_toFinset.mpr hj)
    refine ⟨a,b,r,hr,fun i hi => hrs i (List.mem_toFinset.mp hi),?_⟩
    intro S hS hn i hi he
    exact hri i (hpi S hS hn (Sum.inr i) hi he)
  obtain ⟨u,v,p,hp,hps,hpi⟩ := hpaths t
  have hpR := hps.trans (originalResidualIndices_subset_complement P _)
  by_cases htq : t=q
  · subst q
    exact C.no_residual_same_path_interior_edge H hH d L W U hmax p hp
      (hpi S hS hSN x hx hxE) (hpi T hT hTN y hy hyE) (hpR.trans hRW)
      (Finset.disjoint_of_subset_left hpR hRU) hL hd0 hd ha hb
  obtain ⟨s,z,r,hr,hrs,hri⟩ := hpaths q
  have hrR := hrs.trans (originalResidualIndices_subset_complement P _)
  have hdis : Disjoint p.support.toFinset r.support.toFinset :=
    (originalResidualIndices_disjoint P (ResidualComponents.disjoint K _ t q htq)).mono hps hrs
  intro hab
  have hh := C.residual_distinct_paths_edge_near_end H d L W U hmax p r hp hr hdis
    (Finset.union_subset (hpR.trans hRW) (hrR.trans hRW))
    (Finset.disjoint_of_subset_left (Finset.union_subset hpR hrR) hRU) hL hd ha hb hab
  exact hh.elim (fun h => h (hpi S hS hSN x hx hxE)) (fun h => h (hri T hT hTN y hy hyE))

end ClusterFamily
end MinorFreeSpanners
