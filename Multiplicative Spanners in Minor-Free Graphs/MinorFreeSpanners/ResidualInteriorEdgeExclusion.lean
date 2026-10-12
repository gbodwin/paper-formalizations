import MinorFreeSpanners.ResidualBlockInterior
import MinorFreeSpanners.SamePathInteriorExclusion

/-! Original heavy edges cannot join the small non-endpoint blocks of the
actual residual component partition. Both equal and distinct components are
handled on the same old weighted host. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem no_residual_small_interior_edge (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (hforest : H.IsAcyclic) (d : I → ℝ) (L M : ℝ)
    (W U R : Finset I) (hRW : R⊆W) (hRU : Disjoint R U)
    (hmax : ∀ S : Finset I,S⊆W → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    (F : Finset (H.induce (R:Set I)).ConnectedComponent) (N : ℕ)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (P : (H.induce (R:Set I)).ConnectedComponent → Finset (Finset I))
    (selected ends : (H.induce (R:Set I)).ConnectedComponent → Finset I)
    (hpart : ∀ t∈F,ResidualAttachmentPartition H R t (fun i => d i+1)
      M L N (port t) (P t) (selected t) (ends t))
    (hL : 0<L) (hd0 : ∀ i∈W,0≤d i+1) (hd : ∀ i∈W,d i≤D)
    {t q : (H.induce (R:Set I)).ConnectedComponent} (ht : t∈F) (hq : q∈F)
    {S T : Finset I} (hS : S∈P t) (hT : T∈P q)
    (hSN : S.card≤N) (hTN : T.card≤N)
    {x y : I} (hx : x∈S) (hy : y∈T) (hxE : x∉ends t) (hyE : y∉ends q)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) : ¬B.Adj a b := by
  classical
  obtain ⟨u,v,p,hp,hps,hpi⟩ := (hpart t ht).interior_path hforest
    (fun i hi => hd0 i (hRW hi))
  have hpx := hpi S hS hSN x hx hxE
  have hpR : p.support.toFinset⊆R := hps ▸ ResidualComponents.subset H R t
  by_cases htq : t=q
  · subst q
    exact C.no_residual_same_path_interior_edge H hforest d L W U hmax p hp hpx
      (hpi T hT hTN y hy hyE) (hpR.trans hRW)
      (Finset.disjoint_of_subset_left hpR hRU) hL hd0 hd ha hb
  obtain ⟨s,z,r,hr,hrs,hri⟩ := (hpart q hq).interior_path hforest
    (fun i hi => hd0 i (hRW hi))
  have hrR : r.support.toFinset⊆R := hrs ▸ ResidualComponents.subset H R q
  have hdis : Disjoint p.support.toFinset r.support.toFinset := by
    rw [hps,hrs]
    exact ResidualComponents.disjoint H R t q htq
  intro hab
  have hh := C.residual_distinct_paths_edge_near_end H d L W U hmax p r hp hr hdis
    (Finset.union_subset (hpR.trans hRW) (hrR.trans hRW))
    (Finset.disjoint_of_subset_left (Finset.union_subset hpR hrR) hRU) hL hd ha hb hab
  exact hh.elim (fun h => h hpx) (fun h => h (hri T hT hTN y hy hyE))

end ClusterFamily
end MinorFreeSpanners
