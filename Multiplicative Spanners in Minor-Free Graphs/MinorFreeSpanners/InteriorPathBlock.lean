import MinorFreeSpanners.SelectedResidualPathSlices
import MinorFreeSpanners.FourArmCore
import Mathlib.Data.List.Basic

/-! A connected endpoint block in an actual forest lies wholly before every
vertex outside it along the component's spanning path. This links the
unordered block partition to genuine weighted path interior predicates. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem connected_start_block_before {I : Type*} (H : SimpleGraph I) (hH : H.IsAcyclic)
    {a b x : I} (p : H.Walk a b) (hp : p.IsPath)
    (S : Finset I) (hS : S⊆p.support.toFinset) (hconn : ConnectedWithin H S)
    (ha : a∈S) (hx : x∈p.support) (hxS : x∉S) :
    S⊆(p.takeUntil x hx).support.toFinset := by
  classical
  intro z hz
  have hzp : z∈p.support := List.mem_toFinset.mp (hS hz)
  obtain ⟨q,hq⟩ := hconn a ha z hz
  have he : p.takeUntil z hzp=q.toPath.val :=
    congrArg Subtype.val ((hH.subsingleton_path a z).elim
      ⟨p.takeUntil z hzp,hp.takeUntil hzp⟩ q.toPath)
  have hnot : x∉(p.takeUntil z hzp).support := by
    intro h
    rw [he] at h
    exact hxS (hq x (q.support_toPath_subset_support h))
  rw [Walk.takeUntil_eq_take,Walk.support_copy,Walk.support_take,
    List.mem_take_iff_idxOf_lt hx] at hnot
  apply List.mem_toFinset.mpr
  rw [Walk.takeUntil_eq_take,Walk.support_copy,Walk.support_take,
    List.mem_take_iff_idxOf_lt hzp]
  omega

 theorem connected_end_block_after {I : Type*} (H : SimpleGraph I) (hH : H.IsAcyclic)
    {a b x : I} (p : H.Walk a b) (hp : p.IsPath)
    (S : Finset I) (hS : S⊆p.support.toFinset) (hconn : ConnectedWithin H S)
    (hb : b∈S) (hx : x∈p.support) (hxS : x∉S) :
    S⊆(p.dropUntil x hx).support.toFinset := by
  classical
  have hx' : x∈p.reverse.support := by simpa using hx
  have hS' : S⊆p.reverse.support.toFinset := by simpa using hS
  have hh := connected_start_block_before H hH p.reverse hp.reverse S hS' hconn hb hx' hxS
  have he : p.reverse.takeUntil x hx'=(p.dropUntil x hx).reverse :=
    congrArg Subtype.val ((hH.subsingleton_path b x).elim
      ⟨p.reverse.takeUntil x hx',hp.reverse.takeUntil hx'⟩
      ⟨(p.dropUntil x hx).reverse,(hp.dropUntil hx).reverse⟩)
  simpa only [he,Walk.support_reverse,List.toFinset_reverse] using hh

 theorem interior_of_nonendpoint_block {I : Type*} (H : SimpleGraph I) (hH : H.IsAcyclic)
    {a b : I} (p : H.Walk a b) (hp : p.IsPath) (P : Finset (Finset I))
    (hcover : P.biUnion id=p.support.toFinset)
    (hdis : ∀ S∈P,∀ T∈P,S≠T → Disjoint S T)
    (hconn : ∀ S∈P,ConnectedWithin H S) (d : I → ℝ) (L : ℝ)
    (hd : ∀ i∈p.support,0≤d i) (hm : ∀ S∈P,L≤∑ i∈S,d i)
    (B : Finset I) (hB : B∈P) (haB : a∉B) (hbB : b∉B)
    (x : I) (hxB : x∈B) : WeightedInterior d L p x := by
  classical
  have hsub : ∀ S∈P,S⊆p.support.toFinset := by
    intro S hS i hi
    rw [←hcover]
    exact Finset.mem_biUnion.mpr ⟨S,hS,hi⟩
  have hx : x∈p.support := List.mem_toFinset.mp (hsub B hB hxB)
  obtain ⟨S,hS,haS⟩ := Finset.mem_biUnion.mp
    (hcover.symm ▸ List.mem_toFinset.mpr p.start_mem_support)
  obtain ⟨T,hT,hbT⟩ := Finset.mem_biUnion.mp
    (hcover.symm ▸ List.mem_toFinset.mpr p.end_mem_support)
  have hxS : x∉S := fun h => Finset.disjoint_left.mp
    (hdis S hS B hB (by intro he;exact haB (he ▸ haS))) h hxB
  have hxT : x∉T := fun h => Finset.disjoint_left.mp
    (hdis T hT B hB (by intro he;exact hbB (he ▸ hbT))) h hxB
  have hpre := connected_start_block_before H hH p hp S (hsub S hS) (hconn S hS) haS hx hxS
  have hpost := connected_end_block_after H hH p hp T (hsub T hT) (hconn T hT) hbT hx hxT
  refine ⟨hx,?_,?_⟩
  · exact (hm S hS).trans (Finset.sum_le_sum_of_subset_of_nonneg hpre
      (fun i hi _ => hd i (p.support_takeUntil_subset_support hx (List.mem_toFinset.mp hi))))
  · exact (hm T hT).trans (Finset.sum_le_sum_of_subset_of_nonneg hpost
      (fun i hi _ => hd i (p.support_dropUntil_subset_support hx (List.mem_toFinset.mp hi))))

end MinorFreeSpanners
