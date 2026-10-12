import MinorFreeSpanners.RootedPathReserve

/-! Actual long residual paths supply released credit. Disjoint component
supports prevent reusing any donor, and the diameter reserve can obstruct
only the two components met by its actual supporting simple path. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem path_released_credit_lower {I : Type*} {H : SimpleGraph I}
    {x y : I} (p : H.Walk x y) (d credit : I → ℝ) (c a : ℝ)
    (hc : 0≤c) (hd : ∀ i∈p.support,2≤d i)
    (hcredit : ∀ i∈p.support,c*(d i-1)≤credit i)
    (hhalf : ∀ i∈p.support,2*a≤credit i) :
    c*pathMass d p/4≤∑ i∈p.support.toFinset,(credit i-a) := by
  classical
  have hh : ∀ i∈p.support.toFinset,c*d i/4≤credit i-a := by
    intro i hi
    have hi' := List.mem_toFinset.mp hi
    have hm := mul_nonneg hc (show 0≤d i-2 by linarith [hd i hi'])
    nlinarith [hcredit i hi',hhalf i hi']
  have hs := Finset.sum_le_sum hh
  simpa [pathMass,Finset.sum_div,Finset.mul_sum] using hs

 theorem residual_path_donor_credit {I : Type*} (H : SimpleGraph I)
    (U R : Finset I) (Q F : Finset (H.induce (U:Set I)).ConnectedComponent)
    (d credit : I → ℝ) (L c a : ℝ) (hc : 0≤c) (ha : 0≤a)
    (hcover : ∀ i∈R,∃ t∈Q,i∈ResidualComponents.block H U t)
    (hd : ∀ i∈U,2≤d i) (hcredit : ∀ i∈U,c*(d i-1)≤credit i)
    (hhalf : ∀ i∈U,2*a≤credit i)
    (hlong : ∀ t∈F,∃ x y,∃ p : H.Walk x y,p.IsPath ∧
      (∀ i∈p.support,i∈ResidualComponents.block H U t) ∧ L≤pathMass d p) :
    c*L/4*(F\Q).card≤∑ i∈U\R,(credit i-a) := by
  classical
  let B := (F\Q).biUnion (ResidualComponents.block H U)
  have hBS : B⊆U\R := by
    intro i hi
    obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp hi
    refine Finset.mem_sdiff.mpr ⟨ResidualComponents.subset H U t hit,?_⟩
    intro hiR
    obtain ⟨s,hs,his⟩ := hcover i hiR
    have hts : t≠s := by intro he;exact (Finset.mem_sdiff.mp ht).2 (he ▸ hs)
    exact Finset.disjoint_left.mp (ResidualComponents.disjoint H U t s hts) hit his
  have hnonneg : ∀ i∈U,0≤credit i-a := by
    intro i hi
    linarith [hhalf i hi]
  have hcomp : ∀ t∈F\Q,c*L/4≤∑ i∈ResidualComponents.block H U t,(credit i-a) := by
    intro t ht
    obtain ⟨x,y,p,_,hps,hL⟩ := hlong t (Finset.mem_sdiff.mp ht).1
    have hsub : p.support.toFinset⊆ResidualComponents.block H U t :=
      fun i hi => hps i (List.mem_toFinset.mp hi)
    have hpU : ∀ i∈p.support,i∈U := fun i hi => ResidualComponents.subset H U t (hps i hi)
    have hpath := path_released_credit_lower p d credit c a hc
      (fun i hi => hd i (hpU i hi)) (fun i hi => hcredit i (hpU i hi))
      (fun i hi => hhalf i (hpU i hi))
    have hmono := mul_le_mul_of_nonneg_left hL hc
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i hi _ => hnonneg i (ResidualComponents.subset H U t hi))
    linarith
  have hsum := Finset.sum_le_sum hcomp
  have he := Finset.sum_biUnion (s:=F\Q) (f:=fun i => credit i-a)
    (t:=ResidualComponents.block H U)
    (fun t _ s _ hts => ResidualComponents.disjoint H U t s hts)
  have hbig := Finset.sum_le_sum_of_subset_of_nonneg hBS
    (fun i hi _ => hnonneg i (Finset.mem_sdiff.mp hi).1)
  change (∑ i∈B,(credit i-a))=(∑ t∈F\Q,∑ i∈ResidualComponents.block H U t,(credit i-a)) at he
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

end MinorFreeSpanners
