import MinorFreeSpanners.OriginalPaidRootFamily

/-! Merging actual paid root families preserves their common radius floor.
This is an exact statement about the retained radius function, rather than an
inference from its upper cap or from the available credit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace OriginalPaidRootFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
variable {C : ClusterFamily (I:=I) A w D} {hA : A≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {credit : I → ℝ} {c reserve U : ℝ}

 theorem merge_radius_floor
    (X Y : OriginalPaidRootFamily (B:=B) C hA hT H hH credit c reserve U)
    (cross : ∀ S∈X.groups,∀ Z∈Y.groups,Disjoint S Z) (floor : ℝ)
    (hx : ∀ S,floor≤X.radius S) (hy : ∀ S,floor≤Y.radius S) :
    ∀ S,floor≤(X.merge Y cross).radius S := by
  intro S
  change floor≤(if h : S.val∈X.groups then X.radius ⟨S.val,h⟩ else Y.radius _)
  split
  · exact hx _
  · exact hy _

end OriginalPaidRootFamily
end MinorFreeSpanners
