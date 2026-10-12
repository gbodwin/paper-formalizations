import MinorFreeSpanners.OriginalFamilyUnion
import MinorFreeSpanners.PriorCreditFromPhaseBills

/-! Exact finite indexing of the high roots inside a combined original-group
family. These are the literal high groups, rather than a new paid-label set. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*}

noncomputable def originalHighRoots (P Q : Finset (Finset I)) : Finset {S // S∈P∪Q} :=
  Finset.univ.filter (fun S => S.val∈P)

 theorem mem_originalHighRoots (P Q : Finset (Finset I)) (S : {S // S∈P∪Q}) :
    S∈originalHighRoots P Q ↔ S.val∈P := by
  classical
  simp [originalHighRoots]

 theorem originalHighRoots_union (P Q : Finset (Finset I)) :
    (originalHighRoots P Q).biUnion Subtype.val=P.biUnion id := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨S.val,(mem_originalHighRoots P Q S).mp hS,hi⟩
  · intro hi
    obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨⟨S,Finset.mem_union_left _ hS⟩,
      (mem_originalHighRoots P Q _).mpr hS,hi⟩

 theorem originalHighRoots_sum (P Q : Finset (Finset I)) (f : Finset I → ℝ) :
    (∑ S∈originalHighRoots P Q,f S.val)=∑ S∈P,f S := by
  classical
  apply Finset.sum_bij (fun S _ => S.val)
  · intro S hS
    exact (mem_originalHighRoots P Q S).mp hS
  · intro S _ Z _ he
    exact Subtype.ext he
  · intro S hS
    exact ⟨⟨S,Finset.mem_union_left _ hS⟩,(mem_originalHighRoots P Q _).mpr hS,rfl⟩
  · intro S _
    rfl

end MinorFreeSpanners
