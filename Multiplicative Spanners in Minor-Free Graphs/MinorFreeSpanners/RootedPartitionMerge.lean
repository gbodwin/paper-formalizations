import MinorFreeSpanners.WeightedPathBlockFamily

/-! Merging a selected subfamily into one fresh root keeps a literal disjoint
partition of exactly the same vertices plus that root. No leftover block is
silently discarded. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable

 theorem rooted_partition_merge {I : Type*} (P Q : Finset (Finset I)) (root : I)
    (hQP : Q⊆P) (hroot : root∉P.biUnion id)
    (hne : ∀ S∈P,S.Nonempty)
    (hdis : ∀ S∈P,∀ T∈P,S≠T → Disjoint S T) :
    let rootBlock := insert root (Q.biUnion id)
    let out := insert rootBlock (P\Q)
    (∀ S∈out,S.Nonempty) ∧
    (∀ S∈out,∀ T∈out,S≠T → Disjoint S T) ∧
    out.biUnion id=insert root (P.biUnion id) := by
  classical
  let B := insert root (Q.biUnion id)
  have hrem : ∀ S∈P\Q,Disjoint B S := by
    intro S hS
    obtain ⟨hSP,hSQ⟩ := Finset.mem_sdiff.mp hS
    apply Finset.disjoint_left.mpr
    intro i hi hiS
    rcases Finset.mem_insert.mp hi with rfl | hiQ
    · exact hroot (Finset.mem_biUnion.mpr ⟨S,hSP,hiS⟩)
    · obtain ⟨T,hT,hiT⟩ := Finset.mem_biUnion.mp hiQ
      exact Finset.disjoint_left.mp (hdis T (hQP hT) S hSP
        (by intro h;exact hSQ (h ▸ hT))) hiT hiS
  refine ⟨?_,?_,?_⟩
  · intro S hS
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact ⟨root,Finset.mem_insert_self _ _⟩
    · exact hne S (Finset.mem_sdiff.mp hS).1
  · intro S hS T hT hST
    rcases Finset.mem_insert.mp hS with rfl | hS
    · rcases Finset.mem_insert.mp hT with rfl | hT
      · exact (hST rfl).elim
      · exact hrem T hT
    · rcases Finset.mem_insert.mp hT with rfl | hT
      · exact (hrem S hS).symm
      · exact hdis S (Finset.mem_sdiff.mp hS).1 T (Finset.mem_sdiff.mp hT).1 hST
  · ext i
    simp only [Finset.mem_biUnion,Finset.mem_insert,id_eq,Finset.mem_sdiff]
    constructor
    · rintro ⟨S,rfl | ⟨hSP,_⟩,hi⟩
      · rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inl rfl
        · obtain ⟨T,hT,hiT⟩ := Finset.mem_biUnion.mp hi
          exact Or.inr ⟨T,hQP hT,hiT⟩
      · exact Or.inr ⟨S,hSP,hi⟩
    · rintro (rfl | ⟨S,hSP,hi⟩)
      · exact ⟨B,Or.inl rfl,Finset.mem_insert_self _ _⟩
      · by_cases hSQ : S∈Q
        · exact ⟨B,Or.inl rfl,Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨S,hSQ,hi⟩)⟩
        · exact ⟨S,Or.inr ⟨hSP,hSQ⟩,hi⟩

end MinorFreeSpanners
