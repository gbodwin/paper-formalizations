import MinorFreeSpanners.WeightedPathPartition
import Mathlib.Data.List.Pairwise

/-! Internally selected disjoint path blocks cover the exact old path. The
block containing an actual attachment port is unique, and at most two blocks
contain its original endpoints. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem exists_weighted_path_block_family {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (D L : ℝ) (hD : 0≤D) (hL : 0<L)
    {x y : I} (p : H.Walk x y) (hp : p.IsPath)
    (hd : ∀ i∈p.support,d i≤D) (hm : L≤pathMass d p) :
    ∃ P : Finset (Finset I),
      (∀ S∈P,∀ T∈P,S≠T → Disjoint S T) ∧
      P.biUnion id=p.support.toFinset ∧
      ∀ S∈P,∃ u v,∃ q : H.Walk u v,q.IsPath ∧ q.support.toFinset=S ∧
        L≤pathMass d q ∧ pathMass d q<2*L+D := by
  classical
  obtain ⟨blocks,hblocks,hgood⟩ := exists_weighted_path_partition d D L hD hL p hp hd hm
  have hnodup : blocks.flatten.Nodup := hblocks.symm ▸ hp.support_nodup
  have hpw := (List.nodup_flatten.mp hnodup).2
  let P := (blocks.map List.toFinset).toFinset
  have hmem : ∀ S,S∈P ↔ ∃ nodes∈blocks,nodes.toFinset=S := by
    intro S
    simp [P]
  refine ⟨P,?_,?_,?_⟩
  · intro S hS T hT hST
    obtain ⟨s,hs,rfl⟩ := (hmem S).mp hS
    obtain ⟨t,ht,rfl⟩ := (hmem T).mp hT
    exact List.disjoint_toFinset_iff_disjoint.mpr (hpw.forall hs ht (by intro he;exact hST (he ▸ rfl)))
  · ext i
    simp only [Finset.mem_biUnion, id_eq,List.mem_toFinset]
    rw [←hblocks,List.mem_flatten]
    constructor
    · rintro ⟨S,hS,hi⟩
      obtain ⟨nodes,hn,rfl⟩ := (hmem S).mp hS
      exact ⟨nodes,hn,List.mem_toFinset.mp hi⟩
    · rintro ⟨nodes,hn,hi⟩
      exact ⟨nodes.toFinset,(hmem _).mpr ⟨nodes,hn,rfl⟩,List.mem_toFinset.mpr hi⟩
  · intro S hS
    obtain ⟨nodes,hn,rfl⟩ := (hmem S).mp hS
    obtain ⟨u,v,q,hq,he,hlo,hhi⟩ := hgood nodes hn
    exact ⟨u,v,q,hq,congrArg List.toFinset he,hlo,hhi⟩

 theorem disjoint_path_block_port {I : Type*} [DecidableEq I]
    (P : Finset (Finset I)) (port : I)
    (hdis : ∀ S∈P,∀ T∈P,S≠T → Disjoint S T) (hport : port∈P.biUnion id) :
    ∃ S∈P,port∈S ∧ ∀ T∈P,port∈T → T=S := by
  obtain ⟨S,hS,hp⟩ := Finset.mem_biUnion.mp hport
  refine ⟨S,hS,hp,?_⟩
  intro T hT ht
  by_contra hne
  exact Finset.disjoint_left.mp (hdis T hT S hS hne) ht hp

 theorem endpoint_blocks_card {I : Type*} [DecidableEq I]
    (P : Finset (Finset I)) (x y : I)
    (hdis : ∀ S∈P,∀ T∈P,S≠T → Disjoint S T)
    (hx : x∈P.biUnion id) (hy : y∈P.biUnion id) :
    (P.filter (fun S => x∈S ∨ y∈S)).card≤2 := by
  classical
  obtain ⟨S,hS,hxS,huniqS⟩ := disjoint_path_block_port P x hdis hx
  obtain ⟨T,hT,hyT,huniqT⟩ := disjoint_path_block_port P y hdis hy
  have hsub : P.filter (fun A => x∈A ∨ y∈A)⊆{S,T} := by
    intro A hA
    obtain ⟨hAP,hA⟩ := Finset.mem_filter.mp hA
    rcases hA with hAx | hAy
    · simp [huniqS A hAP hAx]
    · simp [huniqT A hAP hAy]
  exact (Finset.card_le_card hsub).trans (by by_cases h : S=T <;> simp [h])

 theorem exists_attached_path_blocks {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (D L : ℝ) (hD : 0≤D) (hL : 0<L)
    {x y : I} (p : H.Walk x y) (hp : p.IsPath)
    (hd : ∀ i∈p.support,d i≤D) (hm : L≤pathMass d p)
    (port : I) (hport : port∈p.support) (N : ℕ) :
    ∃ P : Finset (Finset I),∃ S∈P,
      (∀ A∈P,∀ B∈P,A≠B → Disjoint A B) ∧
      P.biUnion id=p.support.toFinset ∧ port∈S ∧
      (∀ A∈P,∃ u v,∃ q : H.Walk u v,q.IsPath ∧ q.support.toFinset=A ∧
        L≤pathMass d q ∧ pathMass d q<2*L+D) ∧
      ((P.filter (fun A => (x∈A ∨ y∈A) ∧ A.card≤N)).biUnion id).card≤2*N := by
  classical
  obtain ⟨P,hdis,hcover,hgood⟩ := exists_weighted_path_block_family d D L hD hL p hp hd hm
  obtain ⟨S,hS,hportS,_⟩ := disjoint_path_block_port P port hdis (by simpa [hcover] using hport)
  let E := P.filter (fun A => (x∈A ∨ y∈A) ∧ A.card≤N)
  have hE : E.card≤2 := (Finset.card_le_card (show E⊆P.filter (fun A => x∈A ∨ y∈A) from
    fun A hA => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1,(Finset.mem_filter.mp hA).2.1⟩)).trans
      (endpoint_blocks_card P x y hdis (by simp [hcover])
        (by simp [hcover]))
  have heach : ∀ A∈E,A.card≤N := fun A hA => (Finset.mem_filter.mp hA).2.2
  have hsum : (∑ A∈E,A.card)≤E.card*N := by
    calc
      _ ≤ ∑ _A∈E,N := Finset.sum_le_sum heach
      _ = _ := by simp
  have hbound : (E.biUnion id).card≤2*N :=
    (Finset.card_biUnion_le).trans (hsum.trans (Nat.mul_le_mul_right N hE))
  exact ⟨P,S,hS,hdis,hcover,hportS,hgood,hbound⟩

end MinorFreeSpanners
