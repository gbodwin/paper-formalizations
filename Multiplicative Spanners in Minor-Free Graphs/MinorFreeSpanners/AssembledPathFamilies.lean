import MinorFreeSpanners.MultiRootPathAssembly

/-! All root-fiber assemblies are read through their single actual ownership
map. The global component segmentation is the same one used by the root walks
and payments, rather than a fresh independent existential path partition. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
variable {C : ClusterFamily (I:=I) B w D₀} {hB : B≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {roots : Finset I}
variable (O : ResidualOwnership H roots)
variable {d credit : I → ℝ} {M L c b a : ℝ} {spare future : {r // r∈roots} → ℝ} {N : ℕ}
variable (Q : (r : {r // r∈roots}) → RootedPathAssemblyResult C hB hT H hH
    (Finset.univ\roots) r.val (O.components r) O.port d credit M L c b a (spare r) (future r) N)

noncomputable def blocks (t : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent) :=
  (Q (O.owner t)).blocks t
noncomputable def selected (t : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent) :=
  (Q (O.owner t)).selected t
noncomputable def ends (t : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent) :=
  (Q (O.owner t)).ends t
noncomputable def rootCarrier (r : {r // r∈roots}) : Finset I := by
  classical
  exact insert r.val ((O.components r).biUnion (Q r).selected)
noncomputable def leftovers : Finset (Finset I) := by
  classical
  exact Finset.univ.biUnion fun r => ((O.components r).biUnion (Q r).blocks)\(O.components r).image (Q r).selected

 theorem component_partition (t : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent) :
    ResidualAttachmentPartition H (Finset.univ\roots) t d M L N (O.port t)
      (blocks O Q t) (selected O Q t) (ends O Q t) := by
  exact (Q (O.owner t)).partition t (by simp [ResidualOwnership.components])

 theorem rootCarrier_subset (r : {r // r∈roots}) : rootCarrier O Q r⊆O.filled r := by
  classical
  apply Finset.insert_subset_insert
  intro i hi
  obtain ⟨t,ht,hi⟩ := Finset.mem_biUnion.mp hi
  apply (O.mem_absorbed r i).mpr
  refine ⟨t,?_,?_⟩
  · simpa [ResidualOwnership.components] using ht
  · rw [←((Q r).partition t ht).cover]
    exact Finset.mem_biUnion.mpr ⟨(Q r).selected t,((Q r).partition t ht).member,hi⟩

 theorem leftover_component {S : Finset I} (hS : S∈leftovers O Q) :
    ∃ r : {r // r∈roots},∃ t∈O.components r,S∈(Q r).blocks t := by
  classical
  obtain ⟨r,_,hS⟩ := Finset.mem_biUnion.mp hS
  obtain ⟨t,ht,hS⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hS).1
  exact ⟨r,t,ht,hS⟩

 theorem leftover_subset {S : Finset I} (hS : S∈leftovers O Q) : S⊆Finset.univ\roots := by
  classical
  obtain ⟨r,t,ht,hS⟩ := leftover_component O Q hS
  intro i hi
  apply ResidualComponents.subset H (Finset.univ\roots) t
  rw [←((Q r).partition t ht).cover]
  exact Finset.mem_biUnion.mpr ⟨S,hS,hi⟩

 theorem leftover_good {S : Finset I} (hS : S∈leftovers O Q) :
    ∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support.toFinset=S ∧
      L≤pathMass d p ∧ pathMass d p<2*L+M := by
  obtain ⟨r,t,ht,hS⟩ := leftover_component O Q hS
  exact ((Q r).partition t ht).good S hS

 theorem full_partition :
    (∀ r,(rootCarrier O Q r).Nonempty) ∧
    (∀ r s,r≠s → Disjoint (rootCarrier O Q r) (rootCarrier O Q s)) ∧
    (∀ S∈leftovers O Q,S.Nonempty) ∧
    (∀ S∈leftovers O Q,∀ U∈leftovers O Q,S≠U → Disjoint S U) ∧
    (∀ r,Disjoint (rootCarrier O Q r) ((leftovers O Q).biUnion id)) ∧
    (Finset.univ.biUnion (rootCarrier O Q))∪(leftovers O Q).biUnion id=Finset.univ := by
  classical
  have href := finite_partition_refinement O.filled (fun r => (Q r).output)
    O.filled_disjoint (fun r => (Q r).output_union) (fun r => (Q r).output_ne)
    (fun r => (Q r).output_pairwise)
  let out := Finset.univ.biUnion fun r => (Q r).output
  have hroot (r) : rootCarrier O Q r∈out := Finset.mem_biUnion.mpr
    ⟨r,Finset.mem_univ _,Finset.mem_insert_self _ _⟩
  have hleft (S) (hS : S∈leftovers O Q) : S∈out := by
    obtain ⟨r,_,hS⟩ := Finset.mem_biUnion.mp hS
    exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,Finset.mem_insert_of_mem hS⟩
  refine ⟨fun r => ⟨r.val,Finset.mem_insert_self _ _⟩,
    fun r s hrs => (O.filled_disjoint r s hrs).mono (rootCarrier_subset O Q r) (rootCarrier_subset O Q s),
    fun S hS => href.1 S (hleft S hS),
    fun S hS U hU => href.2.1 S (hleft S hS) U (hleft U hU),?_,?_⟩
  · intro r
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨S,hS,hiS⟩ := Finset.mem_biUnion.mp hj
    have hne : rootCarrier O Q r≠S := by
      intro he
      have hr : r.val∈S := he ▸ Finset.mem_insert_self _ _
      exact (Finset.mem_sdiff.mp (leftover_subset O Q hS hr)).2 r.property
    exact Finset.disjoint_left.mp (href.2.1 _ (hroot r) S (hleft S hS) hne) hi hiS
  · apply Finset.eq_univ_iff_forall.mpr
    intro i
    obtain ⟨r,hr⟩ := O.filled_covers i
    have ho : i∈(Q r).output.biUnion id := by simpa only [(Q r).output_union,ResidualOwnership.filled,ResidualOwnership.absorbed] using hr
    obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp ho
    rcases Finset.mem_insert.mp hS with he | hS
    · subst S
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,hi⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨S,Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,hS⟩,hi⟩)

end AssembledPathFamilies
end MinorFreeSpanners
