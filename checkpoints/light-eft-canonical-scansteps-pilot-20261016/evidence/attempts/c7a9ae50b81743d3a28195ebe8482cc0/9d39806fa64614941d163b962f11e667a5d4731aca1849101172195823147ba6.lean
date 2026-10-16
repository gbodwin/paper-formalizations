import LightEFTSpanners.EvenSplittingMass

namespace LightEFTSpanners.EvenSplitting
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

def SkewSupermodular (p : Finset V → ℤ) : Prop :=
  ∀ S T,p S+p T≤p (S∩T)+p (S∪T) ∨ p S+p T≤p (S\T)+p (T\S)

omit [Fintype V] in
/-- Tight sets sharing an actual positive incident-edge identity have tight
union. Difference uncrossing is impossible because it loses that positive mass. -/
theorem tight_union (ends : I → V) (p : Finset V → ℤ)
    (hcover : ∀ S,p S≤mass ends S) (hskew : SkewSupermodular p)
    {S T : Finset V} (hs : p S=mass ends S) (ht : p T=mass ends T)
    (i : I) (hiS : ends i∈S) (hiT : ends i∈T) :
    p (S∪T)=mass ends (S∪T) := by
  have hp := mass_pos_of_mem ends i (mem_inter.mpr ⟨hiS,hiT⟩)
  rcases hskew S T with hu | hd
  · have hc := hcover (S∩T)
    have hc' := hcover (S∪T)
    have hm := mass_union_inter ends S T
    omega
  · have hc := hcover (S\T)
    have hc' := hcover (T\S)
    have hm := mass_sdiff_identity ends S T
    omega

/-- A maximal actual tight set containing the chosen incident endpoint
contains every such tight set; the finite maximization is constructed. -/
theorem exists_largest_tight (ends : I → V) (p : Finset V → ℤ)
    (hcover : ∀ S,p S≤mass ends S) (hskew : SkewSupermodular p) (i : I)
    (hex : ∃ S,ends i∈S ∧ p S=mass ends S) :
    ∃ A,ends i∈A ∧ p A=mass ends A ∧
      ∀ S,ends i∈S → p S=mass ends S → S⊆A := by
  classical
  let C : Finset (Finset V) := univ.filter (fun S => ends i∈S ∧ p S=mass ends S)
  obtain ⟨S,hi,hs⟩ := hex
  have hn : C.Nonempty := ⟨S,mem_filter.mpr ⟨mem_univ _,hi,hs⟩⟩
  obtain ⟨A,hA,hmax⟩ := C.exists_max_image Finset.card hn
  obtain ⟨hiA,htA⟩ := (mem_filter.mp hA).2
  refine ⟨A,hiA,htA,?_⟩
  intro T hiT htT
  have htU := tight_union ends p hcover hskew htA htT i hiA hiT
  have hU : A∪T∈C := mem_filter.mpr ⟨mem_univ _,mem_union_left _ hiA,htU⟩
  have hEq : A∪T=A := (eq_of_subset_of_card_le (subset_union_left) (hmax _ hU)).symm
  exact hEq ▸ subset_union_right

/-- Symmetry forbids a positive tight set from containing every incident
identity: its complement has zero mass but the same required deficit. -/
theorem exists_outside_tight (ends : I → V) (p : Finset V → ℤ)
    (hcover : ∀ S,p S≤mass ends S) (hsym : ∀ S,p Sᶜ=p S)
    {A : Finset V} (ht : p A=mass ends A) (i : I) (hi : ends i∈A) :
    ∃ j : I,ends j∉A := by
  classical
  by_contra! hall
  have hz : mass ends Aᶜ=0 := by
    unfold mass
    apply sum_eq_zero
    intro j _
    simp [hall j]
  have hc := hcover Aᶜ
  rw [hsym,ht,hz] at hc
  have hp := mass_pos_of_mem ends i hi
  omega
end LightEFTSpanners.EvenSplitting
