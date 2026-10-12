import MinorFreeSpanners.ConnectedComponentSlice

/-! The actual components of a disjoint selected slice union correspond
bijectively to the original components which supplied those slices. Thus a
charge indexed by original components is neither omitted nor counted twice. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem exists_selected_component_owner {I : Type*} (H : SimpleGraph I)
    (R U : Finset I) (F : Finset (H.induce (R:Set I)).ConnectedComponent)
    (A : (H.induce (R:Set I)).ConnectedComponent → Finset I)
    (hA : ∀ t∈F,A t⊆ResidualComponents.block H R t)
    (hne : ∀ t∈F,(A t).Nonempty)
    (hf : ∀ t∈F,∃ q : (H.induce (U:Set I)).ConnectedComponent,ResidualComponents.block H U q=A t)
    (hg : ∀ q : (H.induce (U:Set I)).ConnectedComponent,∃ t∈F,ResidualComponents.block H U q=A t) :
    ∃ owner : (H.induce (U:Set I)).ConnectedComponent → (H.induce (R:Set I)).ConnectedComponent,
      (∀ q,owner q∈F ∧ ResidualComponents.block H U q=A (owner q)) ∧
      Function.Injective owner ∧ ∀ t∈F,∃ q,owner q=t := by
  classical
  choose owner hmem heq using hg
  have hi : Function.Injective owner := by
    intro q q' h
    by_contra hne
    obtain ⟨i,hi⟩ := ResidualComponents.nonempty H U q
    exact Finset.disjoint_left.mp (ResidualComponents.disjoint H U q q' hne) hi (by
      rw [heq q',←h,←heq q];exact hi)
  refine ⟨owner,fun q => ⟨hmem q,heq q⟩,hi,?_⟩
  intro t ht
  obtain ⟨q,hq⟩ := hf t ht
  refine ⟨q,?_⟩
  by_contra hne'
  obtain ⟨i,hit⟩ := hne t ht
  have hiq : i∈A (owner q) := by rw [←heq q,hq];exact hit
  exact Finset.disjoint_left.mp (ResidualComponents.disjoint H R (owner q) t hne')
    (hA _ (hmem q) hiq) (hA t ht hit)

 theorem component_owner_sum {I J : Type*} [Fintype I] (F : Finset J)
    (owner : I → J) (hmem : ∀ q,owner q∈F) (hinj : Function.Injective owner)
    (hsurj : ∀ t∈F,∃ q,owner q=t) (f : J → ℝ) :
    (∑ q,f (owner q))=∑ t∈F,f t := by
  classical
  apply Finset.sum_bij (fun q _ => owner q)
  · intro q _;exact hmem q
  · intro q _ q' _ h;exact hinj h
  · intro t ht
    obtain ⟨q,hq⟩ := hsurj t ht
    exact ⟨q,Finset.mem_univ q,hq⟩
  · intro q _;rfl

end MinorFreeSpanners
