import MinorFreeSpanners.FullContractionModel
import MinorFreeSpanners.PostleMates

/-! Pick a real unabsorbed singleton neighbor outside the actual mate set.
The injectivity count uses original singleton branch identities. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace MinorModel
variable {I V : Type*} [Fintype I]
variable {F : SimpleGraph I} {G : SimpleGraph V}

theorem exists_singleton_nonmate (M : MinorModel F G) (hM : M.IsFull)
    (u : I) (c : V) (hc : c ∈ M.branch u) (T : Finset V)
    (hadj : ∀ x ∈ T, G.Adj c x) (hout : ∀ x ∈ T, x ∉ M.branch u)
    (hsingle : ∀ x ∈ T, ∃ i, M.branch i={x})
    (K eps1 eps2 d : ℝ) (hun : Unmated F K eps1 eps2 d)
    (hsmall : (F.degree u:ℝ) ≤ K*d) (hsize : eps1*d ≤ (T.card:ℝ)) :
    ∃ x ∈ T, ∃ v : I, M.branch v={x} ∧ F.Adj u v ∧
      (Fintype.card (F.commonNeighbors u v):ℝ) < eps2*d := by
  classical
  choose f hf using (fun x : T => hsingle x.val x.property)
  have hfi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    have hs : ({x.val}:Set V)={y.val} := (hf x).symm.trans ((congrArg M.branch he).trans (hf y))
    exact Set.singleton_injective hs
  let L := Finset.univ.image f
  have hcard : L.card=T.card := by
    dsimp [L]
    rw [Finset.card_image_of_injective _ hfi]
    simp
  have hex : ∃ v ∈ L, (Fintype.card (F.commonNeighbors u v):ℝ) < eps2*d := by
    by_contra hn
    push Not at hn
    have hsub : L ⊆ Finset.univ.filter (fun v => eps2*d ≤
        (Fintype.card (F.commonNeighbors u v):ℝ)) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn v hv⟩
    have hb := Finset.card_le_card hsub
    rw [hcard] at hb
    have hbR : (T.card:ℝ) ≤ ((Finset.univ.filter (fun v => eps2*d ≤
        (Fintype.card (F.commonNeighbors u v):ℝ))).card:ℝ) := by exact_mod_cast hb
    exact not_lt_of_ge (hsize.trans hbR) (hun u hsmall)
  obtain ⟨v,hv,hn⟩ := hex
  obtain ⟨x,_hx,rfl⟩ := Finset.mem_image.mp hv
  have huv : u ≠ f x := by
    intro he
    have hx : x.val ∈ M.branch u := by rw [he,hf x]; simp
    exact hout x.val x.property hx
  refine ⟨x.val,x.property,f x,hf x,?_,hn⟩
  exact hM u (f x) huv c hc x.val (by rw [hf x]; simp) (hadj x.val x.property)

end MinorModel
end MinorFreeSpanners
