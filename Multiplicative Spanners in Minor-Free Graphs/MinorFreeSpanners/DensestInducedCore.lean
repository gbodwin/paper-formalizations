import MinorFreeSpanners.MinimumDensityCore

/-! A genuine globally densest induced core, chosen internally, with an exact
real density and a universal original-subset edge upper bound. Among maximum
density sets the actual finite minimum-cardinality choice has degree>d. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- The exact chosen density controls every original induced subset, while
its own nonempty induced core has strictly larger minimum degree. -/
theorem exists_densest_induced_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d0 : ℝ) (hd0 : 0 < d0) (hn : 0 < Fintype.card V)
    (hden : d0*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ)) :
    ∃ d : ℝ, d0 ≤ d ∧ ∃ U : Finset V, U.Nonempty ∧
      ((G.induce (U:Set V)).edgeFinset.card:ℝ)=d*(U.card:ℝ) ∧
      (∀ v : U, d < ((G.induce (U:Set V)).degree v:ℝ)) ∧
      ∀ W : Finset V, ((G.induce (W:Set V)).edgeFinset.card:ℝ) ≤ d*(W.card:ℝ) := by
  classical
  let density := fun U : Finset V => ((G.induce (U:Set V)).edgeFinset.card:ℝ)/(U.card:ℝ)
  let nonemptySets := (Finset.univ : Finset (Finset V)).filter Finset.Nonempty
  have fullMem : (Finset.univ : Finset V) ∈ nonemptySets := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.card_pos.mp (by simpa using hn)⟩
  obtain ⟨T,hT,hmax⟩ := Finset.exists_max_image nonemptySets density ⟨_,fullMem⟩
  have hTne := (Finset.mem_filter.mp hT).2
  have hTpos : (0:ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hTne
  let d := density T
  have hfullEdges : (G.induce (↑(Finset.univ : Finset V):Set V)).edgeFinset.card=
      G.edgeFinset.card := by
    let e : (↑(Finset.univ : Finset V):Set V) ≃ V :=
      { toFun := Subtype.val
        invFun := fun v => ⟨v,Finset.mem_univ v⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let i : G.induce (↑(Finset.univ : Finset V):Set V) ≃g G :=
      RelIso.mk e (by intro x y; rfl)
    exact i.card_edgeFinset_eq
  have hd0d : d0 ≤ d := by
    have hp : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
    have hf : d0 ≤ density (Finset.univ : Finset V) := by
      dsimp [density]
      rw [hfullEdges]
      exact (le_div_iff₀ hp).mpr hden
    exact hf.trans (hmax _ fullMem)
  have hd : 0 < d := lt_of_lt_of_le hd0 hd0d
  have hupper : ∀ W : Finset V, ((G.induce (W:Set V)).edgeFinset.card:ℝ) ≤ d*(W.card:ℝ) := by
    intro W
    by_cases hW : W.Nonempty
    · have hp : (0:ℝ) < W.card := by exact_mod_cast Finset.card_pos.mpr hW
      have hw := hmax W (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hW⟩)
      exact (div_le_iff₀ hp).mp hw
    · have hz : W=∅ := Finset.not_nonempty_iff_eq_empty.mp hW
      subst W
      have hb := (G.induce (↑(∅:Finset V):Set V)).card_edgeFinset_le_card_choose_two
      simp only [← Set.toFinset_card,Finset.toFinset_coe,Finset.card_empty] at hb
      norm_num at hb
      simp [hb]
  have hTd : d*(T.card:ℝ) ≤ ((G.induce (T:Set V)).edgeFinset.card:ℝ) := by
    dsimp [d,density]
    rw [div_mul_cancel₀ _ (ne_of_gt hTpos)]
  let candidates := (Finset.univ : Finset (Finset V)).filter (fun U : Finset V =>
    U.Nonempty ∧ d*(U.card:ℝ) ≤ ((G.induce (U:Set V)).edgeFinset.card:ℝ))
  have hTin : T ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hTne,hTd⟩
  obtain ⟨U,hU,hmin⟩ := Finset.exists_min_image candidates Finset.card ⟨_,hTin⟩
  obtain ⟨hUne,hUd⟩ := (Finset.mem_filter.mp hU).2
  refine ⟨d,hd0d,?_⟩
  have hpos : 1 ≤ U.card := Finset.one_le_card.mpr hUne
  have htwo : 2 ≤ U.card := by
    by_contra h
    have he : U.card=1 := by omega
    have hb := (G.induce (U:Set V)).card_edgeFinset_le_card_choose_two
    simp only [← Set.toFinset_card,Finset.toFinset_coe,he] at hb
    change (G.induce (U:Set V)).edgeFinset.card ≤ 0 at hb
    have hz : ((G.induce (U:Set V)).edgeFinset.card:ℝ)=0 := by
      exact_mod_cast Nat.eq_zero_of_le_zero hb
    rw [he] at hUd
    norm_num only [Nat.cast_one,mul_one] at hUd
    linarith

  refine ⟨U,hUne,le_antisymm (hupper U) hUd,?_,hupper⟩
  · intro v
    by_contra hlow
    have hdeg : ((G.induce (U:Set V)).degree v:ℝ) ≤ d := le_of_not_gt hlow
    have hb := (G.induce (U:Set V)).degree_le_card_edgeFinset v
    have he := VFTSpanners.induced_erase_edge_count G U v
    have hc := Finset.card_erase_of_mem v.property
    have hcR : ((U.erase v.val).card:ℝ)+1=(U.card:ℝ) := by
      exact_mod_cast (show (U.erase v.val).card+1=U.card by omega)
    have heR : ((G.induce (↑(U.erase v.val):Set V)).edgeFinset.card:ℝ)+
        (G.induce (U:Set V)).degree v=(G.induce (U:Set V)).edgeFinset.card := by
      exact_mod_cast (show (G.induce (↑(U.erase v.val):Set V)).edgeFinset.card+
        (G.induce (U:Set V)).degree v=(G.induce (U:Set V)).edgeFinset.card by omega)
    have hdel : U.erase v.val ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_⟩
      · apply Finset.card_pos.mp
        omega
      · nlinarith
    have hs := hmin (U.erase v.val) hdel
    omega

end MinorFreeSpanners
