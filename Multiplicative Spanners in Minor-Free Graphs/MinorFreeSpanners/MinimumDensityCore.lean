import VFTSpanners.Moore
import Mathlib.Basic.Real.Basic

/-! Choose an actual nonempty induced density core by finite minimization.
Unlike a degree-only pruning statement, the exact original density floor
is retained, together with the minimum-degree and minimality witnesses. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- A nonempty graph of positive real edge density at least d contains an
actual induced graph still of density at least d and minimum degree>d.
Its vertex set is chosen internally, minimizing the actual number of vertices. -/
theorem exists_minimum_density_induced {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℝ) (hd : 0 < d) (hn : 0 < Fintype.card V)
    (hden : d*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ)) :
    ∃ U : Finset V, U.Nonempty ∧
      d*(U.card:ℝ) ≤ ((G.induce (U:Set V)).edgeFinset.card:ℝ) ∧
      (∀ v : U, d < ((G.induce (U:Set V)).degree v:ℝ)) ∧
      (∀ W : Finset V, W.Nonempty →
        d*(W.card:ℝ) ≤ ((G.induce (W:Set V)).edgeFinset.card:ℝ) → U.card ≤ W.card) := by
  classical
  let candidates := (Finset.univ : Finset (Finset V)).filter (fun U : Finset V =>
    U.Nonempty ∧ d*(U.card:ℝ) ≤ ((G.induce (U:Set V)).edgeFinset.card:ℝ))
  have hfull : (Finset.univ : Finset V) ∈ candidates := by
    have he : (G.induce (↑(Finset.univ : Finset V):Set V)).edgeFinset.card=
        G.edgeFinset.card := by
      let e : (↑(Finset.univ : Finset V):Set V) ≃ V :=
        { toFun := Subtype.val
          invFun := fun v => ⟨v,Finset.mem_univ v⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let i : G.induce (↑(Finset.univ : Finset V):Set V) ≃g G :=
        RelIso.mk e (by intro x y; rfl)
      exact i.card_edgeFinset_eq
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,Finset.card_pos.mp (by simpa using hn),by simpa [he] using hden⟩
  obtain ⟨U,hU,hmin⟩ := Finset.exists_min_image candidates Finset.card ⟨_,hfull⟩
  obtain ⟨hUne,hUd⟩ := (Finset.mem_filter.mp hU).2
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

  refine ⟨U,hUne,hUd,?_,?_⟩
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
  · intro W hW hWd
    exact hmin W (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hW,hWd⟩)

end MinorFreeSpanners
