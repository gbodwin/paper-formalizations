import LightEFTSpanners.NativeIsolatedIslandReduction

namespace LightEFTSpanners.EvenSplitting
open MultigraphCuts SimpleGraph
universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Finite native Eulerian forest packing. Every original pair surviving fewer
than2k edge deletions is connected in every one of k edge-disjoint original-edge
forests. The induction constructs both smaller-instance families; neither
Mader splitting nor the desired forest packing is assumed as a primitive.
This theorem is an existence result and makes no polynomial-time claim. -/
theorem exists_native_eulerian_forest_packing (G : Graph V E) (k : ℕ)
    (hall : G.vertexSet=Set.univ) (hdeg : ∀ x,Even (nativeDegree G x)) :
    HasNativeForestPacking G k := by
  classical
  let Q : ℕ → Prop := fun n => ∀ (W : Type u) (hW : Fintype W)
      (F : Type v) (hF : Fintype F) (H : Graph W F),
    letI := hW
    letI := hF
    Fintype.card W=n → H.vertexSet=Set.univ →
      (∀ x,Even (nativeDegree H x)) → HasNativeForestPacking H k
  have hQ : ∀ n,Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W hW F hF H hn hfull hd
      let := hW
      let := hF
      by_cases hsmall : n≤1
      · let : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        exact forestPacking_of_subsingleton H k
      · by_cases hconn : ∀ x y : H.vertexSet,FaultConnected H (2*k) x y
        · have hpos : 0<Fintype.card W := by omega
          obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
          exact forestPacking_of_all_pairs H k ⟨x,by rw [hfull]; trivial⟩ hconn
        · obtain ⟨x,y,hxy⟩ : ∃ x y : H.vertexSet,¬FaultConnected H (2*k) x y := by
            simpa only [not_forall] using hconn
          by_cases hbasic : ∀ a : H.vertexSet,∃ b : H.vertexSet,a≠b ∧ FaultConnected H (2*k) a b
          · obtain ⟨K,_,_,hfullK,hcard,hdegK,hconnK,hlift⟩ :=
              exists_native_basic_core_reduction H k hfull hd hxy hbasic
            let J := H.map (collapseOutside (K:Set W)ᶜ)
            have hlt : Fintype.card (Option {v : W // v∉K})<n := by omega
            have hp := ih _ hlt (Option {v : W // v∉K}) inferInstance F hF J rfl hfullK hdegK
            obtain ⟨A,hA,hAd,hAj⟩ := hp
            obtain ⟨B,hB,hBd,hBj⟩ := hlift A (fun c => (hA c).1) (fun c => (hA c).2) hAd
            refine ⟨B,hB,hBd,?_⟩
            intro c a b hab
            have hr := hAj c (mapVertex H _ a) (mapVertex H _ b) (hconnK a b hab)
            obtain ⟨_,_,hr'⟩ := hBj c a b
              ⟨(mapVertex H _ a).property,(mapVertex H _ b).property,hr⟩
            exact hr'
          · obtain ⟨a,ha⟩ := not_forall.mp hbasic
            obtain ⟨F',hF',J,hfullJ,hdJ,hlift⟩ :=
              exists_native_isolated_island_reduction H k hfull hd a ha
            let := hF'
            have hlt : Fintype.card {v : W // v≠a.val}<n := by
              have hc := Fintype.card_subtype_lt (p:=fun v : W => v≠a.val) (x:=a.val) (by simp)
              omega
            exact hlift (ih _ hlt {v : W // v≠a.val} inferInstance F' hF' J rfl hfullJ hdJ)
  exact hQ _ V inferInstance E inferInstance G rfl hall hdeg
end LightEFTSpanners.EvenSplitting
