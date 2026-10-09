import LinearDistancePreservers.BehrendPorts

/-! Actual inner direction families obtained by pigeonholing squared
norms in an integer box. This supplies a quantitative, assumption-free
family, but its fixed-dimension exponent is weaker than the sharp
Bárány–Larman bound used in the paper. -/
namespace LinearDistancePreservers.SphereDirections
open Finset DirectionGraph
attribute [local instance] Classical.propDecidable

/-- Select exactly `x` distinct directions on one sphere. The entire
geometric input, including average rigidity, is proved here. -/
theorem exists_directions {d r x : ℕ}
    (h : x*(d*(r-1)^2+1) ≤ r^d) :
    ∃ v : Fin x → Fin d → ℕ,
      Function.Injective v ∧ (∀ a i, v a i < r) ∧ AverageRigid v := by
  classical
  obtain ⟨s,_,hs⟩ := Behrend.exists_large_sphere_aux d r
  have hden : (0 : ℝ) < (d*(r-1)^2 : ℕ)+1 := by positivity
  have hx : (x : ℝ) ≤ (Behrend.sphere d r s).card := by
    apply le_trans _ hs
    apply (le_div_iff₀ hden).mpr
    exact_mod_cast h
  have hc : Fintype.card (Fin x) ≤ Fintype.card (Behrend.sphere d r s) := by
    simpa using (show x ≤ (Behrend.sphere d r s).card by exact_mod_cast hx)
  let f : Fin x ↪ Behrend.sphere d r s :=
    (Function.Embedding.nonempty_of_card_le hc).some
  let v : Fin x → Fin d → ℕ := fun a => (f a).val
  have hn (a : Fin x) : ∑ i, v a i^2 = s := (mem_filter.mp (f a).property).2
  refine ⟨v,Subtype.val_injective.comp f.injective,?_,sphere_rigid v ?_⟩
  · intro a i
    exact Behrend.mem_box.mp (mem_filter.mp (f a).property).1 i
  · intro a b
    exact_mod_cast (hn a).trans (hn b).symm

end LinearDistancePreservers.SphereDirections
