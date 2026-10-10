import LinearDistancePreservers.LatticeFlatness
import Mathlib.MeasureTheory.Constructions.Pi

namespace LinearDistancePreservers.LatticeCaps
open MeasureTheory
open scoped RealInnerProductSpace

/-- An orthonormal coordinate system whose first axis is the chosen unit
normal. The remaining coordinates will be the actual transverse slices. -/
theorem exists_axis_basis (n : ℕ) (u : EuclideanSpace ℝ (Fin (n+3))) (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (n+3)) ℝ (EuclideanSpace ℝ (Fin (n+3))), b 0 = u := by
  let v : Fin (n+3) → EuclideanSpace ℝ (Fin (n+3)) := fun _ => u
  have hv : Orthonormal ℝ (({0} : Set (Fin (n+3))).domRestrict v) := by
    apply orthonormal_subsingleton_iff.mpr
    intro i
    exact hu
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b,hb 0 (by simp)⟩

/-- Splitting the first coordinate of Euclidean space preserves its
actual volume and the Euclidean squared norm. -/
noncomputable def sliceEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin (n+3)) ≃ᵐ (ℝ × EuclideanSpace ℝ (Fin (n+2))) :=
  ((MeasurableEquiv.toLp 2 (Fin (n+3) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+3) => ℝ) 0)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin (n+2) → ℝ)))

theorem sliceEquiv_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+3))) :
    sliceEquiv n x = (x 0,WithLp.toLp 2 (fun i : Fin (n+2) => x i.succ)) := by
  rfl

theorem sliceEquiv_measurePreserving (n : ℕ) : MeasurePreserving (sliceEquiv n) := by
  have h1 := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+3) => ℝ) 0).comp
    (PiLp.volume_preserving_ofLp (Fin (n+3)))
  have h2 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin (n+2)))
  exact h2.comp h1

theorem sliceEquiv_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+3))) :
    ‖(sliceEquiv n x).2‖^2+((sliceEquiv n x).1)^2 = ‖x‖^2 := by
  rw [sliceEquiv_apply]
  change ‖WithLp.toLp 2 (fun i : Fin (n+2) => x i.succ)‖^2+(x 0)^2 = ‖x‖^2
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq x]
  simp only [WithLp.ofLp_toLp]
  conv_rhs => rw [Fin.sum_univ_succ]
  ring

/-- Volume-preserving axial slicing in an arbitrary unit direction. -/
theorem exists_axial_slicing (n : ℕ) (u : EuclideanSpace ℝ (Fin (n+3))) (hu : ‖u‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin (n+3)) ≃ᵐ (ℝ × EuclideanSpace ℝ (Fin (n+2))),
      MeasurePreserving e ∧ ∀ x, (e x).1 = inner ℝ u x ∧
        ‖(e x).2‖^2+((e x).1)^2 = ‖x‖^2 := by
  obtain ⟨b,hb⟩ := exists_axis_basis n u hu
  let e := b.measurableEquiv.trans (sliceEquiv n)
  refine ⟨e,?_,?_⟩
  · exact (sliceEquiv_measurePreserving n).comp b.measurePreserving_repr
  · intro x
    constructor
    · change (b.repr x) 0 = inner ℝ u x
      rw [b.repr_apply_apply,hb]
    · change ‖(sliceEquiv n (b.repr x)).2‖^2+((sliceEquiv n (b.repr x)).1)^2 = ‖x‖^2
      rw [sliceEquiv_norm_sq,b.repr.norm_map]

end LinearDistancePreservers.LatticeCaps
