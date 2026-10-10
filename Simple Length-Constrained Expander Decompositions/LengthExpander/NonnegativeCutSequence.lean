import LengthExpander.DirectDecomposition

/-! The union theorem does not require the individual cuts to be sparse.
This module builds the same attained-demand matching geometry from any
finite sequence of nonnegative length increases. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

def NonnegativeCuts (Cs : List (EdgeLength V)) : Prop :=
  ∀ C ∈ Cs, ∀ e, 0 ≤ C e

theorem nonnegativeCuts_total {Cs : List (EdgeLength V)} (hCs : NonnegativeCuts Cs) :
    ∀ e, 0 ≤ totalCut Cs e := by
  induction Cs with
  | nil => intro e; rfl
  | cons C Cs ih =>
    intro e
    exact add_nonneg (hCs C (by simp) e) (ih (fun D hD => hCs D (by simp [hD])) e)

theorem nonnegative_sequenceWeight_mono {w : EdgeLength V} {scale : ℝ}
    {Cs : List (EdgeLength V)} (hCs : NonnegativeCuts Cs) (hscale : 0 ≤ scale) :
    ∀ i j, i ≤ j → ∀ e, sequenceWeight w scale Cs i e ≤ sequenceWeight w scale Cs j e := by
  have step : ∀ i e, sequenceWeight w scale Cs i e ≤ sequenceWeight w scale Cs (i+1) e := by
    induction Cs generalizing w with
    | nil => simp
    | cons C Cs ih =>
      intro i e
      cases i with
      | zero => simpa using le_applyCut w C hscale (hCs C (by simp)) e
      | succ i => exact ih (fun D hD => hCs D (by simp [hD])) i e
  intro i j hij e
  exact (monotone_nat_of_le_succ (fun i => step i e)) hij

theorem nonnegativeCut_witness_geometry (G : SimpleGraph V) (A : NodeWeight V)
    (w : EdgeLength V) (h : ℝ) (s : ℕ) (Cs : List (EdgeLength V))
    (hCs : NonnegativeCuts Cs) (hh : 0 ≤ h) :
    ∃ D : Fin Cs.length → Demand V,
      (∀ i, Respects (D i) A) ∧
      (∀ i, demandSize (D i) = demandVolume G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s) ∧
      SequentialDemandGeometry G (sequenceWeight w (h*s) Cs) h s D := by
  classical
  let D (i : Fin Cs.length) := (exists_volume_witness G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s).choose
  have hD (i : Fin Cs.length) := (exists_volume_witness G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s).choose_spec
  refine ⟨D,fun i => (hD i).1.1,fun i => (hD i).2,?_⟩
  refine ⟨nonnegative_sequenceWeight_mono hCs (mul_nonneg hh (Nat.cast_nonneg s)),?_,?_⟩
  · intro i u v hp
    exact (hD i).1.2.1 u v hp
  · intro i u v hp
    rw [sequenceWeight_step]
    exact (hD i).1.2.2 u v hp

end LengthExpander
