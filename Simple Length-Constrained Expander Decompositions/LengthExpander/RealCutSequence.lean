import LengthExpander.RealParameterArboricity
import LengthExpander.DegreeUnion

/-! A valid all-real variant of the sequence geometry and direct decomposition.
The price of rounding the graph threshold is exponent 4/s rather than 2/s. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

structure RealSequentialDemandGeometry (G : SimpleGraph V) (w : ℕ → EdgeLength V)
    (h s : ℝ) {k : ℕ} (D : Fin k → Demand V) : Prop where
  monotone : ∀ i j, i ≤ j → ∀ e, w i e ≤ w j e
  near : ∀ i u v, 0 < D i u v → Near G (w i.val) h u v
  far : ∀ i u v, 0 < D i u v → Far G (w (i.val+1)) (h*s) u v

namespace RealSequentialDemandGeometry
variable {G : SimpleGraph V} {w : ℕ → EdgeLength V} {h s : ℝ}
    {k : ℕ} {D : Fin k → Demand V} (geo : RealSequentialDemandGeometry G w h s D)
include geo

theorem toFloor (hh : 0 ≤ h) (hs : 0 ≤ s) :
    SequentialDemandGeometry G w h ⌊s⌋₊ D := by
  refine ⟨geo.monotone,geo.near,?_⟩
  intro i u v hp p
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Nat.floor_le hs) hh) (geo.far i u v hp p)

/-- Preserve the real separation threshold, rather than weakening the final
cut geometry to the rounded graph-counting threshold. -/
theorem short_pair_far {A : NodeWeight V} (a : ∀ i, DemandAllocation (D i) A)
    (hh : 0 ≤ h) {x y : DirectedCopies A} (hxy : CopyShortPair (familyGraph a) x y) :
    Far G (w k) (h*(s-1)) (copyVertex x) (copyVertex y) := by
  rcases hxy with ⟨i,hi⟩ | ⟨z,⟨i,hi⟩,⟨j,hj⟩,hne⟩
  · have hf := (a i).graph_property _ (fun _ _ => far_symm) (geo.far i) hi
    have hf' := far_length_mono (geo.monotone (i.val+1) k i.isLt) hf
    intro p
    have hp := hf' p
    nlinarith
  · have hij : i ≠ j := by
      intro he; subst j
      exact hne ((a i).graph_matching x y z hi hj.symm)
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hf := (a i).graph_property _ (fun _ _ => far_symm) (geo.far i) hi
      have hn := near_length_mono (geo.monotone (i.val+1) j.val hij)
        ((a j).graph_property _ (fun _ _ => near_symm) (geo.near j) hj)
      exact far_length_mono (geo.monotone (i.val+1) k i.isLt) (dispersed_pair_far hf hn)
    · have hf := (a j).graph_property _ (fun _ _ => far_symm) (geo.far j) hj.symm
      have hn := near_length_mono (geo.monotone (j.val+1) i.val hji)
        ((a i).graph_property _ (fun _ _ => near_symm) (geo.near i) hi.symm)
      exact far_symm (far_length_mono (geo.monotone (j.val+1) k j.isLt) (dispersed_pair_far hf hn))

end RealSequentialDemandGeometry

theorem real_nonnegativeCut_geometry (G : SimpleGraph V) (A : NodeWeight V)
    (w : EdgeLength V) (h s : ℝ) (Cs : List (EdgeLength V))
    (hCs : NonnegativeCuts Cs) (hh : 0 ≤ h) (hs : 0 ≤ s) :
    ∃ D : Fin Cs.length → Demand V,
      (∀ i, Respects (D i) A) ∧
      (∀ i, demandSize (D i) = demandVolume G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s) ∧
      RealSequentialDemandGeometry G (sequenceWeight w (h*s) Cs) h s D := by
  classical
  let D (i : Fin Cs.length) := (exists_volume_witness G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s).choose
  have hD (i : Fin Cs.length) := (exists_volume_witness G (sequenceWeight w (h*s) Cs i.val) Cs[i.val] A h s).choose_spec
  refine ⟨D,fun i => (hD i).1.1,fun i => (hD i).2,?_⟩
  refine ⟨nonnegative_sequenceWeight_mono hCs (mul_nonneg hh hs),?_,?_⟩
  · intro i u v hp; exact (hD i).1.2.1 u v hp
  · intro i u v hp
    rw [sequenceWeight_step]
    exact (hD i).1.2.2 u v hp

theorem real_sequenceVolume_bound (G : SimpleGraph V) (A : NodeWeight V)
    (w : EdgeLength V) (h s : ℝ) (Cs : List (EdgeLength V))
    (hCs : NonnegativeCuts Cs) (hh : 0 ≤ h) (hs : 2 ≤ s) :
    (sequenceVolume G A h s w Cs : ℝ) ≤
      (8*s*(2*(weightSize A:ℝ))^(4/s))*(weightSize A:ℝ) := by
  classical
  obtain ⟨Ds,hr,hsize,geo⟩ := real_nonnegativeCut_geometry G A w h s Cs hCs hh (by linarith)
  let a i := demandAllocation (hr i)
  have hfloor := (floor_threshold_bounds hs).1
  have gi := geo.toFloor hh (by linarith : 0 ≤ s)
  have hpg := gi.parallelGreedy a hh (by omega)
  have hedge : Fintype.card (familyGraph a).edgeSet = sequenceVolume G A h s w Cs := by
    rw [familyGraph_edge_card a (gi.supportDisjoint hh (by omega)),sequenceVolume_eq_sum]
    exact sum_congr rfl (fun i _ => hsize i)
  have hb := parallelGreedy_edge_budget hpg hfloor
  rw [hedge,card_directedCopies] at hb
  have hp := rounded_density_le_smooth (2*weightSize A) hs
  push_cast at hb hp
  have hm := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (weightSize A) : (0:ℝ) ≤ weightSize A)
  nlinarith

/-- All-real repaired Theorem 5.1: the exact unscaled cut, with smooth
slack 8s(2|A|)^(4/s). The integer theorem retains its sharper 2/s exponent. -/
theorem exists_real_direct_decomposition (G : SimpleGraph V) (U : Sym2 V → ℕ)
    (A : NodeWeight V) (w : EdgeLength V) (h s φ : ℝ)
    (hh : 0 ≤ h) (hs : 2 ≤ s) (hφ : 0 ≤ φ) :
    ∃ C, IsDecomposition G U w A h s φ (8*s*(2*(weightSize A:ℝ))^(4/s)) C := by
  obtain ⟨Cs,hCs,hExp,_⟩ := exists_finite_maximal_sequence G U A h s φ hh (by linarith) w
  refine ⟨totalCut Cs,sequence_total_nonneg hCs,?_,hExp⟩
  have hc := sparseSequence_cost_le_volume hCs
  have hv := real_sequenceVolume_bound G A w h s Cs (sparseSequence_nonnegative hCs) hh hs
  have hm := mul_le_mul_of_nonneg_left hv hφ
  exact hc.trans (by nlinarith [hm])

end LengthExpander
