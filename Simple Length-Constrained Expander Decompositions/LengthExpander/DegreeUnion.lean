import LengthExpander.UnionBoundConstants
import LengthExpander.DegreeDecomposition

/-! The simplified union theorem for a nonempty sparse-cut sequence,
unit capacities, and the original graph's degree weighting. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem sparseSequence_nonnegative {G : SimpleGraph V} {U : Sym2 V → ℕ}
    {A : NodeWeight V} {h s φ : ℝ} {w : EdgeLength V} {Cs : List (EdgeLength V)}
    (hCs : SparseSequence G U A h s φ w Cs) : NonnegativeCuts Cs := by
  induction Cs generalizing w with
  | nil => simp [NonnegativeCuts]
  | cons C Cs ih =>
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hCs.1.1
    · exact ih hCs.2 D hD

theorem sparseSequence_volume_pos {G : SimpleGraph V} {U : Sym2 V → ℕ}
    {A : NodeWeight V} {h s φ : ℝ} {w : EdgeLength V} {Cs : List (EdgeLength V)}
    (hCs : SparseSequence G U A h s φ w Cs) (hne : Cs ≠ []) :
    0 < sequenceVolume G A h s w Cs := by
  cases Cs with
  | nil => exact False.elim (hne rfl)
  | cons C Cs => exact Nat.add_pos_left hCs.1.2.1 _

/-- A sparse input sequence removes the ratio of summed costs to summed
volumes, with all node-weight and integral-demand conventions retained. -/
theorem sparseSequence_union {G : SimpleGraph V} {U : Sym2 V → ℕ}
    {A : NodeWeight V} {h φ : ℝ} {s : ℕ} {w : EdgeLength V} {Cs : List (EdgeLength V)}
    (hCs : SparseSequence G U A h s φ w Cs) (hh : 0 ≤ h) (hs : 2 ≤ s)
    (hne : Cs ≠ []) :
    SparseCut G U w A (2*h) (((s:ℝ)-1)/2)
      (512*(s:ℝ)*(weightSize A:ℝ)^(2/(s:ℝ))*φ) (unionCut Cs s) := by
  have hv := sparseSequence_volume_pos hCs hne
  have hc := union_sparseCut_explicit G U A w h s Cs (sparseSequence_nonnegative hCs) hh hs hv
  have hv' : (0:ℝ) < sequenceVolume G A h s w Cs := by exact_mod_cast hv
  have hratio : cutCost G U (totalCut Cs) / (sequenceVolume G A h s w Cs : ℝ) ≤ φ :=
    (div_le_iff₀ hv').mpr (sparseSequence_cost_le_volume hCs)
  have hfactor : (0:ℝ) ≤ 512*(s:ℝ)*(weightSize A:ℝ)^(2/(s:ℝ)) := by positivity
  have hb := mul_le_mul_of_nonneg_left hratio hfactor
  rw [← mul_div_assoc] at hb
  exact ⟨hc.1,hc.2.1,hc.2.2.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _))⟩

/-- Theorem 1.4 with explicit loss 2048*s*n^(4/s), for integer s>=2.
The sequence is nonempty so the resulting sparse cut has positive volume. -/
theorem degree_sparseSequence_union (G : SimpleGraph V) (w : EdgeLength V)
    (h φ : ℝ) (s : ℕ) (Cs : List (EdgeLength V))
    (hCs : SparseSequence G (fun _ => 1) (fun v => G.degree v) h s φ w Cs)
    (hh : 0 ≤ h) (hφ : 0 ≤ φ) (hs : 2 ≤ s) (hne : Cs ≠ []) :
    SparseCut G (fun _ => 1) w (fun v => G.degree v) (2*h) (((s:ℝ)-1)/2)
      (2048*(s:ℝ)*(Fintype.card V:ℝ)^(4/(s:ℝ))*φ) (unionCut Cs s) := by
  classical
  have hc := sparseSequence_union hCs hh hs hne
  have hdeg : weightSize (fun v => G.degree v) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hm : G.edgeFinset.card ≤ (Fintype.card V)^2 := by
    have hh' : ∑ v, G.degree v ≤ ∑ _ : V, Fintype.card V :=
      sum_le_sum (fun v _ => (G.degree_lt_card_verts v).le)
    rw [G.sum_degrees_eq_twice_card_edges] at hh'
    simp only [sum_const,card_univ,smul_eq_mul] at hh'
    nlinarith
  have hp := four_mass_rpow_bound hm hs
  have hpow : (weightSize (fun v => G.degree v):ℝ)^(2/(s:ℝ)) ≤
      4*(Fintype.card V:ℝ)^(4/(s:ℝ)) := by
    rw [hdeg]; push_cast
    exact (Real.rpow_le_rpow (by positivity)
      (by nlinarith [show (0:ℝ) ≤ G.edgeFinset.card from Nat.cast_nonneg _] : (2:ℝ)*G.edgeFinset.card ≤ 4*G.edgeFinset.card)
      (by positivity)).trans hp
  have hf := mul_le_mul_of_nonneg_left hpow
    (by positivity : (0:ℝ) ≤ 512*(s:ℝ)*φ)
  have hb : 512*(s:ℝ)*(weightSize (fun v => G.degree v):ℝ)^(2/(s:ℝ))*φ ≤
      2048*(s:ℝ)*(Fintype.card V:ℝ)^(4/(s:ℝ))*φ := by nlinarith [hf]
  exact ⟨hc.1,hc.2.1,hc.2.2.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _))⟩

end LengthExpander
