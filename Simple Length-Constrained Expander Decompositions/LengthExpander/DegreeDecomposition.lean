import LengthExpander.DirectDecomposition
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Unit capacities and the degree node weighting specialize the general
construction to the paper's simplified decomposition theorem, with an
explicit 64*s*n^(4/s) cut-slack bound. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem four_mass_rpow_bound {m n s : ℕ} (hm : m ≤ n^2) (hs : 2 ≤ s) :
    (4*(m:ℝ))^(2/(s:ℝ)) ≤ 4*(n:ℝ)^(4/(s:ℝ)) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hexp : (0 : ℝ) ≤ 2/(s:ℝ) := by positivity
  have hbase : (4:ℝ)*m ≤ 4*(n:ℝ)^2 := by exact_mod_cast Nat.mul_le_mul_left 4 hm
  have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 4*m) hbase hexp
  have he : (2:ℝ)/s ≤ 1 := (div_le_one hspos).mpr (by exact_mod_cast hs)
  have hfour : (4:ℝ)^(2/(s:ℝ)) ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) he
  have heq : ((n:ℝ)^2)^(2/(s:ℝ)) = (n:ℝ)^(4/(s:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    norm_num
    ring
  calc
    _ ≤ (4*(n:ℝ)^2)^(2/(s:ℝ)) := hpow
    _ = (4:ℝ)^(2/(s:ℝ))*(n:ℝ)^(4/(s:ℝ)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),heq]
    _ ≤ _ := mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Theorem 1.2 with explicit slack. The output expands for the actual
original degree weighting, using unit capacities and unscaled total cut.
No union-sparsity theorem or fractional witness is assumed. -/
theorem exists_degree_decomposition (G : SimpleGraph V) (w : EdgeLength V)
    (h φ : ℝ) (s : ℕ) (hh : 0 ≤ h) (hφ : 0 ≤ φ) (hs : 2 ≤ s) :
    ∃ C : EdgeLength V, (∀ e, 0 ≤ C e) ∧
      cutCost G (fun _ => 1) C ≤
        (64*(s:ℝ)*(Fintype.card V : ℝ)^(4/(s:ℝ))) * φ * (Fintype.card G.edgeSet : ℝ) ∧
      IsExpander G (fun _ => 1) (applyCut w C (h*s)) (fun v => G.degree v) h s φ := by
  classical
  obtain ⟨C,hC,hcost,hExp⟩ := exists_direct_decomposition G (fun _ => 1)
    (fun v => G.degree v) w h φ s hh hφ hs
  refine ⟨C,hC,?_,hExp⟩
  have hdeg : weightSize (fun v => G.degree v) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hm : G.edgeFinset.card ≤ (Fintype.card V)^2 := by
    have hh' : ∑ v, G.degree v ≤ ∑ _ : V, Fintype.card V :=
      sum_le_sum (fun v _ => (G.degree_lt_card_verts v).le)
    rw [G.sum_degrees_eq_twice_card_edges] at hh'
    simp only [sum_const,card_univ,smul_eq_mul] at hh'
    nlinarith
  have hp := four_mass_rpow_bound hm hs
  have hedge : G.edgeFinset.card = Fintype.card G.edgeSet := by simp [edgeFinset,Set.toFinset_card]
  rw [hdeg] at hcost
  push_cast at hcost
  have heq : (2:ℝ)*(2*(G.edgeFinset.card:ℝ)) = 4*G.edgeFinset.card := by ring
  rw [heq] at hcost
  rw [← hedge]
  have hscale : (0:ℝ) ≤ 16*(s:ℝ)*φ*(G.edgeFinset.card:ℝ) := by positivity
  have hp' := mul_le_mul_of_nonneg_left hp hscale
  nlinarith [hcost,hp']

end LengthExpander
