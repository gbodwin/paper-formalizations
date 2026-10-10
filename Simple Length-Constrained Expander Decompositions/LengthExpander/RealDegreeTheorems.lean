import LengthExpander.RealUnionSparsity

/-! The simplified main statements extend to every real s>=2 with the
advertised n^O(1/s) form. The exact 2/s general exponent is not asserted. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem mass_rpow_real_bound {m n : ℕ} {s c : ℝ} (hm : m ≤ n^2)
    (hs : 2 ≤ s) (hc : 1 ≤ c) :
    (c*(m:ℝ))^(4/s) ≤ c^2*(n:ℝ)^(8/s) := by
  have hspos : 0 < s := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hm' : (m:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hm
  have hpow := Real.rpow_le_rpow (mul_nonneg hc0 (Nat.cast_nonneg m))
    (mul_le_mul_of_nonneg_left hm' hc0) (by positivity : (0:ℝ) ≤ 4/s)
  have he : (4:ℝ)/s ≤ 2 := (div_le_iff₀ hspos).mpr (by linarith)
  have hcPow : c^(4/s) ≤ c^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hc he
  have heq : ((n:ℝ)^2)^(4/s) = (n:ℝ)^(8/s) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    norm_num
    ring
  calc
    _ ≤ (c*(n:ℝ)^2)^(4/s) := hpow
    _ = c^(4/s)*(n:ℝ)^(8/s) := by rw [Real.mul_rpow hc0 (by positivity),heq]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcPow (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The simplified decomposition theorem for every real s>=2, with explicit
cut slack 256s*n^(8/s). The returned cut remains unscaled. -/
theorem exists_real_degree_decomposition (G : SimpleGraph V) (w : EdgeLength V)
    (h s φ : ℝ) (hh : 0 ≤ h) (hs : 2 ≤ s) (hφ : 0 ≤ φ) :
    ∃ C : EdgeLength V, (∀ e, 0 ≤ C e) ∧
      cutCost G (fun _ => 1) C ≤
        (256*s*(Fintype.card V:ℝ)^(8/s))*φ*(Fintype.card G.edgeSet:ℝ) ∧
      IsExpander G (fun _ => 1) (applyCut w C (h*s)) (fun v => G.degree v) h s φ := by
  classical
  obtain ⟨C,hC,hcost,hExp⟩ := exists_real_direct_decomposition G (fun _ => 1)
    (fun v => G.degree v) w h s φ hh hs hφ
  refine ⟨C,hC,?_,hExp⟩
  have hdeg : weightSize (fun v => G.degree v) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hm : G.edgeFinset.card ≤ (Fintype.card V)^2 := by
    have hh' : ∑ v, G.degree v ≤ ∑ _ : V, Fintype.card V :=
      sum_le_sum (fun v _ => (G.degree_lt_card_verts v).le)
    rw [G.sum_degrees_eq_twice_card_edges] at hh'
    simp only [sum_const,card_univ,smul_eq_mul] at hh'
    nlinarith
  have hp := mass_rpow_real_bound hm hs (by norm_num : (1:ℝ) ≤ 4)
  have hedge : G.edgeFinset.card = Fintype.card G.edgeSet := by simp [edgeFinset,Set.toFinset_card]
  rw [hdeg] at hcost
  push_cast at hcost
  have heq : (2:ℝ)*(2*(G.edgeFinset.card:ℝ)) = 4*G.edgeFinset.card := by ring
  rw [heq] at hcost
  rw [← hedge]
  have hp' := mul_le_mul_of_nonneg_left hp
    (by positivity : (0:ℝ) ≤ 16*s*φ*(G.edgeFinset.card:ℝ))
  norm_num at hp'
  nlinarith [hcost,hp']

theorem real_sparseSequence_union {G : SimpleGraph V} {U : Sym2 V → ℕ}
    {A : NodeWeight V} {h s φ : ℝ} {w : EdgeLength V} {Cs : List (EdgeLength V)}
    (hCs : SparseSequence G U A h s φ w Cs) (hh : 0 ≤ h) (hs : 2 ≤ s)
    (hne : Cs ≠ []) :
    SparseCut G U w A (2*h) ((s-1)/2)
      (512*s*(weightSize A:ℝ)^(4/s)*φ) (realUnionCut Cs s) := by
  have hv := sparseSequence_volume_pos hCs hne
  have hc := real_union_sparseCut_explicit G U A w h s Cs (sparseSequence_nonnegative hCs) hh hs hv
  have hv' : (0:ℝ) < sequenceVolume G A h s w Cs := by exact_mod_cast hv
  have hratio : cutCost G U (totalCut Cs)/(sequenceVolume G A h s w Cs:ℝ) ≤ φ :=
    (div_le_iff₀ hv').mpr (sparseSequence_cost_le_volume hCs)
  have hb := mul_le_mul_of_nonneg_left hratio
    (by positivity : (0:ℝ) ≤ 512*s*(weightSize A:ℝ)^(4/s))
  rw [← mul_div_assoc] at hb
  exact ⟨hc.1,hc.2.1,hc.2.2.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _))⟩

/-- The simplified union theorem for every real s>=2, with loss
2048s*n^(8/s)*phi and the original exact output parameters. -/
theorem real_degree_sparseSequence_union (G : SimpleGraph V) (w : EdgeLength V)
    (h s φ : ℝ) (Cs : List (EdgeLength V))
    (hCs : SparseSequence G (fun _ => 1) (fun v => G.degree v) h s φ w Cs)
    (hh : 0 ≤ h) (hs : 2 ≤ s) (hφ : 0 ≤ φ) (hne : Cs ≠ []) :
    SparseCut G (fun _ => 1) w (fun v => G.degree v) (2*h) ((s-1)/2)
      (2048*s*(Fintype.card V:ℝ)^(8/s)*φ) (realUnionCut Cs s) := by
  classical
  have hc := real_sparseSequence_union hCs hh hs hne
  have hdeg : weightSize (fun v => G.degree v) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hm : G.edgeFinset.card ≤ (Fintype.card V)^2 := by
    have hh' : ∑ v, G.degree v ≤ ∑ _ : V, Fintype.card V :=
      sum_le_sum (fun v _ => (G.degree_lt_card_verts v).le)
    rw [G.sum_degrees_eq_twice_card_edges] at hh'
    simp only [sum_const,card_univ,smul_eq_mul] at hh'
    nlinarith
  have hp := mass_rpow_real_bound hm hs (by norm_num : (1:ℝ) ≤ 2)
  have hpow : (weightSize (fun v => G.degree v):ℝ)^(4/s) ≤
      4*(Fintype.card V:ℝ)^(8/s) := by rw [hdeg]; push_cast; norm_num at hp; exact hp
  have hf := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ 512*s*φ)
  have hb : 512*s*(weightSize (fun v => G.degree v):ℝ)^(4/s)*φ ≤
      2048*s*(Fintype.card V:ℝ)^(8/s)*φ := by nlinarith [hf]
  exact ⟨hc.1,hc.2.1,hc.2.2.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _))⟩

end LengthExpander
