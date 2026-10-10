import LinearDistancePreservers.TheoremFourGeneral

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- For a fixed positive exponent gap, one fixed dimension has a positive
polynomial gain over the square of the terminal count. -/
theorem exists_dimension_gain {eps : ℝ} (heps : 0 < eps) :
    ∃ d : ℕ, 2 ≤ d ∧ ∃ η : ℝ, 0 < η ∧
      (2 : ℝ)/(d+1) +
        (((((2*d+1)*(d-1) : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ))-2)*
          ((2 : ℝ)/3-eps) = η ∧
      ((((2*d+1)*(d-1) : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ)) ≤ 2 ∧
      4*((d-1 : ℕ) : ℝ)/d ≤ 4 := by
  obtain ⟨d,hd⟩ := exists_nat_gt (max 2 (1/eps))
  have hd2 : 2 ≤ d := by
    have hh := le_max_left (2 : ℝ) (1/eps)
    have hh' : (2 : ℝ) ≤ d := by linarith
    exact_mod_cast hh'
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdε : 1 < (d : ℝ)*eps := by
    apply (div_lt_iff₀ heps).mp
    exact (le_max_right (2 : ℝ) (1/eps)).trans_lt hd
  let η := (3*(d : ℝ)*eps+eps-2/3)/((d : ℝ)*(d+1))
  have hη : 0 < η := div_pos (by nlinarith) (by positivity)
  refine ⟨d,hd2,η,hη,?_,?_,?_⟩
  · dsimp [η]
    push_cast [Nat.cast_sub hd1]
    field_simp
    ring
  · push_cast [Nat.cast_sub hd1]
    apply (div_le_iff₀ (by positivity : 0 < (d : ℝ)*(d+1))).mpr
    nlinarith
  · rw [Nat.cast_sub hd1,Nat.cast_one]
    apply (div_le_iff₀ hd0).mpr
    linarith

/-- A fixed positive polynomial power eventually dominates the square-root
exponential loss by every prescribed factor. The threshold is a natural
number and the conclusion holds at every larger natural size. -/
theorem eventually_power_loss_large {η : ℝ} (hη : 0 < η) (Q : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ (N : ℝ) ∧
      Q < (N : ℝ)^η * Real.exp (-4*Real.sqrt (Real.log N)) := by
  let q := max Q 0
  let M := max 1 ((q+5)/η)
  have hq : 0 ≤ q := le_max_right _ _
  have hM : 1 ≤ M := le_max_left _ _
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (Real.exp (M^2)+1)
  refine ⟨N₀,?_⟩
  intro N hN
  have hNN : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) < N := by linarith [Real.exp_pos (M^2)]
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog : M^2 < Real.log N := by
    have hh : Real.exp (M^2) < (N : ℝ) := by linarith
    rw [← Real.exp_log hN0] at hh
    exact Real.exp_lt_exp.mp hh
  let x := Real.sqrt (Real.log N)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x^2 = Real.log N := Real.sq_sqrt (Real.log_nonneg hN1.le)
  have hxM : M ≤ x := by nlinarith
  have hx1 : 1 ≤ x := hM.trans hxM
  have hqx : q+5 ≤ η*x := by
    have hh : (q+5)/η ≤ x := (le_max_right 1 _).trans hxM
    simpa only [mul_comm] using (div_le_iff₀ hη).mp hh
  have hgrowth : q+1 ≤ η*Real.log N-4*x := by
    have hh := mul_le_mul_of_nonneg_right hqx hx0
    have hh' := mul_le_mul_of_nonneg_left hx1 (by positivity : 0 ≤ q+1)
    rw [← hx2]
    nlinarith
  have hexp : Q < Real.exp (η*Real.log N-4*x) := by
    have hh := Real.add_one_le_exp (η*Real.log N-4*x)
    have hQ : Q ≤ q := le_max_left _ _
    linarith
  refine ⟨hN1.le,?_⟩
  rw [Real.rpow_def_of_pos hN0,← Real.exp_add]
  convert hexp using 1 <;> congr 1 <;> dsimp [x] <;> ring

/-- A terminal upper bound converts the literal two-parameter rate into a
polynomial gain times the square of the terminal count. -/
theorem terminal_rate_lower {N T α β a η : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hcap : T ≤ N^a) (hβ : β ≤ 2)
    (hη : α+(β-2)*a = η) :
    T^2*N^η ≤ N^α*T^β := by
  have hp := Real.rpow_le_rpow_of_nonpos hT hcap (sub_nonpos.mpr hβ)
  have hn : N^α*(N^a)^(β-2) = N^η := by
    rw [← Real.rpow_mul hN.le,← Real.rpow_add hN]
    congr 1
    linarith [hη]
  have ht : T^2*T^(β-2) = T^β := by
    rw [← Real.rpow_two,← Real.rpow_add hT]
    congr 1
    ring
  calc
    _ = T^2*(N^α*(N^a)^(β-2)) := by rw [hn]
    _ ≤ T^2*(N^α*T^(β-2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hN.le _))
        (sq_nonneg T)
    _ = _ := by rw [← mul_assoc,mul_right_comm (T^2),ht]; ring

/-- A finite uniform version of the valid fixed-gap superquadratic corollary.
The positive exponent gap and desired factor are fixed before the size
threshold; one dimension depends only on the gap. This does not assert the
paper's sharper square-root-exponential near-threshold range. -/
theorem superquadratic_fixed_gap {eps : ℝ} (heps : 0 < eps) (B : ℝ) :
    ∃ N₀ : ℕ, ∀ N T : ℕ, N₀ ≤ N → 2 ≤ T →
      (T : ℝ) ≤ (N : ℝ)^((2 : ℝ)/3-eps) →
      ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
        ∀ H : SimpleGraph (Fin N), H ≤ G →
          (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
          B*(T : ℝ)^2 < (H.edgeFinset.card : ℝ) := by
  obtain ⟨d,hd,η,hη,hgain,hβ,hc⟩ := exists_dimension_gain heps
  obtain ⟨K,hK,hgraph⟩ := displayed_lower_bound d hd
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨N₀,hN₀⟩ := eventually_power_loss_large hη (B*K)
  refine ⟨N₀,?_⟩
  intro N T hN hT hcap
  obtain ⟨hN1,hlarge⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hTN : T ≤ N := by
    have hh := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (2 : ℝ)/3-eps ≤ 1)
    rw [Real.rpow_one] at hh
    exact_mod_cast hcap.trans hh
  obtain ⟨G,S,hS,hbound⟩ := hgraph N T hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hHG hpres
  have hr := terminal_rate_lower hN0 hT0 hcap hβ hgain
  have hloss : Real.exp (-4*Real.sqrt (Real.log N)) ≤
      Real.exp (-(4*((d-1 : ℕ) : ℝ)/d)*Real.sqrt (Real.log N)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (Real.log (N : ℝ)))
    linarith
  have hrate := mul_le_mul hr hloss (Real.exp_nonneg _)
    (mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hT0.le _))
  have hstrict := mul_lt_mul_of_pos_left hlarge (sq_pos_of_pos hT0)
  have hfinal := hrate.trans (hbound H hHG hpres)
  apply (mul_lt_mul_iff_right₀ hKR).mp
  calc
    (K : ℝ)*(B*(T : ℝ)^2) = (T : ℝ)^2*(B*K) := by ring
    _ < (T : ℝ)^2*((N : ℝ)^η*Real.exp (-4*Real.sqrt (Real.log N))) := hstrict
    _ = ((T : ℝ)^2*(N : ℝ)^η)*Real.exp (-4*Real.sqrt (Real.log N)) := by ring
    _ ≤ _ := hfinal

end LinearDistancePreservers.TheoremFourGeneral
