import OnlineReachabilityPreservers.SteinerAssembly

/-! Integer parameters and exponent accounting for the Section 5 composition. -/

namespace OnlineReachabilityPreservers

open Finset

private def fifthRootFloor (value cap : ℕ) : ℕ :=
  Nat.findGreatest (fun k => k^5 ≤ value) cap

private theorem fifthRootFloor_bounds {value cap : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (capBound : x ≤ cap) (power : x^5 = value) :
    (fifthRootFloor value cap:ℝ) ≤ x ∧ x < (fifthRootFloor value cap:ℝ)+1 := by
  let k := fifthRootFloor value cap
  have hk : k^5 ≤ value := Nat.findGreatest_spec (P := fun j => j^5 ≤ value) (m := 0)
    (Nat.zero_le cap) (by simp)
  have hr : (k:ℝ)^5 ≤ x^5 := by
    rw [power]
    exact_mod_cast hk
  have lower := (pow_le_pow_iff_left₀ (show 0 ≤ (k:ℝ) by positivity) hx
    (by decide : (5:ℕ) ≠ 0)).mp hr
  refine ⟨lower,?_⟩
  by_contra! h
  have inCap : k+1 ≤ cap := by exact_mod_cast h.trans capBound
  have test : (k+1)^5 ≤ value := by
    have q := pow_le_pow_left₀ (show 0 ≤ (k:ℝ)+1 by positivity) h 5
    rw [power] at q
    exact_mod_cast q
  have bigger : k+1 ≤ k := Nat.le_findGreatest (P := fun j => j^5 ≤ value) inCap test
  omega

private theorem real_fifth_power {n : ℝ} (hn : 0 ≤ n) (j : ℕ) :
    (n^((j:ℝ)/5))^5 = n^j := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hn]
  have eq : ((j:ℝ)/5)*((5:ℕ):ℝ) = j := by push_cast; ring
  rw [eq,Real.rpow_natCast]

/-- Thickness floor corresponding to n^(3/5). -/
def steinerThinThreshold (n : ℕ) : ℕ := fifthRootFloor (n^3) n

/-- First integer above n^(6/5), used for the early phase. -/
def steinerEarlyCutoff (n : ℕ) : ℕ := fifthRootFloor (n^6) (n^2)+1

theorem steinerThinThreshold_bounds {n : ℕ} (hn : 0 < n) :
    (steinerThinThreshold n:ℝ) ≤ (n:ℝ)^(3/5:ℝ) ∧
      (n:ℝ)^(3/5:ℝ) < (steinerThinThreshold n:ℝ)+1 := by
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have cap : (n:ℝ)^(3/5:ℝ) ≤ n := Real.rpow_le_self_of_one_le n1 (by norm_num)
  have eq : ((n:ℝ)^(3/5:ℝ))^5 = ((n^3:ℕ):ℝ) := by
    push_cast
    simpa using real_fifth_power (n := (n:ℝ)) (by positivity) 3
  exact fifthRootFloor_bounds (by positivity) cap eq

theorem steinerEarlyCutoff_bounds {n : ℕ} (hn : 0 < n) :
    (n:ℝ)^(6/5:ℝ) ≤ steinerEarlyCutoff n ∧
      (steinerEarlyCutoff n:ℝ) ≤ 2*(n:ℝ)^(6/5:ℝ) := by
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have cap : (n:ℝ)^(6/5:ℝ) ≤ ((n^2:ℕ):ℝ) := by
    push_cast
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
  have eq : ((n:ℝ)^(6/5:ℝ))^5 = ((n^6:ℕ):ℝ) := by
    push_cast
    simpa using real_fifth_power (n := (n:ℝ)) (by positivity) 6
  obtain ⟨lo,hi⟩ := fifthRootFloor_bounds (by positivity) cap eq
  have x1 : 1 ≤ (n:ℝ)^(6/5:ℝ) := Real.one_le_rpow n1 (by norm_num)
  push_cast [steinerEarlyCutoff]
  exact ⟨hi.le,by linarith only [lo,x1]⟩

theorem nat_log2_le_log {n : ℕ} (hn : 0 < n) :
    (n.log2:ℝ) ≤ Real.log (n:ℝ)/Real.log 2 := by
  have logTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ logTwo).mpr
  rw [← Real.log_pow]
  have bound : (2:ℝ)^n.log2 ≤ (n:ℝ) := by
    exact_mod_cast ((Nat.le_log2 hn.ne').mp (le_rfl : n.log2≤n.log2))
  exact Real.log_le_log (by positivity) bound

private theorem edge_log2_le {m n : ℕ} (hn : 0 < n) (hm : m ≤ n^2) :
    (m.log2:ℝ) ≤ 2*Real.log (n:ℝ)/Real.log 2 := by
  have logTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases m0 : m=0
  · subst m
    norm_num
    have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have := Real.log_nonneg n1
    positivity
  have l := nat_log2_le_log (Nat.pos_of_ne_zero m0)
  have b : (m:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hm
  have ll := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero m0)) b
  rw [Real.log_pow] at ll
  push_cast at ll
  exact l.trans (div_le_div_of_nonneg_right ll logTwo.le)

theorem log_power_absorption {ε : ℝ} (he : 0 < ε) (k : ℕ) :
    ∃ C ≥ 1, ∀ {x : ℝ}, 1 ≤ x → (1+Real.log x)^k ≤ C*x^ε := by
  let δ := ε/((k:ℝ)+1)
  have hd : 0 < δ := by dsimp [δ]; positivity
  let C := (1+1/δ)^k
  have c1 : 1 ≤ C := by
    dsimp [C]
    exact one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  refine ⟨C,c1,?_⟩
  intro x hx
  have xp := zero_lt_one.trans_le hx
  have x1 : 1 ≤ x^δ := Real.one_le_rpow hx hd.le
  have lp := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos xp δ)
  rw [Real.log_rpow xp] at lp
  have div : Real.log x ≤ x^δ/δ := (le_div_iff₀ hd).mpr (by linarith only [lp])
  have mul : 1+Real.log x ≤ (1+1/δ)*x^δ := by
    calc
      _ ≤ x^δ+x^δ/δ := add_le_add x1 div
      _ = _ := by ring
  have ex : δ*(k:ℝ) ≤ ε := by
    have h : δ*((k:ℝ)+1) = ε := by dsimp [δ]; field_simp
    linarith only [h,hd]
  calc
    _ ≤ ((1+1/δ)*x^δ)^k := pow_le_pow_left₀ (by have := Real.log_nonneg hx; positivity) mul _
    _ = C*x^(δ*(k:ℝ)) := by
      dsimp [C]
      have ep : (x^δ)^k = x^(δ*(k:ℝ)) := by
        rw [← Real.rpow_natCast (x^δ) k,← Real.rpow_mul xp.le]
      rw [mul_pow,ep]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ex) (by linarith)

private theorem lateCoefficient_polylog {n m τ : ℕ} (hn : 0 < n) (hm : m ≤ n^2)
    (thin : (τ:ℝ) ≤ (n:ℝ)^(3/5:ℝ)) :
    let A : ℝ := 1+4*(1/Real.log 2+1)
    let B : ℝ := 2/Real.log 2+2
    (6+4*((2+(2:ℝ))*Real.log (n:ℝ)+1))*(n:ℝ)^(3/5:ℝ)+
      ((thinRoundingFactor n τ:ℝ)*((m.log2:ℝ)+2)+1) ≤
      (A*B+17)*(1+Real.log (n:ℝ))^2*(n:ℝ)^(3/5:ℝ) := by
  let A : ℝ := 1+4*(1/Real.log 2+1)
  let B : ℝ := 2/Real.log 2+2
  let Y := 1+Real.log (n:ℝ)
  let N := (n:ℝ)^(3/5:ℝ)
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg n1
  have Y1 : 1 ≤ Y := by dsimp [Y]; linarith
  have N1 : 1 ≤ N := Real.one_le_rpow n1 (by norm_num)
  have logTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have a0 : 0 ≤ A := by dsimp [A]; positivity
  have b0 : 0 ≤ B := by dsimp [B]; positivity
  have U : (n.log2:ℝ)+1 ≤ (1/Real.log 2+1)*Y := by
    have h := nat_log2_le_log hn
    dsimp [Y]
    have e : (1/Real.log 2+1)*(1+Real.log (n:ℝ)) =
        Real.log (n:ℝ)/Real.log 2+1+1/Real.log 2+Real.log (n:ℝ) := by ring
    rw [e]
    linarith only [h,hlog,show (0:ℝ) ≤ 1/Real.log 2 by positivity]
  have V : (m.log2:ℝ)+2 ≤ B*Y := by
    have h := edge_log2_le hn hm
    dsimp [B,Y]
    have e : (2/Real.log 2+2)*(1+Real.log (n:ℝ)) =
        2*Real.log (n:ℝ)/Real.log 2+2+2/Real.log 2+2*Real.log (n:ℝ) := by ring
    rw [e]
    linarith only [h,hlog,show (0:ℝ) ≤ 2/Real.log 2 by positivity]
  have L : (thinRoundingFactor n τ:ℝ) ≤ A*Y*N := by
    have y0 : 0 ≤ Y := by linarith
    have n0 : 0 ≤ N := by linarith
    have C0 : 0 ≤ (1/Real.log 2+1)*Y := mul_nonneg (by positivity) y0
    have yN : N ≤ Y*N := by simpa using mul_le_mul_of_nonneg_right Y1 n0
    have extra : (1/Real.log 2+1)*Y ≤ (1/Real.log 2+1)*Y*N := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left N1 C0
    push_cast [thinRoundingFactor]
    change (τ:ℝ)+4*((n.log2:ℝ)+1) ≤ A*Y*N
    calc
      _ ≤ Y*N+4*((1/Real.log 2+1)*Y*N) :=
        add_le_add (thin.trans yN) (mul_le_mul_of_nonneg_left (U.trans extra) (by norm_num))
      _ = _ := by dsimp [A]; ring
  have Y0 : 0 ≤ Y := zero_le_one.trans Y1
  have N0 : 0 ≤ N := zero_le_one.trans N1
  have S1 : 1 ≤ Y^2*N := by
    simpa using mul_le_mul (one_le_pow₀ Y1 (n := 2)) N1 (by norm_num : (0:ℝ) ≤ 1)
      (sq_nonneg Y)
  have thinTerm : (thinRoundingFactor n τ:ℝ)*((m.log2:ℝ)+2)+1 ≤ (A*B+1)*Y^2*N := by
    calc
      _ ≤ (A*Y*N)*(B*Y)+Y^2*N := add_le_add
        (mul_le_mul L V (by positivity) (mul_nonneg (mul_nonneg a0 Y0) N0)) S1
      _ = _ := by ring
  have hub : (6+4*((2+(2:ℝ))*Real.log (n:ℝ)+1))*N ≤ 16*Y^2*N := by
    have ysq : Y ≤ Y^2 := by
      rw [pow_two]
      exact (mul_one Y).symm.le.trans (mul_le_mul_of_nonneg_left Y1 (by linarith))
    have term : 6+4*((2+(2:ℝ))*Real.log (n:ℝ)+1) ≤ 16*Y := by dsimp [Y]; linarith
    exact mul_le_mul_of_nonneg_right (term.trans (mul_le_mul_of_nonneg_left ysq (by norm_num)))
      (by linarith)
  calc
    _ ≤ 16*Y^2*N+(A*B+1)*Y^2*N := add_le_add hub thinTerm
    _ = _ := by ring

universe u

private theorem lateRate_absorb {ε : ℝ} (he : 0 < ε) (A : ℝ) (A0 : 0 ≤ A) :
    ∃ K > 0, ∀ {n m z : ℕ} (_hn : 0 < n) (_hm : m ≤ n ^ 2) (_hz : 0 < z) {coefficient : ℝ},
      coefficient ≤ A * (1 + Real.log (n : ℝ)) ^ 2 * (n : ℝ) ^ (3/5 : ℝ) →
      coefficient * z + (m : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) ≤ K * (n : ℝ) ^ (3/5 + ε) * z := by
  obtain ⟨C, hC, logs⟩ := log_power_absorption he 2
  have C0 := zero_le_one.trans hC
  refine ⟨A * C + 1, by positivity, ?_⟩
  intro n m z hn hm hz coefficient coeff
  let Y := 1 + Real.log (n : ℝ)
  let X := (n : ℝ) ^ (3/5 + ε)
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have n0 := zero_lt_one.trans_le n1
  have growth : A * Y^2 * (n : ℝ) ^ (3/5 : ℝ) ≤ A * C * X := by
    calc
      _ ≤ A * (C * (n : ℝ) ^ ε) * (n : ℝ) ^ (3/5 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (logs n1) A0) (by positivity)
      _ = _ := by
        dsimp [X]
        rw [Real.rpow_add n0]
        ring
  have tail : (m : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg n0.le, Real.rpow_two]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by positivity)).trans_eq
      (mul_inv_cancel₀ (by positivity))
  have X1 : 1 ≤ X := Real.one_le_rpow n1 (by linarith)
  have z1 : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have tail' := tail.trans (one_le_mul_of_one_le_of_one_le X1 z1)
  have costs := mul_le_mul_of_nonneg_right (coeff.trans growth) (show 0 ≤ (z : ℝ) by positivity)
  change _ ≤ (A * C + 1) * X * z
  linarith only [costs, tail']

private theorem integerLateCoefficient_polylog {n m τ : ℕ} (hn : 0 < n) (hm : m ≤ n^2)
    (thin : (τ : ℝ) ≤ (n : ℝ) ^ (3/5 : ℝ)) :
    let A : ℝ := 1+4*(1/Real.log 2+1)
    let B : ℝ := 2/Real.log 2+2
    let C : ℝ := 4*(1/Real.log 2+1)+1
    (6+4*(4*((n.log2 : ℝ)+1)+1))*(n : ℝ)^(3/5 : ℝ)+
      ((thinRoundingFactor n τ : ℝ)*((m.log2 : ℝ)+2)+1) ≤
      (A*B+17+4*C)*(1+Real.log (n : ℝ))^2*(n : ℝ)^(3/5 : ℝ) := by
  let A : ℝ := 1+4*(1/Real.log 2+1)
  let B : ℝ := 2/Real.log 2+2
  let C : ℝ := 4*(1/Real.log 2+1)+1
  let Y := 1 + Real.log (n : ℝ)
  let X := (n : ℝ) ^ (3/5 : ℝ)
  let R := ((thinRoundingFactor n τ : ℝ) * ((m.log2 : ℝ) + 2) + 1)
  let Ck := 4*((n.log2 : ℝ)+1)+1
  let C0 := 4*Real.log (n : ℝ)+1
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have log0 := Real.log_nonneg n1
  have logTwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have Y1 : 1 ≤ Y := le_add_of_nonneg_right log0
  have Y0 := zero_le_one.trans Y1
  have X0 : 0 ≤ X := by dsimp [X]; positivity
  have c0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have logBound : (n.log2 : ℝ) + 1 ≤ (1 / Real.log 2 + 1) * Y := by
    calc
      _ ≤ Real.log (n : ℝ) / Real.log 2 + 1 := add_le_add (nat_log2_le_log hn) le_rfl
      _ ≤ Real.log (n : ℝ) / Real.log 2 + 1 + (1 / Real.log 2 + Real.log (n : ℝ)) :=
        le_add_of_nonneg_right (by positivity)
      _ = _ := by dsimp only [Y]; ring
  have cBound : Ck ≤ C * Y := by
    calc
      _ ≤ 4 * ((1 / Real.log 2 + 1) * Y) + Y :=
        add_le_add (mul_le_mul_of_nonneg_left logBound (by norm_num)) Y1
      _ = _ := by dsimp [C]; ring
  have Cpos : 0 ≤ C := by dsimp [C]; positivity
  have powY : Y ≤ Y ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left Y1 Y0]
  have orig : (6+4*C0)*X + R ≤ (A*B+17)*Y^2*X := by
    simpa only [C0, R, X, Y, A, B, show (2 : ℝ) + 2 = 4 by norm_num]
      using lateCoefficient_polylog hn hm thin
  have extra : 4*Ck*X ≤ (4*C)*(Y^2*X) := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (cBound.trans (mul_le_mul_of_nonneg_left powY Cpos)) (by norm_num : (0 : ℝ) ≤ 4)) X0
    linarith only [h]
  change (6+4*Ck)*X + R ≤ (A*B+17+4*C)*Y^2*X
  calc
    _ ≤ ((6+4*C0)*X + R) + 4*Ck*X := by
      nlinarith only [mul_nonneg c0 X0]
    _ ≤ (A*B+17)*Y^2*X + (4*C)*(Y^2*X) := add_le_add orig extra
    _ = _ := by ring

/-- The summed expected late-phase contribution of Section 5, with the early
budget still supplied separately. -/
theorem assembledSteiner_late_rate_of_opt {ε : ℝ} (he : 0 < ε) :
    ∃ K > 0, ∀ (V : Type u) [LinearOrder V] [Fintype V] {G Z : Arcs V}
      (early : EarlySteinerRule G) (T : ℕ) (D : List (V × V)) (earlyCost : ℝ),
      0 ≤ earlyCost → 0 < Fintype.card V → 0 < Z.card → Z ⊆ G →
      (∀ d ∈ D, Reach Z d.1 d.2) →
      (∀ S : Finset V, (steinerPhaseTraces early T S D).hits ≠ [] →
        steinerEarlyCutoff (Fintype.card V) ≤ Z.card ^ 2) →
      (∀ S : Finset V, ((early.run (steinerPhaseTraces early T S D).early).card:ℝ) ≤
          earlyCost) →
      assembledSteinerMean early T
        (steinerThinThreshold (Fintype.card V)) 2 D ≤
        earlyCost+K*(Fintype.card V:ℝ)^(3/5+ε)*Z.card := by
  let A : ℝ := 1+4*(1/Real.log 2+1)
  let B : ℝ := 2/Real.log 2+2
  have logTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K, Kpos, absorb⟩ := lateRate_absorb he (A*B+17) (by dsimp [A, B]; positivity)
  refine ⟨K, Kpos, ?_⟩
  intro V _ _ G Z early T D earlyCost E0 hn hZ sub feasible optLower earlyBound
  let n := Fintype.card V
  have cap : G.card ≤ n^2 := by simpa [n,Fintype.card_prod,pow_two] using card_le_univ G
  have bound := assembledSteiner_mean_transfer_of_opt (power := 2) early (by norm_num) E0 hn
    (steinerEarlyCutoff_bounds hn).1 (steinerThinThreshold_bounds hn).2.le D sub feasible optLower earlyBound
  have coeff := lateCoefficient_polylog hn cap (steinerThinThreshold_bounds hn).1
  exact bound.trans (by
    have h := absorb hn cap hZ coeff
    linarith only [h])

theorem assembledSteiner_late_rate_of_integer_draws {ε : ℝ} (he : 0 < ε) :
    ∃ K > 0, ∀ (V : Type u) [LinearOrder V] [Fintype V] {G Z : Arcs V}
      (early : EarlySteinerRule G) (T : ℕ) (D : List (V × V)) (earlyCost : ℝ),
      0 ≤ earlyCost → 0 < Fintype.card V → 0 < Z.card → Z ⊆ G →
      (∀ d ∈ D, Reach Z d.1 d.2) →
      (∀ S : Finset V, (steinerPhaseTraces early T S D).hits ≠ [] →
        steinerEarlyCutoff (Fintype.card V) ≤ Z.card ^ 2) →
      (∀ S : Finset V, ((early.run (steinerPhaseTraces early T S D).early).card:ℝ) ≤
          earlyCost) →
      assembledSteinerMeanOfDrawCount early T
        (steinerThinThreshold (Fintype.card V))
        (steinerHubDraws (Fintype.card V) (steinerThinThreshold (Fintype.card V))) D ≤
        earlyCost+K*(Fintype.card V:ℝ)^(3/5+ε)*Z.card := by
  let A : ℝ := 1+4*(1/Real.log 2+1)
  let B : ℝ := 2/Real.log 2+2
  let C : ℝ := 4*(1/Real.log 2+1)+1
  have logTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K, Kpos, absorb⟩ := lateRate_absorb he (A*B+17+4*C) (by dsimp [A, B, C]; positivity)
  refine ⟨K, Kpos, ?_⟩
  intro V _ _ G Z early T D earlyCost E0 hn hZ sub feasible optLower earlyBound
  let n := Fintype.card V
  let τ := steinerThinThreshold n
  have cap : G.card ≤ n^2 := by simpa [n,Fintype.card_prod,pow_two] using card_le_univ G
  have size := steinerHubDraws_balanced hn (steinerThinThreshold_bounds hn).2.le
  have bound := assembledSteiner_mean_transfer_of_draw_count early (by positivity) E0 hn
    (steinerEarlyCutoff_bounds hn).1 size (steinerHubDraws_probability G τ hn) D sub feasible optLower earlyBound
  have coeff := integerLateCoefficient_polylog hn cap (steinerThinThreshold_bounds hn).1
  refine bound.trans ?_
  have h := absorb hn cap hZ coeff
  linarith only [h]

theorem assembledSteiner_late_rate {ε : ℝ} (he : 0 < ε) :
    ∃ K > 0, ∀ (V : Type u) [LinearOrder V] [Fintype V] {G Z : Arcs V}
      (early : EarlySteinerRule G) (D : List (V × V)) (earlyCost : ℝ),
      0 ≤ earlyCost → 0 < Fintype.card V → 0 < Z.card → Z ⊆ G →
      (∀ d ∈ D, Reach Z d.1 d.2) →
      (∀ S : Finset V,
        ((early.run (steinerPhaseTraces early (steinerEarlyCutoff (Fintype.card V)) S D).early).card:ℝ) ≤
          earlyCost) →
      assembledSteinerMean early (steinerEarlyCutoff (Fintype.card V))
        (steinerThinThreshold (Fintype.card V)) 2 D ≤
        earlyCost+K*(Fintype.card V:ℝ)^(3/5+ε)*Z.card := by
  obtain ⟨K, pos, bound⟩ := assembledSteiner_late_rate_of_opt.{u} he
  refine ⟨K, pos, ?_⟩
  intro V _ _ G Z early D earlyCost E0 hn hZ sub feasible earlyBound
  exact bound V early _ D earlyCost E0 hn hZ sub feasible
    (fun S => phaseCutoff_le_opt_of_hits early _ S D sub feasible) earlyBound

end OnlineReachabilityPreservers
