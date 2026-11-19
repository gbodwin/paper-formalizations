import OnlineReachabilityPreservers.BranchWindow
import OnlineReachabilityPreservers.OnlineArithmetic
import OnlineReachabilityPreservers.OffBaseAverage
import OnlineReachabilityPreservers.Regularization

/-! The Appendix A bootstrap on systems with a common vertex order. -/

namespace OnlineReachabilityPreservers

open Finset

universe u v

/-- A uniform incidence bound for finite common-order half-4-bridge-free
systems. The same bound applies to their induced subfamilies. -/
def OnlineIncidenceBound (a b C : ℝ) : Prop :=
  ∀ (V : Type u) (I : Type v) [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
    (paths : I → Finset V), HalfBridgeFree (PathBefore paths) 4 →
    (∑ i, ((paths i).card : ℝ)) ≤ C*onlineRate a b (Fintype.card V) (Fintype.card I)

set_option maxHeartbeats 800000 in
private theorem online_regular_step {a b C : ℝ} (hC : 1 ≤ C) (ha₀ : 29/40 ≤ a)
    (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 701/1000)
    (hβ₀ : 2/3 ≤ onlineExponentStep b) (hβ₁ : onlineExponentStep b ≤ 701/1000)
    (prior : OnlineIncidenceBound.{u,v} a b C) :
    ∃ A > 0, ∀ {V : Type u} {I : Type v} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → Finset V} (_ : HalfBridgeFree (PathBefore paths) 4) (L D : ℕ),
      0 < Fintype.card V → 0 < Fintype.card I →
      let M := ∑ i, (paths i).card
      16*Fintype.card V < M → 8*Fintype.card I < M →
      L*Fintype.card I ≤ 4*M → D*Fintype.card V ≤ 4*M →
      (∀ i, (paths i).card ≤ L) → (∀ v, (occurrences paths v).card ≤ D) →
      (M:ℝ) ≤ A*onlineRate ((2+b)/(3+b)) (onlineExponentStep b) (Fintype.card V) (Fintype.card I) := by
  let α := (2+b)/(3+b)
  let β := onlineExponentStep b
  have βhi : β ≤ 3/4 := by linarith
  have bpos : 0 < b := by linarith
  have bwide : b ≤ 3/4 := by linarith
  have αhi : α ≤ 3/4 := (div_le_iff₀ (by linarith : 0 < 3+b)).mpr (by linarith)
  obtain ⟨X, hX, Y, hY, sampled⟩ := lemma36_acyclic_expectation hC
    (show 7/10 ≤ a by linarith) ha₁ hb₀ bwide
  obtain ⟨K, hK, upper⟩ := lemma37_substitute_window (a := a) hX hY hb₀ bwide
  let W : ℝ := 40*2048^2
  have hpW : 0 < W := by norm_num [W]
  obtain ⟨N, hN⟩ := exists_nat_ge (W*(Y+1))
  let cN := max 40960 N
  let c : ℝ := cN
  have c40960 : 40960 ≤ cN := le_max_left _ _
  have cpos : 0 < c := Nat.cast_pos.mpr ((by decide : 0 < 40960).trans_le c40960)
  have cLarge : W*(Y+1) ≤ c := hN.trans (Nat.cast_le.mpr (le_max_right _ _))
  obtain ⟨A, hA, rearrange⟩ := lemma37_comparison cpos hK ha₀ ha₁ hb₀ hb₁ hβ₀ hβ₁
  let U := (3*c)^(1/4:ℝ)
  have hU : 0 < U := by dsimp only [U]; positivity
  let B := 1+A+U
  have hB : 0 < B := by dsimp only [B]; linarith only [hA,hU]
  have uB : U ≤ B := by dsimp only [B]; linarith only [hA]
  have aB : A ≤ B := by dsimp only [B]; linarith only [hU]
  refine ⟨B,hB,?_⟩
  intro V I _ _ _ _ paths free L D hn hp
  dsimp only
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  intro dense long avgL avgD lengths degree
  change 16*n < M at dense
  change 8*p < M at long
  have hm : 0 < M := by omega
  have npos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from hn)
  have ppos : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have mpos : (0:ℝ) < M := Nat.cast_pos.mpr hm
  let ℓ : ℝ := (M:ℝ)/p
  let d : ℝ := (M:ℝ)/n
  let t := c*p/(ℓ*d^2)
  have lpos : 0 < ℓ := div_pos mpos ppos
  have dpos : 0 < d := div_pos mpos npos
  have tpos : 0 < t := div_pos (mul_pos cpos ppos) (mul_pos lpos (sq_pos_of_pos dpos))
  let h := (cN*n^2*p^2)/M^3+1
  have hpos : 0 < h := Nat.succ_pos _
  have cube : M^3 ≤ 2048*(n*p)^2 :=
    ((lemma27_acyclic paths free).resolve_left (not_le_of_gt dense)).resolve_left (not_le_of_gt long)
  obtain ⟨cap, height⟩ := rounded_branch_window hn hp hm
    ((by decide : 2048 ≤ 40960).trans c40960) cube
  change (h:ℝ)+1 ≤ 3*t at cap
  change cN*n^2*p^2 ≤ (h+1)*M^3 at height
  let F := onlineRate α β (n:ℝ) (p:ℝ)
  have Fm : (n:ℝ) ≤ F := le_max_left _ _
  have Fp : 0 ≤ F := npos.le.trans Fm
  have leading : (n:ℝ)^α*(p:ℝ)^(2-2*α) ≤ F := (le_max_left _ _).trans (le_max_right _ _)
  have mixed : (n:ℝ)^(2-2*β)*(p:ℝ)^β ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have pairs : (p:ℝ) ≤ F := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  change (M:ℝ) ≤ B*F
  by_cases length_window : h*p ≤ M
  swap
  · have hout : ℓ ≤ 3*t := by
      have nat : M ≤ h*p := le_of_not_ge length_window
      have real : (M:ℝ) ≤ (h:ℝ)*p := by exact_mod_cast nat
      exact ((div_le_iff₀ ppos).mpr real).trans (by linarith only [cap])
    have m := mass_large_length_window mpos npos ppos cpos hout
    have branch : (n:ℝ)^(1/2:ℝ)*(p:ℝ)^(3/4:ℝ) ≤ F := by
      have h := (mixed_term_le βhi (show (3/4:ℝ) ≤ 1 by norm_num) npos ppos).trans (max_le mixed pairs)
      simpa only [show (2:ℝ)-2*(3/4)=1/2 by norm_num] using h
    exact (m.trans_eq (mul_assoc _ _ _)).trans
      ((mul_le_mul_of_nonneg_left branch hU.le).trans (mul_le_mul_of_nonneg_right uB Fp))
  by_cases degree_window : h*n ≤ M
  swap
  · have hout : d ≤ 3*t := by
      have nat : M ≤ h*n := le_of_not_ge degree_window
      have real : (M:ℝ) ≤ (h:ℝ)*n := by exact_mod_cast nat
      exact ((div_le_iff₀ npos).mpr real).trans (by linarith only [cap])
    have m := mass_large_degree_window mpos npos ppos cpos hout
    have branch := (square_root_rate_le npos ppos.le αhi).trans (max_le Fm leading)
    exact (m.trans_eq (mul_assoc _ _ _)).trans
      ((mul_le_mul_of_nonneg_left branch hU.le).trans (mul_le_mul_of_nonneg_right uB Fp))
  have length_total : M ≤ p*L := calc
    _ ≤ ∑ _ : I, L := sum_le_sum (fun i _ => lengths i)
    _ = _ := by simp [p]
  have degree_total : M ≤ n*D := by
    change (∑ i, (paths i).card) ≤ n*D
    rw [← sum_occurrences]
    calc
      _ ≤ ∑ _ : V, D := sum_le_sum (fun v _ => degree v)
      _ = _ := by simp [n]
  have hl : h ≤ L := Nat.le_of_mul_le_mul_left ((Nat.mul_comm p h).le.trans (length_window.trans length_total)) hp
  have hd : h ≤ D := Nat.le_of_mul_le_mul_left ((Nat.mul_comm n h).le.trans (degree_window.trans degree_total)) hn
  have input : InducedSizeBound paths C a b := by
    intro S J free'
    have h := prior S J (inducedPaths paths S J) free'
    simpa only [Fintype.card_coe, onlineRate] using h
  have Hsmall : 40960*n^2*p^2 ≤ (h+1)*M^3 :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ c40960)).trans height
  have count := lemma28_scaled_mean_lower free L h lengths hn hp dense.le long.le avgL length_window Hsmall
  let Qn := ∑ base : I, (branchTuples paths base h).card
  let Q := uniformMean (fun base => ((branchTuples paths base h).card:ℝ))
  have hQ := branch_window_mean_lower (Q := Qn) hn hp height count
  have castQ : (Qn:ℝ) = ∑ base : I, ((branchTuples paths base h).card:ℝ) := Nat.cast_sum _ _
  change c*(ℓ^2*d^2) ≤ W*((Qn:ℝ)/(p:ℝ)) at hQ
  rw [castQ] at hQ
  have qLower : (Y+1)*(ℓ^2*d^2) ≤ Q := by
    apply le_of_mul_le_mul_left (a := W) _ hpW
    calc
      _ = (W*(Y+1))*(ℓ^2*d^2) := by ring
      _ ≤ c*(ℓ^2*d^2) := mul_le_mul_of_nonneg_right cLarge (mul_nonneg (sq_nonneg ℓ) (sq_nonneg d))
      _ ≤ _ := hQ
  have sampled_bound := sampled free L D h hn hp hpos hl hd lengths degree input hm avgL avgD
  have cap' : (h:ℝ) ≤ 3*t := by linarith only [cap]
  have upperQ := sampled_bound.trans (upper lpos dpos (Nat.cast_nonneg h) tpos cap')
  let S := ℓ^2*d*t^(1/b) +
    ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*t^((2*b+1)/(2*b)) +
    ℓ^(1/b)*d^2*t^((4*b-2*b^2-1)/b^2) + ℓ^(3/2:ℝ)*d^2*t^(5/4:ℝ)
  change Q ≤ Y*(ℓ^2*d^2)+K*S at upperQ
  have comparison : ℓ^2*d^2 ≤ K*S := by nlinarith only [qLower,upperQ]
  exact (rearrange mpos n1 ppos comparison).trans (mul_le_mul_of_nonneg_right aB Fp)


private theorem onlineRate_mono {a b n n' p p' : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hb : 0 ≤ b) (hb' : b ≤ 1) (hn : 0 ≤ n) (hp : 0 ≤ p) (hn' : n ≤ n') (hp' : p ≤ p') :
    onlineRate a b n p ≤ onlineRate a b n' p' := by
  have pn := hn.trans hn'
  have pp := hp.trans hp'
  have e₁ : 0 ≤ 2-2*a := by linarith
  have e₂ : 0 ≤ 2-2*b := by linarith
  unfold onlineRate
  gcongr

private theorem onlineRate_double {a b n p : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hn : 0 ≤ n) (hp : 0 ≤ p) :
    onlineRate a b (2*n) (2*p) ≤ 4*onlineRate a b n p := by
  have shift {f g : ℝ} (hfg : f+g ≤ 2) :
      (2*n)^f*(2*p)^g ≤ 4*(n^f*p^g) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hn, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hp]
    calc
      _ = ((2:ℝ)^f*(2:ℝ)^g)*(n^f*p^g) := by ring
      _ ≤ _ := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hfg).trans_eq (by norm_num)
  let F := onlineRate a b n p
  have hN : n ≤ F := le_max_left _ _
  have hP : p ≤ F := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hF : n^a*p^(2-2*a) ≤ F := (le_max_left _ _).trans (le_max_right _ _)
  have hG : n^(2-2*b)*p^b ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  change max (2*n) (max _ (max _ (2*p))) ≤ 4*F
  refine max_le (by linarith) (max_le ?_ (max_le ?_ (by linarith)))
  · exact (shift (by linarith)).trans (mul_le_mul_of_nonneg_left hF (by norm_num))
  · exact (shift (by linarith)).trans (mul_le_mul_of_nonneg_left hG (by norm_num))

/-- The corrected online exponent update for acyclic half-4-bridge-free
systems. The chosen branching window uses the input envelope coefficient. -/
theorem lemma37_acyclic_update {a b C : ℝ} (hC : 1 ≤ C) (ha₀ : 29/40 ≤ a) (ha₁ : a < 3/4)
    (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 701/1000)
    (hβ₀ : 2/3 ≤ onlineExponentStep b) (hβ₁ : onlineExponentStep b ≤ 701/1000)
    (prior : OnlineIncidenceBound.{u,v} a b C) :
    ∃ A ≥ 1, OnlineIncidenceBound.{u,v} ((2+b)/(3+b)) (onlineExponentStep b) A := by
  let α := (2+b)/(3+b)
  let β := onlineExponentStep b
  have α0 : 0 ≤ α := by unfold α; exact div_nonneg (by linarith) (by linarith)
  have α1 : α ≤ 1 := (div_le_iff₀ (by linarith : 0 < 3+b)).mpr (by linarith)
  have β0 : 0 ≤ β := by linarith
  have β1 : β ≤ 1 := by linarith
  obtain ⟨A, hA, denseBound⟩ := online_regular_step hC ha₀ ha₁ hb₀ hb₁ hβ₀ hβ₁ prior
  refine ⟨32+4*A, by linarith, ?_⟩
  intro V I _ _ _ _ paths free
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  let F := onlineRate α β (n:ℝ) (p:ℝ)
  have fN : (n:ℝ) ≤ F := le_max_left _ _
  have fP : (p:ℝ) ≤ F :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have f0 : 0 ≤ F := (Nat.cast_nonneg n).trans fN
  have castMass : (∑ i, ((paths i).card : ℝ)) = M := by simp only [M,Nat.cast_sum]
  rw [castMass]
  change (M:ℝ) ≤ (32+4*A)*F
  by_cases dense : 32*n < M
  swap
  · have real : (M:ℝ) ≤ 32*n := by exact_mod_cast (le_of_not_gt dense)
    nlinarith only [real, fN, mul_nonneg hA.le f0]
  by_cases long : 16*p < M
  swap
  · have real : (M:ℝ) ≤ 16*p := by exact_mod_cast (le_of_not_gt long)
    nlinarith only [real, fP, f0, mul_nonneg hA.le f0]
  have cap : M ≤ p*n := calc
    _ ≤ ∑ _i : I, n := sum_le_sum (fun i _ => card_le_univ (paths i))
    _ = _ := by simp [p, mul_comm]
  have hn : 0 < n := Nat.pos_of_ne_zero (fun e => by rw [e, mul_zero] at cap; omega)
  have hp : 0 < p := Nat.pos_of_ne_zero (fun e => by rw [e, zero_mul] at cap; omega)
  let D := M/n+1
  let L := M/p+1
  let vertices := splitVertices paths D
  let after := splitPaths vertices L
  let n' := Fintype.card (VertexBlockIndex paths D)
  let p' := Fintype.card (BlockIndex vertices L)
  obtain ⟨ncap, pcap, same, length, degree, avgD, avgL⟩ :=
    regularization_average_caps paths hn hp (by omega) (by omega)
  change n' ≤ 2*n at ncap
  change p' ≤ 2*p at pcap
  change (∑ i, (after i).card) = M at same
  have hn' : 0 < n' := hn.trans_le (blockIndex_card_ge (occurrences paths) D)
  have hp' : 0 < p' := hp.trans_le (blockIndex_card_ge vertices L)
  have deg' : 16*n' < ∑ i, (after i).card := by rw [same]; omega
  have len' : 8*p' < ∑ i, (after i).card := by rw [same]; omega
  have capL : L*p' ≤ 4*∑ i, (after i).card := same.symm ▸ avgL
  have capD : D*n' ≤ 4*∑ i, (after i).card := same.symm ▸ avgD
  have stage := denseBound (regularization_halfFree free D L) L D hn' hp'
    deg' len' capL capD length degree
  rw [same] at stage
  have size : onlineRate α β (n':ℝ) (p':ℝ) ≤ 4*F :=
    (onlineRate_mono α0 α1 β0 β1 (Nat.cast_nonneg n') (Nat.cast_nonneg p')
      (by exact_mod_cast ncap) (by exact_mod_cast pcap)).trans
      (onlineRate_double α0 β0 (Nat.cast_nonneg n) (Nat.cast_nonneg p))
  exact stage.trans ((mul_le_mul_of_nonneg_left size hA.le).trans (by nlinarith only [f0]))

private theorem online_incidence_initial : OnlineIncidenceBound.{u,v} (8/11) (2/3) 16 := by
  intro V I _ _ _ _ paths free
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  let F := onlineRate (8/11) (2/3) (n:ℝ) (p:ℝ)
  have hNF : (n:ℝ) ≤ F := le_max_left _ _
  have hPF : (p:ℝ) ≤ F :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have castMass : (∑ i, ((paths i).card : ℝ)) = M := by simp only [M, Nat.cast_sum]
  rw [castMass]
  change (M:ℝ) ≤ 16*F
  rcases lemma27_acyclic paths free with h | h | h
  · have hr : (M:ℝ) ≤ 16*n := by exact_mod_cast h
    linarith
  · have hr : (M:ℝ) ≤ 8*p := by exact_mod_cast h
    have hF : 0 ≤ F := (Nat.cast_nonneg p).trans hPF
    linarith
  · have hr : (M:ℝ)^3 ≤ 2048*((n:ℝ)*p)^2 := by exact_mod_cast h
    have hroot := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg M : (0:ℝ) ≤ M) 3) hr
        (show (0:ℝ) ≤ 1/3 by norm_num)
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg M) 3,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2048) (by positivity),
      ← Real.rpow_natCast_mul (by positivity : 0 ≤ (n:ℝ)*p) 2,
      Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg p)] at hroot
    norm_num at hroot
    have c : (2048:ℝ)^(1/3:ℝ) ≤ 16 := by
      have t := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 2048)
        (by norm_num : (2048:ℝ) ≤ (16:ℝ)^3) (by norm_num : (0:ℝ) ≤ 1/3)
      rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 16) 3] at t
      norm_num at t
      exact t
    have hG : (n:ℝ)^(2/3:ℝ)*(p:ℝ)^(2/3:ℝ) ≤ F := by
      have ha : (n:ℝ)^(2-2*(2/3:ℝ))*(p:ℝ)^(2/3:ℝ) ≤ F :=
        (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      norm_num at ha
      exact ha
    calc
      _ ≤ _ := hroot
      _ ≤ 16*((n:ℝ)^(2/3:ℝ)*(p:ℝ)^(2/3:ℝ)) := by grw [c]
      _ ≤ _ := mul_le_mul_of_nonneg_left hG (by norm_num)

/-- Each finite iterate in Theorem 38 is an incidence bound on actual
acyclic systems, with a constant uniform over systems at that iterate. -/
theorem theorem38_acyclic_iteration (k : ℕ) :
    ∃ C ≥ 1, OnlineIncidenceBound.{u,v} (onlineFirstExponent k) (onlineSecondExponent k) C := by
  obtain ⟨α, ⟨ha, hz⟩, _⟩ := theorem38_root
  obtain ⟨_, hsec, hfirst, _, _⟩ := theorem38_exponent_limits ha hz
  induction k with
  | zero => exact ⟨16, by norm_num, online_incidence_initial⟩
  | succ k ih =>
    obtain ⟨C, hC, prior⟩ := ih
    have next : onlineSecondExponent (k+1) = onlineExponentStep (onlineSecondExponent k) :=
      Function.iterate_succ_apply' _ _ _
    have hβ := hsec (k+1)
    rw [next] at hβ
    have b := hsec k
    have a := hfirst k
    have carry := lemma37_acyclic_update hC ((by norm_num : (29/40:ℝ) ≤ 8/11).trans a.1) a.2
      b.1 (b.2.trans ha.2).le hβ.1 (hβ.2.trans ha.2).le prior
    rw [next]
    exact carry

end OnlineReachabilityPreservers
