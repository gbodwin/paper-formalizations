import OnlineReachabilityPreservers.BranchWindow
import OnlineReachabilityPreservers.BranchingDegrees

/-! The Appendix B critical power in the path-length second moment. -/

namespace OnlineReachabilityPreservers

open Finset

/-- The offline recurrence's square-root term gives a logarithm in the moment.
Choose the online exponent within 1/max(4, log n) of 3/4 and apply the
finite online moment estimate with this exponent. -/
theorem lemma40_ranked_moment (N : ℕ) (values : ℕ → ℝ) {n d L C b : ℝ}
    (hn : 1 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hL : 0 < L) (hC : 0 < C)
    (hb₀ : 1/2 < b) (hb₁ : b ≤ 1)
    (nonneg : ∀ i < N, 0 ≤ values i)
    (decreasing : ∀ i j, i ≤ j → j < N → values j ≤ values i)
    (cap : ∀ i < N, values i ≤ L)
    (total : (∑ i ∈ range N, values i) ≤ n*d)
    (prefixBounds : ∀ k ≤ N, (∑ i ∈ range k, values i) ≤
      C * max n (max (n^(3/4 : ℝ)*(k:ℝ)^(1/2 : ℝ)) (max (n^(2-2*b)*(k:ℝ)^b) (k:ℝ)))) :
    (∑ i ∈ range N, (values i)^2) ≤
      2*C*n*L + Real.exp 8 * (max 1 C)^2 * (2+Real.log n) * n^(3/2 : ℝ) +
      (2*C+(1/(2*b-1)+1)*C^(1/b))*n^(1/b)*d^((2*b-1)/b) := by
  let t := max 4 (Real.log n)
  let a : ℝ := 3/4 - 1/t
  have npos : 0 < n := zero_lt_one.trans_le hn
  have log_nonneg := Real.log_nonneg hn
  have lt : 4 ≤ t := le_max_left _ _
  have tpos : 0 < t := (by norm_num : (0 : ℝ) < 4).trans_le lt
  have log_le : Real.log n ≤ t := le_max_right _ _
  have ht : t ≤ 4+Real.log n := max_le (by linarith) (by linarith)
  have inv_pos := one_div_pos.mpr tpos
  have inv_le := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) lt
  have la : 1/2 ≤ a := by dsimp [a]; linarith
  have ua : a < 3/4 := by dsimp [a]; linarith
  have bound := lemma31_ranked_moment N values npos hd hL hC la ua hb₀ hb₁
    nonneg decreasing cap total (by
      intro k hk
      apply (prefixBounds k hk).trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      have h := square_root_rate_le npos (by positivity : (0 : ℝ) ≤ k) ua.le
      apply max_le
      · exact le_max_left _ _
      · apply max_le
        · exact h.trans (max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _)))
        · exact le_max_right _ _ |>.trans (le_max_right _ _))
  have ha : 0 < 2-2*a := by linarith
  have ha2 : 1/(2-2*a) ≤ 2 := (div_le_iff₀ ha).mpr (by linarith)
  have coeff : 3-4*a = 4/t := by dsimp [a]; ring
  have ep : 0 ≤ (3-4*a)/(2-2*a) := div_nonneg (by linarith) ha.le
  have ep_le : (3-4*a)/(2-2*a) ≤ 8/t := by
    rw [coeff, div_eq_mul_one_div]
    exact (mul_le_mul_of_nonneg_left ha2 (by positivity)).trans_eq (by ring)
  have t_bound : 1/(3-4*a)+1 ≤ 2+Real.log n := by
    rw [coeff, one_div_div]
    linarith
  have c_bound : C^(1/(2-2*a)) ≤ (max 1 C)^2 := by
    rw [← Real.rpow_two]
    exact (Real.rpow_le_rpow hC.le (le_max_right _ _) (by positivity)).trans
      (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) ha2)
  have d_bound : d^((3-4*a)/(2-2*a)) ≤ Real.exp 8 := calc
    _ ≤ n^((3-4*a)/(2-2*a)) := Real.rpow_le_rpow hd.le hdn ep
    _ ≤ n^(8/t) := Real.rpow_le_rpow_of_exponent_le hn ep_le
    _ = Real.exp (Real.log n * (8/t)) := Real.rpow_def_of_pos npos _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ t*(8/t) := mul_le_mul_of_nonneg_right log_le (by positivity)
        _ = _ := by field_simp
  have mid :
      (1/(3-4*a)+1)*C^(1/(2-2*a))*n^(3/2 : ℝ)*d^((3-4*a)/(2-2*a)) ≤
        Real.exp 8 * (max 1 C)^2 * (2+Real.log n) * n^(3/2 : ℝ) := calc
    _ ≤ (2+Real.log n)*(max 1 C)^2*n^(3/2 : ℝ)*Real.exp 8 := by gcongr
    _ = _ := by ring
  let e : ℝ := (2*b-1)/b
  have hb : 0 < b := by linarith
  have invB : 0 ≤ 1/b-1 := sub_nonneg.mpr ((le_div_iff₀ hb).mpr (by linarith))
  have eqD : (1/b-1)+e = 1 := by
    dsimp [e]
    field_simp
    ring
  have degree : n*d ≤ n^(1/b)*d^e := calc
    _ = d^(1/b-1)*(n*d^e) := by
      rw [show d^(1/b-1)*(n*d^e)=n*(d^(1/b-1)*d^e) by ring,
        ← Real.rpow_add hd, eqD, Real.rpow_one]
    _ ≤ n^(1/b-1)*(n*d^e) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd.le hdn invB) (by positivity)
    _ = (n^(1/b-1)*n^(1:ℝ))*d^e := by rw [Real.rpow_one, mul_assoc]
    _ = _ := by rw [← Real.rpow_add npos, show 1/b-1+1 = 1/b by ring]
  calc
    _ ≤ _ := bound
    _ = 2*C*n*L + (1/(3-4*a)+1)*C^(1/(2-2*a))*n^(3/2 : ℝ)*d^((3-4*a)/(2-2*a)) +
        (1/(2*b-1)+1)*C^(1/b)*n^(1/b)*d^e + 2*C*(n*d) := by ring
    _ ≤ 2*C*n*L + Real.exp 8 * (max 1 C)^2 * (2+Real.log n) * n^(3/2 : ℝ) +
        (1/(2*b-1)+1)*C^(1/b)*n^(1/b)*d^e + 2*C*(n^(1/b)*d^e) := by gcongr
    _ = _ := by ring

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

/-- Lemma 40 for acyclic full bridge-free systems. The ambient size bound n
also bounds the degree parameter d, as in the sampling application. -/
theorem lemma40_acyclic_moment (paths : I → Finset V) (free : BridgeFree (PathBefore paths) 4)
    {n d L C b : ℝ} (hn : 1 ≤ n) (hd : 0 < d) (hdn : d ≤ n) (hL : 0 < L) (hC : 0 < C)
    (hb₀ : 1/2 < b) (hb₁ : b ≤ 1)
    (cap : ∀ i, ((paths i).card : ℝ) ≤ L)
    (mass : (∑ i, ((paths i).card : ℝ)) ≤ n*d)
    (subfamily : ∀ J : Finset I, BridgeFree (PathBefore fun i : J => paths i.val) 4 →
      let p : ℝ := J.card
      (∑ i ∈ J, ((paths i).card : ℝ)) ≤
        C * max n (max (n^(3/4 : ℝ)*p^(1/2 : ℝ)) (max (n^(2-2*b)*p^b) p))) :
    (∑ i, ((paths i).card : ℝ)^2) ≤
      2*C*n*L + Real.exp 8 * (max 1 C)^2 * (2+Real.log n) * n^(3/2 : ℝ) +
      (2*C+(1/(2*b-1)+1)*C^(1/b))*n^(1/b)*d^((2*b-1)/b) := by
  let p := Fintype.card I
  obtain ⟨values, order, listed, prefixes⟩ := ranked_path_lengths paths
  obtain ⟨all, hc, sums⟩ := prefixes p le_rfl
  have heq : all = (Finset.univ : Finset I) := Finset.eq_univ_of_card _ hc
  have total : (∑ i ∈ range p, values i) = ∑ j, ((paths j).card : ℝ) := by
    simpa only [heq, id_eq] using sums id
  have bound := lemma40_ranked_moment p values hn hd hdn hL hC hb₀ hb₁
    (fun i hi => by obtain ⟨j, eq⟩ := listed i hi; rw [eq]; positivity) order
    (fun i hi => by obtain ⟨j, eq⟩ := listed i hi; rw [eq]; exact cap j) (total.le.trans mass) (by
      intro k hk
      obtain ⟨J, hJ, hsum⟩ := prefixes k hk
      have eq : (∑ i ∈ range k, values i) = ∑ j ∈ J, ((paths j).card : ℝ) := hsum id
      rw [eq]
      simpa only [hJ] using subfamily J (free.restrict_paths J))
  rw [sums (· ^ 2), heq] at bound
  exact bound

variable [Fintype V]

omit [Fintype V] [LinearOrder I] in
/-- Bound the sample size from the path length and degree caps. -/
theorem branchSupport_card_caps (paths : I → Finset V) (b : I) (h L D : ℕ)
    (cap : (paths b).card ≤ L) (degree_cap : ∀ u ∈ paths b, (occurrences paths u).card ≤ D) :
    (branchSupport paths b h).card ≤ L*D*(h+1) := calc
  _ ≤ ∑ u ∈ paths b, (occurrences paths u).card*(h+1) := branchSupport_card paths b h
  _ ≤ ∑ _ ∈ paths b, D*(h+1) := sum_le_sum fun u hu => Nat.mul_le_mul_right _ (degree_cap u hu)
  _ = (paths b).card * D * (h+1) := by simp [mul_assoc]
  _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ cap)

/-- The upper bound on Q in Lemma 41, after substituting the moment estimate
on the actual sampled system. The parameter n can be any ambient upper bound
on the sample size that also bounds D. -/
theorem lemma41_sampled_upper {paths : I → Finset V} (free : BridgeFree (PathBefore paths) 4)
    (base : I) (h D : ℕ) {n L C b : ℝ} (hn : 1 ≤ n) (hD : 0 < D) (hdn : (D : ℝ) ≤ n)
    (hL : 0 < L) (hC : 0 < C) (hb₀ : 1/2 < b) (hb₁ : b ≤ 1)
    (ambient : ((branchSupport paths base h).card : ℝ) ≤ n)
    (cap : ∀ i, ((paths i).card : ℝ) ≤ L)
    (degree_cap : ∀ u ∈ branchSupport paths base h, (occurrences paths u).card ≤ D)
    (subfamily : ∀ J : Finset I,
      BridgeFree (PathBefore (inducedPaths paths (branchSupport paths base h) J)) 4 →
      let p : ℝ := J.card
      (∑ i : J, ((inducedPaths paths (branchSupport paths base h) J i).card : ℝ)) ≤
        C * max n (max (n^(3/4 : ℝ)*p^(1/2 : ℝ)) (max (n^(2-2*b)*p^b) p))) :
    ((branchTuples paths base h).card : ℝ) ≤
      2*C*n*L + Real.exp 8 * (max 1 C)^2 * (2+Real.log n) * n^(3/2 : ℝ) +
      (2*C+(1/(2*b-1)+1)*C^(1/b))*n^(1/b)*(D : ℝ)^((2*b-1)/b) := by
  let S := branchSupport paths base h
  let restricted := inducedPath paths S
  have lengths (i : I) : ((restricted i).card : ℝ) ≤ L := by
    change ((inducedPath paths S i).card : ℝ) ≤ L
    rw [inducedPath_card]
    have sub : ((paths i ∩ S).card : ℝ) ≤ (paths i).card := by
      exact_mod_cast card_le_card (inter_subset_left : paths i ∩ S ⊆ paths i)
    exact sub.trans (cap i)
  have massNat : (∑ i, (restricted i).card) ≤ S.card * D :=
    inducedPath_mass_le paths S D degree_cap
  have mass : (∑ i, ((restricted i).card : ℝ)) ≤ n*D := calc
    _ ≤ (S.card : ℝ)*D := by exact_mod_cast massNat
    _ ≤ _ := mul_le_mul_of_nonneg_right ambient (by positivity)
  have upper := lemma40_acyclic_moment restricted (free.induced_vertices S) hn
    (show (0 : ℝ) < D by exact_mod_cast hD) hdn hL hC hb₀ hb₁ lengths mass (by
      intro J hfree
      have hi := subfamily J hfree
      change (∑ i : J, ((restricted i.val).card : ℝ)) ≤ _ at hi
      have sum_eq : (∑ i : J, ((restricted i.val).card : ℝ)) = ∑ i ∈ J, ((restricted i).card : ℝ) :=
        J.sum_coe_sort (fun i : I => ((restricted i).card : ℝ))
      rwa [sum_eq] at hi)
  have card : (branchTuples paths base h).card ≤ ∑ i, (restricted i).card^2 := calc
    _ ≤ ∑ i, (paths i ∩ S).card.choose 2 := lemma41_branch_count free base h
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      have eq : (restricted i).card = (paths i ∩ S).card := inducedPath_card paths S i
      rw [eq, square_choose]
      omega
  exact (show ((branchTuples paths base h).card : ℝ) ≤ ∑ i, ((restricted i).card : ℝ)^2 by
    exact_mod_cast card).trans upper

end OnlineReachabilityPreservers
