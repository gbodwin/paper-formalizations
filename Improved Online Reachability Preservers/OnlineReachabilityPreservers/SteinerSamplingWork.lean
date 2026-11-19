import Mathlib.Data.Nat.Size
import OnlineReachabilityPreservers.SteinerSeedCoordinates

/-! Bit budgets for the independent integer seed coordinates. -/

namespace OnlineReachabilityPreservers

/-- Reading a fixed number of bits gives exactly one word in the
corresponding power-of-two range, including the empty word. -/
def uniformBitsEquiv : (w : ℕ) → (Fin w → Bool) ≃ Fin (2^w)
  | 0 =>
    { toFun := fun _ => 0
      invFun := fun _ i => i.elim0
      left_inv := fun f => funext (fun i => i.elim0)
      right_inv := by
        intro i
        apply Fin.ext
        have bound : i.val < 1 := by simpa only [pow_zero] using i.isLt
        change 0 = i.val
        omega }
  | w+1 =>
    let split : (Fin (w+1) → Bool) ≃ Bool × (Fin w → Bool) :=
      { toFun := fun f => (f 0, fun i => f i.succ)
        invFun := fun r => Fin.cases r.1 r.2
        left_inv := fun f => funext (Fin.cases rfl (fun _ => rfl))
        right_inv := fun _ => rfl }
    split.trans ((finTwoEquiv.symm.prodCongr (uniformBitsEquiv w)).trans
      (finProdFinEquiv.trans (finCongr (pow_succ' 2 w).symm)))

/-- The bit width of a rejection-sampling proposal for a range of size `N`. -/
def uniformProposalWidth (N : ℕ) : ℕ := (N-1).size

theorem uniformProposalSize_bounds {N : ℕ} (positive : 0 < N) :
    N ≤ 2^uniformProposalWidth N ∧ 2^uniformProposalWidth N ≤ 2*N := by
  have low := Nat.lt_size_self (N-1)
  constructor
  · change N ≤ 2^(N-1).size
    omega
  · unfold uniformProposalWidth
    cases h : (N-1).size with
    | zero => simp; omega
    | succ k =>
      have earlier : k < (N-1).size := by omega
      have small := Nat.lt_size.mp earlier
      rw [pow_succ']
      exact Nat.mul_le_mul_left _ (small.trans (Nat.sub_le _ _))

/-- Summing the probabilities of all first successful attempts gives
exactly the uniform target probability. The expected number of proposals
is at most two. -/
theorem uniformRejectionSeries {N : ℕ} (positive : 0 < N) :
    let total : ℝ := (2^uniformProposalWidth N : ℕ)
    let miss := (total-N)/total
    0 ≤ miss ∧ miss ≤ 1/2 ∧
      (∑' k : ℕ, miss^k * (1/total)) = 1/(N:ℝ) ∧
      (∑' k : ℕ, miss^k) ≤ 2 := by
  let total : ℝ := (2^uniformProposalWidth N : ℕ)
  let miss := (total-N)/total
  obtain ⟨small, large⟩ := uniformProposalSize_bounds positive
  have pp : (0:ℝ) < N := Nat.cast_pos.mpr positive
  have smallR : (N:ℝ) ≤ total := Nat.cast_le.mpr small
  have largeR : total ≤ (2:ℝ)*N := by
    dsimp only [total]
    exact_mod_cast large
  have tp : 0 < total := pp.trans_le smallR
  have r0 : 0 ≤ miss := div_nonneg (sub_nonneg.mpr smallR) tp.le
  have r1 : miss ≤ 1/2 := (div_le_iff₀ tp).mpr (by linarith)
  have rlt : miss < 1 := by linarith
  have sum := tsum_geometric_of_lt_one r0 rlt
  have value : 1-miss = (N:ℝ)/total := by
    dsimp only [miss]
    field_simp
    ring
  have expected : (∑' k : ℕ, miss^k) = total/N := by rw [sum, value, inv_div]
  change 0 ≤ miss ∧ miss ≤ 1/2 ∧
    (∑' k : ℕ, miss^k * (1/total)) = 1/(N:ℝ) ∧ (∑' k : ℕ, miss^k) ≤ 2
  refine ⟨r0, r1, ?_, ?_⟩
  · rw [tsum_mul_right, expected]
    field_simp
  · rw [expected]
    exact (div_le_iff₀ pp).mpr largeR

private def rejectedProposals (N : ℕ) : Finset (Fin (2^uniformProposalWidth N)) :=
  Finset.univ.filter fun i => N ≤ i.val

private theorem rejectedProposals_card {N : ℕ} (h : N ≤ 2^uniformProposalWidth N) :
    (rejectedProposals N).card = 2^uniformProposalWidth N - N := by
  let accepted := (Finset.univ : Finset (Fin N)).map (Fin.castLEEmb h)
  have count : accepted.card = N := by simp [accepted]
  have members {i : Fin (2^uniformProposalWidth N)} : i ∈ accepted ↔ i.val < N := by
    constructor
    · intro member
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp member
      exact j.isLt
    · intro member
      exact Finset.mem_map.mpr ⟨⟨i.val, member⟩, Finset.mem_univ _, Fin.ext rfl⟩
  have eq : rejectedProposals N = Finset.univ \ accepted := by
    ext i
    simp [rejectedProposals, members, not_lt]
  rw [eq, Finset.card_sdiff_of_subset (Finset.subset_univ _), count, Finset.card_univ, Fintype.card_fin]

/-- Choices on the first `k` attempts are rejected and the last word
represents target `t`. The finite independent sample checks this event. -/
noncomputable def rejectionAtAttempt {N : ℕ} (positive : 0 < N) (k : ℕ) (t : Fin N) :
    Finset (Fin (k+1) → Fin (2^uniformProposalWidth N)) :=
  constrainedSamples fun i => if i = Fin.last k then
    {Fin.castLEEmb (uniformProposalSize_bounds positive).1 t}
    else rejectedProposals N

theorem rejectionAtAttempt_probability {N : ℕ} (positive : 0 < N) (k : ℕ) (t : Fin N) :
    let total : ℝ := (2^uniformProposalWidth N : ℕ)
    finiteProbability (rejectionAtAttempt positive k t) = ((total-N)/total)^k * (1/total) := by
  let h := (uniformProposalSize_bounds positive).1
  dsimp only [rejectionAtAttempt]
  rw [finiteProbability_constrainedSamples, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_ne_last, ite_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ite_true, finiteProbability, rejectedProposals_card h, Finset.card_singleton,
    Nat.cast_sub h, Nat.cast_one]

/-- The actual independent trial events sum to an exact uniform draw. -/
theorem uniformRejection_target_probability {N : ℕ} (positive : 0 < N) (t : Fin N) :
    (∑' k : ℕ, finiteProbability (rejectionAtAttempt positive k t)) = 1/(N:ℝ) := by
  simp_rw [rejectionAtAttempt_probability positive]
  exact (uniformRejectionSeries positive).2.2.1

/-- The same event on the independent input bits of the proposed words. -/
noncomputable def rejectionAtBitAttempt {N : ℕ} (positive : 0 < N) (k : ℕ) (t : Fin N) :
    Finset (Fin (k+1) → Fin (uniformProposalWidth N) → Bool) :=
  (rejectionAtAttempt positive k t).map
    (Equiv.arrowCongr (Equiv.refl _) (uniformBitsEquiv (uniformProposalWidth N)).symm).toEmbedding

theorem rejectionAtBitAttempt_probability {N : ℕ} (positive : 0 < N) (k : ℕ) (t : Fin N) :
    let total : ℝ := (2^uniformProposalWidth N : ℕ)
    finiteProbability (rejectionAtBitAttempt positive k t) = ((total-N)/total)^k*(1/total) := by
  have same : finiteProbability (rejectionAtBitAttempt positive k t) =
      finiteProbability (rejectionAtAttempt positive k t) := by
    simp only [rejectionAtBitAttempt, finiteProbability, Finset.card_map,
      ← Fintype.card_congr (Equiv.arrowCongr (Equiv.refl (Fin (k+1)))
        (uniformBitsEquiv (uniformProposalWidth N)).symm)]
  exact same.trans (rejectionAtAttempt_probability positive k t)

theorem uniformBitRejection_target_probability {N : ℕ} (positive : 0 < N) (t : Fin N) :
    (∑' k : ℕ, finiteProbability (rejectionAtBitAttempt positive k t)) = 1/(N:ℝ) := by
  simp_rw [rejectionAtBitAttempt_probability positive]
  exact (uniformRejectionSeries positive).2.2.1

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- The checked flattened early seed can be built directly from fair bit words. -/
def earlySeedBitWords (G : Arcs V) (height : ℕ) :
    EarlyRoundSample G height ≃
      (EarlySeedCoordinate G height → Fin ((forestScale G height).log2+1) → Bool) :=
  (earlySeedCoordinates G height).trans
    (Equiv.arrowCongr (Equiv.refl _) (uniformBitsEquiv ((forestScale G height).log2+1)).symm)

/-- A complete early seed is exactly an array of fixed-width fair bit words. -/
def earlySeedBits (G : Arcs V) (height : ℕ) : ℕ :=
  Fintype.card (EarlySeedCoordinate G height)*((forestScale G height).log2+1)

theorem earlySeedBits_le [Nonempty V] (G : Arcs V) (height : ℕ) :
    let n := Fintype.card V
    let B := max 1 (n * Fintype.card (HeightForestVertex V height)^2)
    earlySeedBits G height ≤
      earlyTrialCount V height * (n * ((B.log2+1)^2*(2*((height+1)*n^height)+1))) := by
  let n := Fintype.card V
  let B := max 1 (n * Fintype.card (HeightForestVertex V height)^2)
  have scale : forestScale G height ≤ B := forestNetworkScale_le G height
  have width : (forestScale G height).log2+1 ≤ B.log2+1 := by
    apply Nat.succ_le_succ
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) scale
  have card := earlySeedCoordinate_card_le G height
  unfold earlySeedBits
  calc
    _ ≤ (earlyTrialCount V height*(n*((B.log2+1)*(2*((height+1)*n^height)+1))))*(B.log2+1) := by
      apply Nat.mul_le_mul _ width
      refine card.trans ?_
      gcongr
    _ = _ := by ring

/-- Expected bit bound for the separate hub and thin draws. A draw of size
zero has no coordinates in the actual algorithm. -/
noncomputable def expectedRejectionBits (N : ℕ) : ℝ :=
  let total : ℝ := (2^uniformProposalWidth N : ℕ)
  (uniformProposalWidth N : ℝ) * (∑' k : ℕ, ((total-N)/total)^k)

theorem expectedRejectionBits_le {N : ℕ} (positive : 0 < N) :
    expectedRejectionBits N ≤ 2*(uniformProposalWidth N : ℝ) := by
  have bound := (uniformRejectionSeries positive).2.2.2
  calc
    _ ≤ (uniformProposalWidth N : ℝ)*2 := mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The seed generation uses one thin grid choice per input arc and one
vertex choice per hub draw, independently of the early coordinate array. -/
noncomputable def completeSteinerExpectedSeedBits (G : Arcs V) (height : ℕ) : ℝ :=
  earlySeedBits G height +
    (completeSteinerHubCount V : ℝ)*expectedRejectionBits (Fintype.card V) +
    (G.card : ℝ)*expectedRejectionBits G.card

theorem completeSteinerExpectedSeedBits_le (G : Arcs V) (height : ℕ) :
    completeSteinerExpectedSeedBits G height ≤
      earlySeedBits G height +
        (completeSteinerHubCount V : ℝ)*(2*uniformProposalWidth (Fintype.card V)) +
        (G.card : ℝ)*(2*uniformProposalWidth G.card) := by
  have hub : (completeSteinerHubCount V : ℝ)*expectedRejectionBits (Fintype.card V) ≤
      (completeSteinerHubCount V : ℝ)*(2*uniformProposalWidth (Fintype.card V)) := by
    by_cases empty : Fintype.card V = 0
    · rw [@completeSteinerHubCount_empty V _ (Fintype.card_eq_zero_iff.mp empty)]
      simp
    · exact mul_le_mul_of_nonneg_left (expectedRejectionBits_le (Nat.pos_of_ne_zero empty)) (Nat.cast_nonneg _)
  have thin : (G.card : ℝ)*expectedRejectionBits G.card ≤ (G.card : ℝ)*(2*uniformProposalWidth G.card) := by
    by_cases empty : G.card = 0
    · simp [empty]
    · exact mul_le_mul_of_nonneg_left (expectedRejectionBits_le (Nat.pos_of_ne_zero empty)) (Nat.cast_nonneg _)
  exact add_le_add (add_le_add le_rfl hub) thin


theorem uniformProposalWidth_le (N : ℕ) : uniformProposalWidth N ≤ N :=
  Nat.size_le.mpr ((Nat.sub_le _ _).trans_lt Nat.lt_two_pow_self)

/-- An explicit polynomial in graph sizes for each fixed height. -/
def completeSteinerSeedPolynomial (n m height : ℕ) : ℕ :=
  let history := (height+1)*n^height
  let forest := (n*2)*history
  let scale := 1+n*forest^2
  16*(height+1)^2*(n+1)*n*((scale+1)^2*(2*history+1)) +
    (4*(n+1)*n+1)*(2*n)+m*(2*m)

theorem completeSteinerExpectedSeedBits_polynomial (G : Arcs V) (height : ℕ) :
    completeSteinerExpectedSeedBits G height ≤
      completeSteinerSeedPolynomial (Fintype.card V) G.card height := by
  let n := Fintype.card V
  let m := G.card
  let history := (height+1)*n^height
  let forest := (n*2)*history
  let scale := 1+n*forest^2
  let early := 16*(height+1)^2*(n+1)*n*((scale+1)^2*(2*history+1))
  have first : earlySeedBits G height ≤ early := by
    by_cases empty : n = 0
    · simp [earlySeedBits, n, empty]
    · have nonempty : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero empty)
      have number : Fintype.card (HeightForestVertex V height) ≤ forest :=
        @heightForestVertex_card_le V _ nonempty height
      have cap : max 1 (n*Fintype.card (HeightForestVertex V height)^2) ≤ scale := by
        unfold scale
        exact max_le (Nat.le_add_right _ _) ((by gcongr : n*Fintype.card (HeightForestVertex V height)^2 ≤ n*forest^2).trans
          (Nat.le_add_left _ _))
      have logCap : (max 1 (n*Fintype.card (HeightForestVertex V height)^2)).log2+1 ≤ scale+1 :=
        Nat.succ_le_succ ((Nat.log2_le_self _).trans cap)
      refine (@earlySeedBits_le V _ _ nonempty G height).trans ?_
      change earlyTrialCount V height*(n*((((max 1 (n*Fintype.card (HeightForestVertex V height)^2)).log2)+1)^2*(2*history+1))) ≤ early
      unfold earlyTrialCount early
      change 16*(height+1)^2*(n.log2+1)*(n*(_*(2*history+1))) ≤ _
      calc
        _ ≤ 16*(height+1)^2*(n+1)*(n*((scale+1)^2*(2*history+1))) := by
          gcongr
          exact Nat.log2_le_self _
        _ = _ := by ring
  have hubs : completeSteinerHubCount V ≤ 4*(n+1)*n+1 :=
    (completeSteinerHubCount_le V).trans (by gcongr; exact Nat.log2_le_self _)
  have sum : earlySeedBits G height+
      completeSteinerHubCount V*(2*uniformProposalWidth n)+m*(2*uniformProposalWidth m) ≤
      completeSteinerSeedPolynomial n m height := by
    change _ ≤ early+(4*(n+1)*n+1)*(2*n)+m*(2*m)
    exact Nat.add_le_add (Nat.add_le_add first
      (Nat.mul_le_mul hubs (Nat.mul_le_mul_left _ (uniformProposalWidth_le n))))
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (uniformProposalWidth_le m)))
  exact (completeSteinerExpectedSeedBits_le G height).trans (by exact_mod_cast sum)

end OnlineReachabilityPreservers
