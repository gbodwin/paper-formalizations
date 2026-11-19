import Mathlib.Analysis.SpecificLimits.Normed
import OnlineReachabilityPreservers.SteinerSamplingWork

/-! Connect the finite independent proposal events to the executable retry loop. -/

namespace OnlineReachabilityPreservers

open Finset

abbrev UniformProposal (N : ℕ) := Fin (2^uniformProposalWidth N)

private def retryProposals {A : Type*} (N : ℕ) (encode : A → UniformProposal N) :
    List A → Option (Fin N × ℕ)
  | [] => none
  | proposal::rest =>
    let word := encode proposal
    if h : word.val < N then some (⟨word.val,h⟩,1)
    else (retryProposals N encode rest).map fun (value,count) => (value,count+1)

/-- Return the first accepted index and the one-based number of proposals
used. An exhausted finite input leaves the result absent. -/
def uniformRetry (N : ℕ) : List (UniformProposal N) → Option (Fin N × ℕ) :=
  retryProposals N id

theorem uniformRetry_at_last {N : ℕ} (P : List (UniformProposal N))
    (last : UniformProposal N) (target : Fin N) :
    uniformRetry N (P++[last]) = some (target,P.length+1) ↔
      (∀ w ∈ P, N ≤ w.val) ∧ last.val = target.val := by
  induction P with
  | nil =>
    by_cases good : last.val < N
    · simp [uniformRetry,retryProposals,good,Fin.ext_iff]
    · simp [uniformRetry,retryProposals,good]
      exact fun h => good (h ▸ target.isLt)
  | cons w P ih =>
    rw [List.cons_append]
    change ((if h : w.val < N then some (⟨w.val,h⟩,1) else
      (uniformRetry N (P++[last])).map (fun x => (x.1,x.2+1))) = some (target,(w::P).length+1)) ↔ _
    by_cases good : w.val < N
    · rw [dite_eq_left good]
      constructor
      · intro eq
        have count := congrArg (fun out : Option (Fin N × ℕ) => out.map Prod.snd) eq
        simp only [Option.map_some, Option.some.injEq, List.length_cons] at count
        omega
      · rintro ⟨reject,_⟩
        exact (good.not_ge (reject w List.mem_cons_self)).elim
    · rw [dite_eq_right good]
      have mapped : (uniformRetry N (P++[last])).map (fun x => (x.1,x.2+1)) =
          some (target,(w::P).length+1) ↔
          uniformRetry N (P++[last]) = some (target,P.length+1) := by
        cases uniformRetry N (P++[last]) with
        | none => simp
        | some value =>
          rcases value with ⟨out,count⟩
          simp
      rw [mapped,ih]
      simp [not_lt.mp good]

/-- The k-th failure prefix followed by success is exactly an output
of the deterministic retry evaluator. -/
theorem uniformRetry_event {N : ℕ} (positive : 0 < N) (k : ℕ) (target : Fin N)
    (words : Fin (k+1) → UniformProposal N) :
    uniformRetry N (List.ofFn words) = some (target,k+1) ↔
      words ∈ rejectionAtAttempt positive k target := by
  rw [List.ofFn_succ_last]
  have check := uniformRetry_at_last (List.ofFn fun i : Fin k => words i.castSucc) (words (Fin.last k)) target
  rw [List.length_ofFn] at check
  rw [check]
  change ((∀ w ∈ List.ofFn (fun i : Fin k => words i.castSucc), N ≤ w.val) ∧
    (words (Fin.last k)).val = target.val) ↔
    words ∈ constrainedSamples (fun i => if i = Fin.last k then
      {Fin.castLEEmb (uniformProposalSize_bounds positive).1 target}
      else univ.filter (fun w => N ≤ w.val))
  unfold constrainedSamples
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨rejected,accepted⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have eq : words (Fin.last k) = Fin.castLEEmb (uniformProposalSize_bounds positive).1 target :=
        Fin.ext (by exact accepted)
      simpa using eq
    · simpa only [ite_eq_right (Fin.castSucc_ne_last j), mem_filter, mem_univ, true_and] using
        rejected (words j.castSucc) (List.mem_ofFn.mpr ⟨j,rfl⟩)
  · intro all
    constructor
    · intro w member
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
      simpa only [ite_eq_right (Fin.castSucc_ne_last j), mem_filter, mem_univ, true_and] using all j.castSucc
    · have h : words (Fin.last k) = Fin.castLEEmb (uniformProposalSize_bounds positive).1 target := by
        simpa using all (Fin.last k)
      exact congrArg Fin.val h

/-- Read independent fair bit words directly and return the first in range. -/
def fairBitRetry (N : ℕ) (bits : List (Fin (uniformProposalWidth N) → Bool)) :
    Option (Fin N × ℕ) :=
  retryProposals N (uniformBitsEquiv (uniformProposalWidth N)) bits

private theorem fairBitRetry_eq_words (N : ℕ) (bits : List (Fin (uniformProposalWidth N) → Bool)) :
    fairBitRetry N bits = uniformRetry N (bits.map (uniformBitsEquiv (uniformProposalWidth N))) := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
    dsimp only [fairBitRetry, uniformRetry] at ih
    simp only [fairBitRetry, uniformRetry, List.map_cons, retryProposals, id_eq, ih]

noncomputable def fairBitRetryLastEvent {N : ℕ} (k : ℕ) (target : Fin N) :
    Finset (Fin (k+1) → Fin (uniformProposalWidth N) → Bool) := by
  classical
  exact univ.filter fun bits => fairBitRetry N (List.ofFn bits) = some (target,k+1)

theorem fairBitRetryLastEvent_eq {N : ℕ} (positive : 0 < N) (k : ℕ) (target : Fin N) :
    fairBitRetryLastEvent k target = rejectionAtBitAttempt positive k target := by
  classical
  let encoding := Equiv.arrowCongr (Equiv.refl (Fin (k+1))) (uniformBitsEquiv (uniformProposalWidth N))
  ext bits
  have view : uniformRetry N (List.ofFn (encoding bits)) = fairBitRetry N (List.ofFn bits) := by
    simp only [fairBitRetry_eq_words, List.map_ofFn]
    rfl
  simp only [fairBitRetryLastEvent, mem_filter, mem_univ, true_and, ← view, uniformRetry_event positive]
  change (encoding bits) ∈ rejectionAtAttempt positive k target ↔
    bits ∈ (rejectionAtAttempt positive k target).map encoding.symm.toEmbedding
  exact ⟨fun member => mem_map.mpr ⟨_,member,encoding.symm_apply_apply _⟩,
    fun member => by
      obtain ⟨word,valid,eq⟩ := mem_map.mp member
      change encoding.symm word = bits at eq
      rw [← eq, encoding.apply_symm_apply]
      exact valid⟩

/-- The exact uniform law is the sum of the actual evaluator's finite
first-success events. -/
theorem fairBitRetry_uniform {N : ℕ} (positive : 0 < N) (target : Fin N) :
    (∑' k : ℕ, finiteProbability (fairBitRetryLastEvent k target)) = 1/(N:ℝ) := by
  simp_rw [fairBitRetryLastEvent_eq positive]
  exact uniformBitRejection_target_probability positive target

theorem fairBitRetry_total_mass {N : ℕ} (positive : 0 < N) :
    (∑ t : Fin N, ∑' k : ℕ, finiteProbability (fairBitRetryLastEvent k t)) = 1 := by
  have value (t : Fin N) := fairBitRetry_uniform positive t
  simp only [value, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
  exact div_self (Nat.cast_ne_zero.mpr positive.ne')

/-- Weight each first-success event by the bits the retry evaluator
actually reads on that event. -/
theorem fairBitRetry_expectedBits_eq {N : ℕ} (positive : 0 < N) :
    (∑' k : ℕ, (uniformProposalWidth N : ℝ)*(k+1)*
      (∑ t : Fin N, finiteProbability (fairBitRetryLastEvent k t))) = expectedRejectionBits N := by
  let total : ℝ := (2^uniformProposalWidth N : ℕ)
  let miss : ℝ := (total-N)/total
  let width : ℝ := uniformProposalWidth N
  have totalPos : 0 < total := by dsimp only [total]; positivity
  have nonneg : 0 ≤ miss := (uniformRejectionSeries positive).1
  have minor : miss ≤ 1/2 := (uniformRejectionSeries positive).2.1
  have lt : miss < 1 := by linarith
  have norm : ‖miss‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg nonneg] using lt
  have sum (k : ℕ) : (∑ t : Fin N, finiteProbability (fairBitRetryLastEvent k t)) = miss^k*(1-miss) := by
    simp_rw [fairBitRetryLastEvent_eq positive, rejectionAtBitAttempt_probability positive]
    change (∑ _t : Fin N, miss^k*(1/total)) = miss^k*(1-miss)
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [miss]
    field_simp [totalPos.ne']
    ring
  have weighted : (∑' k : ℕ, (k+1)*miss^k) = 1/(1-miss)^2 := by
    simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
      tsum_choose_mul_geometric_of_norm_lt_one 1 norm
  have denom : 1-miss ≠ 0 := by linarith
  simp_rw [sum]
  calc
    _ = (width*(1-miss)) * (∑' k : ℕ, (k+1)*miss^k) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring
    _ = width * (∑' k : ℕ, miss^k) := by
      rw [weighted, tsum_geometric_of_lt_one nonneg lt]
      field_simp [denom]
    _ = _ := rfl

/-- On a specified vector of attempt counts, run the retry evaluator on
independent finite bit words for every coordinate. -/
noncomputable def jointFairBitRetryEvent {I : Type*} [Fintype I] [DecidableEq I]
    (N attempts : I → ℕ) (target : ∀ i, Fin (N i)) :
    Finset (∀ i, Fin (attempts i+1) → Fin (uniformProposalWidth (N i)) → Bool) := by
  classical
  exact univ.filter fun bits => ∀ i, bits i ∈ fairBitRetryLastEvent (attempts i) (target i)

theorem jointFairBitRetryEvent_probability {I : Type*} [Fintype I] [DecidableEq I]
    (N attempts : I → ℕ) (target : ∀ i, Fin (N i)) :
    finiteProbability (jointFairBitRetryEvent N attempts target) =
      ∏ i, finiteProbability (fairBitRetryLastEvent (attempts i) (target i)) := by
  classical
  let e : {bits // bits ∈ jointFairBitRetryEvent N attempts target} ≃
      ∀ i, {words // words ∈ fairBitRetryLastEvent (attempts i) (target i)} :=
    { toFun := fun a i => ⟨a.1 i, (mem_filter.mp a.2).2 i⟩
      invFun := fun f => ⟨(fun i => (f i).1), mem_filter.mpr ⟨mem_univ _,fun i => (f i).2⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => funext fun _ => Subtype.ext rfl }
  have count : (jointFairBitRetryEvent N attempts target).card =
      ∏ i, (fairBitRetryLastEvent (attempts i) (target i)).card := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_pi]
    simp only [Fintype.card_coe]
  simp only [finiteProbability, count, Fintype.card_pi, Nat.cast_prod, prod_div_distrib]

/-- The product of the independent retry laws is the uniform law on
the corresponding array of indices. Empty coordinate sets are allowed. -/
theorem independentFairBitRetry_uniform {I : Type*} [Fintype I] [DecidableEq I] (N : I → ℕ)
    (positive : ∀ i, 0 < N i) (target : ∀ i, Fin (N i)) :
    (∏ i, ∑' k : ℕ, finiteProbability (fairBitRetryLastEvent k (target i))) =
      finiteProbability ({target} : Finset (∀ i, Fin (N i))) := by
  classical
  calc
    _ = ∏ i, (1/(N i : ℝ)) := prod_congr rfl fun i _ => fairBitRetry_uniform (positive i) (target i)
    _ = _ := by
      simp only [finiteProbability, card_singleton, Nat.cast_one, Fintype.card_pi, Fintype.card_fin,
        Nat.cast_prod, prod_div_distrib, prod_const_one]

variable {V : Type*} [LinearOrder V] [Fintype V]

local instance earlyBitAssignmentFintype (G : Arcs V) (height : ℕ) :
    Fintype (EarlySeedCoordinate G height → Fin ((forestScale G height).log2+1) → Bool) :=
  Fintype.ofEquiv (EarlyRoundSample G height) (earlySeedBitWords G height)

/-- The fair-word early seed and the independently retried hub and thin
coordinates give the uniform law on the three seeds of the actual run. -/
theorem completeSteinerSeed_uniform (G : Arcs V) (height : ℕ) (early : EarlyRoundSample G height)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) :
    let encode := Fintype.equivFin V
    let first := finiteProbability ({earlySeedBitWords G height early} : Finset _)
    let hubs := ∏ i, ∑' k : ℕ, finiteProbability (fairBitRetryLastEvent k (encode (draw i)))
    let edges := ∏ e, ∑' k : ℕ, finiteProbability (fairBitRetryLastEvent k (thin e))
    first * (hubs * edges) =
      finiteProbability ({(early, draw, thin)} : Finset (EarlyRoundSample G height × _ × ThinSample G)) := by
  classical
  dsimp only
  let I := Fin (completeSteinerHubCount V)
  let encode := Fintype.equivFin V
  have hub (i : I) : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨draw i⟩
  have arc (e : G) : 0 < G.card := card_pos.mpr ⟨e.val,e.property⟩
  change finiteProbability ({earlySeedBitWords G height early} : Finset _) *
    ((∏ i : I, ∑' k : ℕ, finiteProbability (fairBitRetryLastEvent k ((encode ∘ draw) i))) *
      ∏ e : G, ∑' k : ℕ, finiteProbability (fairBitRetryLastEvent k (thin e))) = _
  rw [independentFairBitRetry_uniform (fun _ : I => Fintype.card V) hub (encode ∘ draw),
    independentFairBitRetry_uniform (fun _ : G => G.card) arc thin]
  have bits : finiteProbability ({earlySeedBitWords G height early} : Finset _) =
      finiteProbability ({early} : Finset (EarlyRoundSample G height)) := by
    simp only [finiteProbability, card_singleton, ← Fintype.card_congr (earlySeedBitWords G height)]
  have indices : finiteProbability ({encode ∘ draw} : Finset (I → Fin (Fintype.card V))) =
      finiteProbability ({draw} : Finset (I → V)) := by
    simp only [finiteProbability, card_singleton,
      ← Fintype.card_congr (Equiv.arrowCongr (Equiv.refl I) encode)]
  rw [bits,indices, ← finiteProbability_product ({draw} : Finset (I → V)) {thin},
    ← finiteProbability_product ({early} : Finset (EarlyRoundSample G height))]
  simp

end OnlineReachabilityPreservers
