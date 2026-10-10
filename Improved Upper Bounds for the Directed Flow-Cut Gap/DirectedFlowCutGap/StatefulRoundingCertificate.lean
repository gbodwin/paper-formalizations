import DirectedFlowCutGap.StatefulBoundedRoundingQuality
import DirectedFlowCutGap.BinaryRetainedEntryCost

/-!
# Joint validity, declared charge, and quality for one actual stateful output

The joint event is measured on the actual returned record and physical ledger.
Every supported result is a valid cut and obeys the reached-width, retained
counter, and total repeated-charge bounds. The remaining failure event is
therefore exactly the selected-size event, with the concrete bounded-bit
probability bound. No independence of full records or cost metadata is used.

Operation charges retain their existing component model. This certificate
does not implement physical reference allocation, a whole-graph bit-storage
simulation, or the remaining weighted oracle/provider construction.
-/
namespace DirectedFlowCutGap.StatefulRoundingCertificate
noncomputable section
open StatefulSamplerProjection EncodedRoundingEntry EncodedRoundingRepetition
variable {n : ℕ} {S : Type}

theorem repeat_valid (draw : StateT S PMF (Output n)) (extra : ℕ)
    (Valid : Output n → Prop)
    (hvalid : ∀ s o, o ∈ (draw.run s).support → Valid o.1)
    (state : S) {out : Result n × S}
    (hout : out ∈ ((repeatDraws draw extra).run state).support) : Valid out.1.selected := by
  have hs : ∀ k s (b : Batch n × S), b ∈ ((drawMany draw k).run s).support →
      ∀ o ∈ b.1.outputs, Valid o := by
    intro k
    induction k with
    | zero =>
        intro s b hb
        have he := (PMF.mem_support_pure_iff _ _).mp hb
        subst b
        simp only [List.not_mem_nil,false_implies,implies_true]
    | succ k ih =>
        intro s b hb
        change b ∈ (PMF.bind _ _).support at hb
        obtain ⟨first,hfirst,hb⟩ := (PMF.mem_support_bind_iff _ _ _).mp hb
        obtain ⟨tail,htail,hb⟩ := (PMF.mem_support_bind_iff _ _ _).mp hb
        have he := (PMF.mem_support_pure_iff _ _).mp hb
        subst b
        intro o ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact hvalid s first hfirst
        · exact ih first.2 tail htail o ho
  change out ∈ (PMF.bind _ _).support at hout
  obtain ⟨first,hfirst,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨rest,hrest,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  rcases List.mem_cons.mp (select_member first.1 rest.1.outputs) with h | h
  · rw [h]
    exact hvalid state first hfirst
  · exact hs extra first.2 rest hrest _ h

open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape BinaryRetainedTapeCost
open BinaryRetainedRoundingCost BinaryRetainedEntryCost RetainedGridState
open EncodedIntegerShortestPaths BinaryWeightedSamplingLaw FiniteAmplification
open scoped NNReal
variable {L : ℕ}

theorem entry_valid [NeZero L] (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (state : Ledger)
    {out : Output n × Ledger}
    (hout : out ∈ ((EncodedAllRegimeRounding.run
      (callback fairBit fuel cutoff hcut hL) adjacency hL).run state).support) :
    IsIntegralCut (graph adjacency) out.1.vertices.toFinset
      (CandidateSchedule.unweightedDemands (graph adjacency) (L : ℝ≥0) : Set (Pair n)) := by
  have ho : out.1 ∈ (observe (EncodedAllRegimeRounding.run
      (callback fairBit fuel cutoff hcut hL) adjacency hL) state).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨out,hout,rfl⟩
  have hc : out.1.vertices.toFinset ∈ ((observe (EncodedAllRegimeRounding.run
      (callback fairBit fuel cutoff hcut hL) adjacency hL) state).map
        (fun o => o.vertices.toFinset)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨out.1,ho,rfl⟩
  rw [AllRegimeBoundedTapeLaw.cut_law fuel cutoff hcut adjacency hL state] at hc
  have hi := FiniteDrawTrees.actual_support_subset_ideal (value fuel)
    (AllRegimeBoundedTapeLaw.tree adjacency hL) hc
  rw [AllRegimeBoundedTapeLaw.tree_ideal] at hi
  exact IntegerClosureAsymptotic.allRegimeLaw_valid (graph adjacency) L hL
    (CandidateEnumeration.make n L).network.enumeration hi

theorem run_valid [NeZero L] (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (extra : ℕ) (state : Ledger)
    {out : Result n × Ledger}
    (hout : out ∈ ((EncodedRoundingRepetition.run
      (callback fairBit fuel cutoff hcut hL) adjacency hL extra).run state).support) :
    IsIntegralCut (graph adjacency) out.1.selected.vertices.toFinset
      (CandidateSchedule.unweightedDemands (graph adjacency) (L : ℝ≥0) : Set (Pair n)) := by
  exact repeat_valid
    (EncodedAllRegimeRounding.run (callback fairBit fuel cutoff hcut hL) adjacency hL) extra
    (fun o => IsIntegralCut (graph adjacency) o.vertices.toFinset
      (CandidateSchedule.unweightedDemands (graph adjacency) (L : ℝ≥0) : Set (Pair n)))
    (fun s o ho => entry_valid fuel cutoff hcut adjacency hL s ho) state hout

/-- A predicate on the entire actual result/ledger pair. The sampling field is
that of all repeated draws, not just that of the selected sample. -/
def Certificate (fuel cutoff : Bits) (adjacency : PairFlags n) (L extra : ℕ)
    (state : Ledger) (out : Result n × Ledger) : Prop :=
  let C := totalCallbacks n extra
  let K := commonCharge n fuel cutoff (ledgerWidth state) C
  IsIntegralCut (graph adjacency) out.1.selected.vertices.toFinset
      (CandidateSchedule.unweightedDemands (graph adjacency) (L : ℝ≥0) : Set (Pair n)) ∧
    ledgerWidth out.2 ≤ reachedWidth n fuel cutoff (ledgerWidth state) C ∧
    value out.2.draws ≤ value state.draws+BinaryRetainedTapeCost.drawBudget n*C ∧
    out.2.operations=state.operations+out.1.sampling ∧
    out.1.sampling ≤ C*K ∧
    out.1.operations ≤ (extra+1)*(EncodedAllRegimeRounding.operationBound n K+4*n+28)+10

theorem run_certificate [NeZero L] (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (extra : ℕ) (state : Ledger)
    {out : Result n × Ledger}
    (hout : out ∈ ((EncodedRoundingRepetition.run
      (callback fairBit fuel cutoff hcut hL) adjacency hL extra).run state).support) :
    Certificate fuel cutoff adjacency L extra state out :=
  ⟨run_valid fuel cutoff hcut adjacency hL extra state hout,
    BinaryRetainedEntryCost.run_bound fairBit fuel cutoff hcut adjacency hL extra state hout⟩

/-- The joint bad event on the full returned pair has the same probability
as the selected-size bad event. Validity and charge hold on every sample path. -/
theorem joint_failure_bound [NeZero L] (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (extra threshold : ℕ) (state : Ledger)
    (ht : 0<threshold)
    (hfuel : FairBitConfidence.trials (AllRegimeBoundedTapeLaw.drawBudget n) 2 ≤ value fuel)
    (he : expectedCost
      (IntegerClosureAsymptotic.allRegimeLaw (graph adjacency) L hL
        (CandidateEnumeration.make n L).network.enumeration)
      (fun X => (X.card : ℝ)) ≤ (threshold : ℝ)/2) :
    ((((EncodedRoundingRepetition.run
      (callback fairBit fuel cutoff hcut hL) adjacency hL extra).run state).toOuterMeasure
        {out | ¬ (Certificate fuel cutoff adjacency L extra state out ∧
          out.1.selected.vertices.length ≤ threshold)}).toReal) ≤ ((3 : ℝ)/4)^(extra+1) := by
  let μ := (EncodedRoundingRepetition.run
    (callback fairBit fuel cutoff hcut hL) adjacency hL extra).run state
  have hevent : μ.toOuterMeasure
      {out | ¬ (Certificate fuel cutoff adjacency L extra state out ∧
        out.1.selected.vertices.length ≤ threshold)} =
      μ.toOuterMeasure {out | threshold < out.1.selected.vertices.length} := by
    apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
    ext out
    by_cases hs : out ∈ μ.support
    · have hc := run_certificate fuel cutoff hcut adjacency hL extra state hs
      simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,hs,hc,true_and,and_true,not_le]
    · simp only [Set.mem_inter_iff,hs,and_false]
  change (μ.toOuterMeasure _).toReal ≤ _
  rw [hevent]
  have hp := StatefulBoundedRoundingQuality.repeated_three_quarter_bound
    fuel cutoff hcut adjacency hL extra threshold state ht hfuel he
  change ((μ.map Prod.fst).toOuterMeasure _).toReal ≤ _ at hp
  rw [PMF.toOuterMeasure_map_apply] at hp
  exact hp

private theorem three_quarter_le_half (k : ℕ) :
    ((3 : ℝ)/4)^(3*k+1) ≤ ((1 : ℝ)/2)^k := by
  calc
    _ ≤ ((3 : ℝ)/4)^(3*k) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = (((3 : ℝ)/4)^3)^k := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by norm_num) _

/-- A source-shaped uniform guarantee for the same actual output and ledger.
The size constant is fixed first; 3*k+1 executed entries give failure at most
2^(-k). This prices all repetitions in the declared charge predicate. -/
theorem uniform_joint_confidence :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
      ∀ (n L : ℕ) [NeZero L] (fuel cutoff : Bits) (_hcut : value cutoff=L)
        (adjacency : PairFlags n) (hL : 0<L) (k : ℕ) (state : Ledger)
        (_hfuel : FairBitConfidence.trials (AllRegimeBoundedTapeLaw.drawBudget n) 2 ≤ value fuel),
        let threshold := Nat.ceil (2*max 1
          (C*(n : ℝ)^ε*AdaptiveCost.sizeFactor (Fin n) (L : ℝ≥0)))
        ((((EncodedRoundingRepetition.run
          (callback fairBit fuel cutoff _hcut hL) adjacency hL (3*k)).run state).toOuterMeasure
            {out | ¬ (Certificate fuel cutoff adjacency L (3*k) state out ∧
              out.1.selected.vertices.length ≤ threshold)}).toReal) ≤ ((1 : ℝ)/2)^k := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := IntegerClosureAsymptotic.allRegimeLaw_expected_uniform ε hε
  refine ⟨C,hC,?_⟩
  intro n L _ fuel cutoff hcut adjacency hL k state hfuel
  let B := C*(n : ℝ)^ε*AdaptiveCost.sizeFactor (Fin n) (L : ℝ≥0)
  have hb : (2*max 1 B : ℝ) ≤ Nat.ceil (2*max 1 B) := Nat.le_ceil _
  have hm : (1 : ℝ) ≤ max 1 B := le_max_left _ _
  have ht : 0<Nat.ceil (2*max 1 B) := by
    have ht' : (0 : ℝ)<Nat.ceil (2*max 1 B) := by linarith
    exact_mod_cast ht'
  have he := hbound (Fin n) (graph adjacency) L hL
    (CandidateEnumeration.make n L).network.enumeration
  simp only [Fintype.card_fin] at he
  have hbm : B ≤ max 1 B := le_max_right _ _
  have hexpected : expectedCost
      (IntegerClosureAsymptotic.allRegimeLaw (graph adjacency) L hL
        (CandidateEnumeration.make n L).network.enumeration)
      (fun X => (X.card : ℝ)) ≤ (Nat.ceil (2*max 1 B) : ℝ)/2 := by
    change _ ≤ B at he
    linarith
  exact (joint_failure_bound fuel cutoff hcut adjacency hL (3*k) _ state ht hfuel hexpected).trans
    (three_quarter_le_half k)

end
end DirectedFlowCutGap.StatefulRoundingCertificate
