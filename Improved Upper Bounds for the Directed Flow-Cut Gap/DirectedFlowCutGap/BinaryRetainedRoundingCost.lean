import DirectedFlowCutGap.BinaryRetainedTapeCost
import DirectedFlowCutGap.EncodedSampledRounding

/-!
# Reached-ledger cost of the existing sampled rounding interpreter

The executable program is EncodedSampledRounding itself, instantiated with
StateT Ledger PMF and the actual binary tape callback. These proofs do not
freeze the incoming ledger, replay a tape, or reset physical metadata. A ghost
callback prefix supplies the finite common width used by each reached draw.
The ledger's operation field telescopes to the controller's total sampling
field; the controller's deterministic work is charged separately.

This component concerns the exact PMF-supported stateful computation. It does
not yet lift costs to an arbitrary finite bit stream, certify the outstanding
representation bodies, or identify bounded rejection with ideal sampling.
-/
namespace DirectedFlowCutGap.BinaryRetainedRoundingCost
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape BinaryRetainedTapeCost
open RetainedGridState IntegerAdaptiveExecution RetainedSampledExecution
open scoped NNReal
open EncodedSampledRounding EncodedIntegerShortestPaths EncodedRoundingState

set_option backward.isDefEq.respectTransparency false

/-- A bound on stored physical metadata after j actual tape callbacks. -/
def reachedWidth (n : ℕ) (fuel cutoff : Bits) (S j : ℕ) : ℕ :=
  S+j*drawBudget n*delta (boundWidth n cutoff) fuel

/-- One common charge, derived from a reserved total callback budget. -/
def commonCharge (n : ℕ) (fuel cutoff : Bits) (S C : ℕ) : ℕ :=
  callbackBound n fuel cutoff (reachedWidth n fuel cutoff S C)

theorem reachedWidth_mono (n : ℕ) (fuel cutoff : Bits) (S : ℕ)
    {j k : ℕ} (h : j ≤ k) :
    reachedWidth n fuel cutoff S j ≤ reachedWidth n fuel cutoff S k := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)) S

theorem reachedWidth_succ (n : ℕ) (fuel cutoff : Bits) (S j : ℕ) :
    reachedWidth n fuel cutoff S (j+1)=reachedWidth n fuel cutoff S j+
      drawBudget n*delta (boundWidth n cutoff) fuel := by
  unfold reachedWidth
  ring

noncomputable section

/-- The same supported callback witness gives both the prefix advance and
the common charge. No uniform cost premise is supplied by the caller. -/
theorem callback_step (bit : PMF Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger)
    (S C j : ℕ) (hj : j ≤ C)
    (hs : ledgerWidth s ≤ reachedWidth n fuel cutoff S j)
    {out : (RetainedTapeInput.Tape L a × ℕ) × Ledger}
    (hout : out ∈ ((callback bit fuel cutoff hcut hL a).run s).support) :
    ledgerWidth out.2 ≤ reachedWidth n fuel cutoff S (j+1) ∧
      out.1.2 ≤ commonCharge n fuel cutoff S C ∧
      out.2.operations=s.operations+out.1.2 ∧
      value out.2.draws=value s.draws+2*Fintype.card ↥(remainingSet a) ∧
      value out.2.draws ≤ value s.draws+drawBudget n := by
  have hp := callback_bounds bit fuel cutoff hcut hL a s
    (reachedWidth n fuel cutoff S j) hs hout
  have hg := callback_bounds bit fuel cutoff hcut hL a s
    (reachedWidth n fuel cutoff S C)
    (hs.trans (reachedWidth_mono n fuel cutoff S hj)) hout
  exact ⟨by simpa only [reachedWidth_succ] using hp.1,hg.2.1,
    hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩

/-- All counts refer to the actual returned log and ledger. -/
structure Summary {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}
    {selector : FlexibleCandidateSchedule.FamilyProvider G D (L : ℝ≥0) → Prop}
    (H : ∃ P, selector P) (fuel cutoff : Bits) (S C j epochs : ℕ)
    (s : Ledger) (out : ChargedResult H × Ledger) : Prop where
  calls : out.1.logged.inputs.length ≤ epochs
  width : ledgerWidth out.2 ≤
    reachedWidth n fuel cutoff S (j+out.1.logged.inputs.length)
  draws_eq : value out.2.draws=value s.draws+
    RetainedExecutionLaw.primitiveDraws out.1.logged.inputs
  draws_le : RetainedExecutionLaw.primitiveDraws out.1.logged.inputs ≤
    drawBudget n*out.1.logged.inputs.length
  ledger_charge : out.2.operations=s.operations+out.1.sampling
  sampling : out.1.sampling ≤ out.1.logged.inputs.length*commonCharge n fuel cutoff S C
  work : out.1.operations ≤ EncodedRoundingRuntime.price n L out.1.logged.result.work+
    epochs*(EncodedTapeMaterialization.materializationBound n+16)+out.1.sampling+1

section Controller
variable {n L : ℕ}
variable (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
variable (horder : F.base.enumeration.vertices = List.finRange n) (hL : 0<L)
variable {demands : Finset (Pair n)}
local notation "H" => EncodedRoundingState.Witness (demands := demands) adjacency F hL
local notation "Q" => RetainedCandidateSolver.optimizer (demands := demands) adjacency F horder hL
local notation "Ccut" => EncodedRoundingInput.cutOracle F.base.enumeration adjacency hL

/-- This is just the defining equation of the existing StateT program. -/
theorem execute_zero (sample : (a : PairFlags n) →
    StateT Ledger PMF (RetainedTapeInput.Tape L a × ℕ))
    (R restartFuel : ℕ) (c : Cache H) (s : Ledger) :
    (EncodedSampledRounding.executeSampled adjacency F horder hL sample
      R restartFuel 0 c).run s =
    pure ((⟨⟨(EncodedRoundingRuntime.stabilize adjacency F horder hL R restartFuel c).1,[]⟩,
      (EncodedRoundingRuntime.stabilize adjacency F horder hL R restartFuel c).2,0⟩ :
      ChargedResult H),s) := rfl

/-- StateT's defining bind carries the actual returned ledger into the tail. -/
theorem execute_succ (sample : (a : PairFlags n) →
    StateT Ledger PMF (RetainedTapeInput.Tape L a × ℕ))
    (R restartFuel epochs : ℕ) (c : Cache H) (s : Ledger) :
    (EncodedSampledRounding.executeSampled adjacency F horder hL sample
      R restartFuel (epochs+1) c).run s =
    (let a := EncodedRoundingRuntime.stabilize adjacency F horder hL R restartFuel c
     if a.1.cache.optimal == 0 then pure ((⟨⟨a.1,[]⟩,a.2+4,0⟩ : ChargedResult H),s)
     else do
       let t ← (sample a.1.cache.state.data.remaining).run s
       let i := EncodedTapeMaterialization.materialize hL a.1.cache.state.data.remaining t.1.1
       let b := EncodedRoundingRuntime.scan adjacency F horder hL R a.1.cache.state.data.current
         i.1.cell i.1.order a.1.cache
       let d ← (EncodedSampledRounding.executeSampled adjacency F horder hL sample
         R restartFuel epochs b.1.cache).run t.2
       pure ((⟨RetainedSampledExecution.finish a.1 b.1 i.1 d.1.logged,
         a.2+t.1.2+i.2+b.2+d.1.operations+8,t.1.2+d.1.sampling⟩ : ChargedResult H),d.2)) := by
  simp only [EncodedSampledRounding.executeSampled]
  dsimp only
  split_ifs
  · rfl
  · congr 1
    funext t
    rcases t with ⟨t,s'⟩
    congr 1
    funext d
    rcases d with ⟨d,s''⟩
    rfl

/-- The local tape bound is used only at reached states. The incoming ghost
prefix plus the remaining epoch fuel reserves enough callback slots. -/
theorem execute_bounds (bit : PMF Bool) (fuel cutoff : Bits)
    (hcut : value cutoff=L) (R restartFuel epochs : ℕ) (c : Cache H)
    (S C j : ℕ) (s : Ledger) (hslots : j+epochs ≤ C)
    (hs : ledgerWidth s ≤ reachedWidth n fuel cutoff S j)
    {out : ChargedResult H × Ledger}
    (hout : out ∈ ((EncodedSampledRounding.executeSampled adjacency F horder hL
      (callback bit fuel cutoff hcut hL) R restartFuel epochs c).run s).support) :
    Summary H fuel cutoff S C j epochs s out := by
  induction epochs generalizing j c s out with
  | zero =>
      rw [execute_zero] at hout
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      refine ⟨by simp,?_,?_,?_,?_,?_,?_⟩
      · simpa only [List.length_nil,Nat.add_zero] using hs
      · simp only [RetainedExecutionLaw.primitiveDraws,Nat.add_zero]
      · simp only [RetainedExecutionLaw.primitiveDraws,List.length_nil,Nat.mul_zero,le_refl]
      · simp only [Nat.add_zero]
      · simp only [List.length_nil,zero_mul,le_refl]
      · simpa only [zero_mul,Nat.add_zero] using
          EncodedRoundingRuntime.stabilize_bound adjacency F horder hL R restartFuel c
  | succ epochs ih =>
      rw [execute_succ] at hout
      dsimp only at hout
      split_ifs at hout with hz
      · have he := (PMF.mem_support_pure_iff _ _).mp hout
        subst out
        have ha := EncodedRoundingRuntime.stabilize_bound adjacency F horder hL R restartFuel c
        refine ⟨by simp,?_,?_,?_,?_,?_,?_⟩
        · simpa only [List.length_nil,Nat.add_zero] using hs
        · simp only [RetainedExecutionLaw.primitiveDraws,Nat.add_zero]
        · simp only [RetainedExecutionLaw.primitiveDraws,List.length_nil,Nat.mul_zero,le_refl]
        · simp only [Nat.add_zero]
        · simp only [List.length_nil,zero_mul,le_refl]
        · dsimp only
          nlinarith
      · obtain ⟨t,ht,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
        obtain ⟨tail,htail,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
        have he := (PMF.mem_support_pure_iff _ _).mp hout
        subst out
        let a := EncodedRoundingRuntime.stabilize adjacency F horder hL R restartFuel c
        let i := EncodedTapeMaterialization.materialize hL a.1.cache.state.data.remaining t.1.1
        let b := EncodedRoundingRuntime.scan adjacency F horder hL R a.1.cache.state.data.current
          i.1.cell i.1.order a.1.cache
        have ht' := callback_step bit fuel cutoff hcut hL a.1.cache.state.data.remaining s
          S C j (by omega) hs ht
        have hd : Summary H fuel cutoff S C (j+1) epochs t.2 tail :=
          ih (c := b.1.cache) (j := j+1) (s := t.2) (by omega) ht'.1 htail
        have hdraws := hd.draws_eq
        have hdrawBound := hd.draws_le
        have hledger := hd.ledger_charge
        have hsampling := hd.sampling
        have hlen : i.1.order.length=Fintype.card ↥(remainingSet a.1.cache.state.data.remaining) := by
          change (EncodedTapeMaterialization.materialize hL a.1.cache.state.data.remaining t.1.1).1.order.length = _
          rw [EncodedTapeMaterialization.materialize_value]
          simpa only [Fintype.card_coe] using RetainedTapeInput.materialize_order_length hL
            a.1.cache.state.data.remaining t.1.1
        have hord : i.1.order.length ≤ n*n := by
          rw [hlen]
          exact RetainedDrawTrees.active_card_le _
        have ha := EncodedRoundingRuntime.stabilize_bound adjacency F horder hL R restartFuel c
        have hi := EncodedTapeMaterialization.materialize_bound hL a.1.cache.state.data.remaining t.1.1
        have hb := EncodedRoundingRuntime.scan_bound adjacency F horder hL R
          a.1.cache.state.data.current i.1.cell i.1.order a.1.cache
        refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
        · simpa only [RetainedSampledExecution.finish,List.length_cons] using Nat.succ_le_succ hd.calls
        · simpa only [RetainedSampledExecution.finish,List.length_cons,Nat.add_assoc,
            Nat.add_comm,Nat.add_left_comm] using hd.width
        · change value tail.2.draws=value s.draws+
            RetainedExecutionLaw.primitiveDraws (i.1::tail.1.logged.inputs)
          rw [RetainedExecutionLaw.primitiveDraws,hlen]
          omega
        · change RetainedExecutionLaw.primitiveDraws (i.1::tail.1.logged.inputs) ≤
            drawBudget n*(i.1::tail.1.logged.inputs).length
          rw [RetainedExecutionLaw.primitiveDraws,List.length_cons,Nat.mul_add,Nat.mul_one]
          have hlocal : 2*i.1.order.length ≤ drawBudget n := Nat.mul_le_mul_left 2 hord
          omega
        · change tail.2.operations=s.operations+(t.1.2+tail.1.sampling)
          omega
        · change t.1.2+tail.1.sampling ≤
            (i.1::tail.1.logged.inputs).length*commonCharge n fuel cutoff S C
          rw [List.length_cons,Nat.add_mul,one_mul]
          omega
        · change a.2+t.1.2+i.2+b.2+tail.1.operations+8 ≤ _
          simp only [RetainedSampledExecution.finish,EncodedRoundingRuntime.price_add]
          change a.2 ≤ EncodedRoundingRuntime.price n L a.1.work+1 at ha
          change i.2 ≤ EncodedTapeMaterialization.materializationBound n at hi
          change b.2 ≤ EncodedRoundingRuntime.price n L b.1.work+1 at hb
          nlinarith [hd.work]

/-- Initial refresh is a pure StateT map: it adds graph work, never sampler
ledger work. Thus the same reached-state and charge invariant survives it. -/
theorem run_bounds (bit : PMF Bool) (fuel cutoff : Bits)
    (hcut : value cutoff=L) (R restartFuel epochs : ℕ)
    (st : Code (graph adjacency) demands L) (S C j : ℕ) (s : Ledger)
    (hslots : j+epochs ≤ C) (hs : ledgerWidth s ≤ reachedWidth n fuel cutoff S j)
    {out : ChargedResult H × Ledger}
    (hout : out ∈ ((EncodedSampledRounding.runSampled adjacency F horder hL
      (callback bit fuel cutoff hcut hL) R restartFuel epochs st).run s).support) :
    Summary H fuel cutoff S C j epochs s out := by
  change out ∈ (((EncodedSampledRounding.executeSampled adjacency F horder hL
      (callback bit fuel cutoff hcut hL) R restartFuel epochs
      (EncodedRoundingState.refresh adjacency F horder hL st).1).run s) >>= _).support at hout
  obtain ⟨tail,htail,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  have h := execute_bounds adjacency F horder hL bit fuel cutoff hcut R restartFuel epochs
    (EncodedRoundingState.refresh adjacency F horder hL st).1 S C j s hslots hs htail
  refine ⟨h.calls,h.width,h.draws_eq,h.draws_le,h.ledger_charge,h.sampling,?_⟩
  have hr := EncodedRoundingState.refresh_bound adjacency F horder hL st
  have hw := h.work
  change (EncodedRoundingState.refresh adjacency F horder hL st).2+tail.1.operations+4 ≤
    EncodedRoundingRuntime.price n L ((refreshWork st).add tail.1.logged.result.work)+
      epochs*(EncodedTapeMaterialization.materializationBound n+16)+tail.1.sampling+1
  rw [EncodedRoundingRuntime.price_add]
  simp only [EncodedRoundingRuntime.price,refreshWork,Nat.one_mul,Nat.zero_mul,
    Nat.add_zero] at hw hr ⊢
  omega

/-- The support argument can keep arbitrary state effects. It prices no
arbitrary sampler: only membership in the full typed ideal tape support is
used here, independently of the concrete cost theorem above. -/
theorem reference_state_support [NeZero L] {σ : Type}
    (sample : (a : PairFlags n) → StateT σ PMF (RetainedTapeInput.Tape L a))
    (R restartFuel epochs : ℕ) (c : Cache H) (s : σ)
    {out : LoggedResult H × σ}
    (hout : out ∈ ((RetainedSampledExecution.executeSampled sample Q hL Ccut
      R restartFuel epochs c).run s).support) :
    out.1 ∈ (RetainedSampledExecution.executeSampled RetainedExecutionLaw.sampleTape
      Q hL Ccut R restartFuel epochs c).support := by
  induction epochs generalizing c s out with
  | zero =>
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | succ epochs ih =>
      have heq : (RetainedSampledExecution.executeSampled sample Q hL Ccut
          R restartFuel (epochs+1) c).run s =
          (let a := IntegerAdaptiveExecution.stabilize Q R restartFuel c
           if a.cache.optimal == 0 then pure ((⟨a,[]⟩ : LoggedResult H),s)
           else do
             let t ← (sample a.cache.state.data.remaining).run s
             let i := RetainedTapeInput.materialize hL a.cache.state.data.remaining t.1
             let b := IntegerAdaptiveExecution.scan Q hL Ccut R a.cache.state.data.current
               i.cell i.order a.cache
             let d ← (RetainedSampledExecution.executeSampled sample Q hL Ccut
               R restartFuel epochs b.cache).run t.2
             pure (RetainedSampledExecution.finish a b i d.1,d.2)) := by
        simp only [RetainedSampledExecution.executeSampled]
        dsimp only
        split_ifs
        · rfl
        · congr 1
          funext t
          rcases t with ⟨t,s'⟩
          congr 1
          funext d
          rcases d with ⟨d,s''⟩
          rfl
      rw [heq] at hout
      dsimp only at hout
      rw [RetainedSampledExecution.executeSampled]
      split_ifs at hout ⊢ with hz
      · have he := (PMF.mem_support_pure_iff _ _).mp hout
        subst out
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      · obtain ⟨t,_,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
        obtain ⟨tail,htail,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
        have he := (PMF.mem_support_pure_iff _ _).mp hout
        subst out
        refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨t.1,?_,?_⟩
        · rw [RetainedExecutionLaw.sampleTape,FiniteGridSampler.tapePMF_uniform]
          exact PMF.mem_support_uniformOfFintype _
        · exact (PMF.mem_support_bind_iff _ _ _).mpr
            ⟨tail.1,ih (c := _) (s := t.2) htail,(PMF.mem_support_pure_iff _ _).mpr rfl⟩

/-- The entire actual logged result stays in ideal support even though the
sampler carries history-dependent charges and biased bounded rejections. -/
theorem execute_support [NeZero L]
    (sample : (a : PairFlags n) → StateT Ledger PMF (RetainedTapeInput.Tape L a × ℕ))
    (R restartFuel epochs : ℕ) (c : Cache H) (s : Ledger)
    {out : ChargedResult H × Ledger}
    (hout : out ∈ ((EncodedSampledRounding.executeSampled adjacency F horder hL sample
      R restartFuel epochs c).run s).support) :
    out.1.logged ∈ (RetainedSampledExecution.executeSampled RetainedExecutionLaw.sampleTape
      Q hL Ccut R restartFuel epochs c).support := by
  have hm : (out.1.logged,out.2) ∈
      ((ChargedResult.logged <$> EncodedSampledRounding.executeSampled adjacency F horder hL
        sample R restartFuel epochs c).run s).support := by
    change (out.1.logged,out.2) ∈
      (((EncodedSampledRounding.executeSampled adjacency F horder hL sample
        R restartFuel epochs c).run s) >>= _).support
    exact (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨out,hout,(PMF.mem_support_pure_iff _ _).mpr rfl⟩
  rw [EncodedSampledRounding.execute_projectionM] at hm
  exact reference_state_support adjacency F horder hL (fun a => Prod.fst <$> sample a)
    R restartFuel epochs c s hm

/-- Initial refresh preserves the same provider and the actual reached ledger.
This support theorem is the input to the existing deterministic work envelope. -/
theorem run_support [NeZero L]
    (sample : (a : PairFlags n) → StateT Ledger PMF (RetainedTapeInput.Tape L a × ℕ))
    (R restartFuel epochs : ℕ) (st : Code (graph adjacency) demands L) (s : Ledger)
    {out : ChargedResult H × Ledger}
    (hout : out ∈ ((EncodedSampledRounding.runSampled adjacency F horder hL sample
      R restartFuel epochs st).run s).support) :
    out.1.logged ∈ (RetainedExecutionLaw.sampledRunLaw Q hL Ccut
      R restartFuel epochs st).support := by
  change out ∈ (((EncodedSampledRounding.executeSampled adjacency F horder hL
      sample R restartFuel epochs
      (EncodedRoundingState.refresh adjacency F horder hL st).1).run s) >>= _).support at hout
  obtain ⟨tail,htail,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  have h := execute_support adjacency F horder hL sample R restartFuel epochs
    (EncodedRoundingState.refresh adjacency F horder hL st).1 s htail
  rw [EncodedRoundingState.refresh_value] at h
  change _ ∈ (RetainedSampledExecution.executeSampled RetainedExecutionLaw.sampleTape Q hL Ccut
    R restartFuel epochs (RetainedGridState.refresh Q st) >>= _).support
  exact (PMF.mem_support_bind_iff _ _ _).mpr
    ⟨tail.1.logged,h,(PMF.mem_support_pure_iff _ _).mpr rfl⟩

end Controller
end
end DirectedFlowCutGap.BinaryRetainedRoundingCost
