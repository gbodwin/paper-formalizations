import DirectedFlowCutGap.BinaryRetainedEntryCost

/-!
# Transport of actual finite-source executions into full-output PMF support

This relation is a proof of reachable support, not a runtime-cost rule for an
arbitrary host function. Every application below follows a named actual body.
It retains the full binary outputs, charges and physical ledger, unlike the
index-only observation used by the sampling-law refinement. A deterministic
source may choose each reached bit arbitrarily: a full-support Boolean PMF
contains the same finite execution path.

The final theorem applies the existing cost bound to that exact returned
record. The StateM source is executed once, and its returned state is retained.
The fixed finite-list reader consumes a head, or returns false at exhaustion.
The theorem does not price an arbitrary expensive user-supplied StateM action;
the declared bit-request primitive and outstanding representation costs keep
their existing scope. No ideal tape law or iid cost-record law is assumed.
-/
namespace DirectedFlowCutGap.BinaryRetainedPathwiseCost
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape BinaryRetainedTapeCost
open BinaryRetainedRoundingCost BinaryRetainedEntryCost RetainedGridState

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The entire actual returned value, including any stored counters, occurs
in the reference support. The source's final state is not replaced. -/
def Supports {σ A : Type} (actual : StateM σ A) (law : PMF A) : Prop :=
  ∀ s, (actual.run s).1 ∈ law.support

theorem supports_pure {σ A : Type} (a : A) :
    Supports (pure a : StateM σ A) (pure a : PMF A) := by
  intro s
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem supports_bind {σ A B : Type} {actual : StateM σ A} {law : PMF A}
    {f : A → StateM σ B} {g : A → PMF B}
    (h : Supports actual law) (ht : ∀ a, Supports (f a) (g a)) :
    Supports (actual >>= f) (law >>= g) := by
  intro s
  change ((f (actual.run s).1).run (actual.run s).2).1 ∈ (law >>= g).support
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨(actual.run s).1,h s,ht _ _⟩

theorem supports_map {σ A B : Type} (f : A → B)
    {actual : StateM σ A} {law : PMF A} (h : Supports actual law) :
    Supports (f <$> actual) (f <$> law) := by
  intro s
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(actual.run s).1,h s,rfl⟩

/-- Paired support through the actual StateT bind; physical metadata is not
discarded or sampled independently of the result. -/
def StateSupports {σ A : Type} (actual : StateT Ledger (StateM σ) A)
    (law : StateT Ledger PMF A) : Prop := ∀ s, Supports (actual.run s) (law.run s)

theorem state_pure {σ A : Type} (a : A) :
    StateSupports (pure a : StateT Ledger (StateM σ) A)
      (pure a : StateT Ledger PMF A) := fun _ => supports_pure _

theorem state_bind {σ A B : Type} {actual : StateT Ledger (StateM σ) A}
    {law : StateT Ledger PMF A} {f : A → StateT Ledger (StateM σ) B}
    {g : A → StateT Ledger PMF B}
    (h : StateSupports actual law) (ht : ∀ a, StateSupports (f a) (g a)) :
    StateSupports (actual >>= f) (law >>= g) := by
  intro s
  exact supports_bind (h s) (fun a => ht a.1 a.2)

theorem state_map {σ A B : Type} (f : A → B)
    {actual : StateT Ledger (StateM σ) A} {law : StateT Ledger PMF A}
    (h : StateSupports actual law) : StateSupports (f <$> actual) (f <$> law) := by
  intro s
  exact supports_bind (h s) (fun a => supports_pure (f a.1,a.2))

variable {σ : Type} (bit : StateM σ Bool) (chance : PMF Bool)
variable (hbit : Supports bit chance)

-- This declared primitive-support hypothesis must be included in each transport helper.
include hbit

/-- Recurse through the actual binary-controlled word routine. In particular,
the literal word padding and its returned instruction count are preserved. -/
theorem word_support (count : Bits) :
    Supports (BinaryRandomWord.word bit count) (BinaryRandomWord.word chance count) := by
  have aux : ∀ N, ∀ c : Bits, value c=N →
      Supports (BinaryRandomWord.word bit c) (BinaryRandomWord.word chance c) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro c hc
      conv_lhs => rw [BinaryRandomWord.word]
      conv_rhs => rw [BinaryRandomWord.word]
      split_ifs with hz
      · exact supports_pure _
      · have hv : 0<value c := Nat.pos_of_ne_zero
          (fun h => hz ((isZero_spec c).1.mpr h))
        have hpred := (predecessor_spec c).1
        have ht := ih (value (predecessor c).1) (by rw [hpred,← hc]; omega)
          (predecessor c).1 rfl
        apply supports_bind hbit
        intro b
        exact supports_bind ht (fun r => supports_pure _)
  exact aux (value count) count rfl

/-- Recurse through the same rejection branches, including the exhausted
default. This keeps steps, raw counters and index bytes, not only observe. -/
theorem draw_support (bound fuel : Bits) (positive : 0<value bound) :
    Supports (BinaryBoundedSampler.draw bit bound positive fuel)
      (BinaryBoundedSampler.draw chance bound positive fuel) := by
  have aux : ∀ N, ∀ f : Bits, value f=N →
      Supports (BinaryBoundedSampler.draw bit bound positive f)
        (BinaryBoundedSampler.draw chance bound positive f) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro f hf
      conv_lhs => rw [BinaryBoundedSampler.draw]
      conv_rhs => rw [BinaryBoundedSampler.draw]
      split_ifs with hz
      · exact supports_pure _
      · have hv : 0<value f := Nat.pos_of_ne_zero
          (fun h => hz ((isZero_spec f).1.mpr h))
        apply supports_bind (word_support bit chance hbit _)
        intro x
        dsimp only
        split_ifs with hx
        · exact supports_pure _
        · have hpred := (predecessor_spec f).1
          have ht := ih (value (predecessor f).1) (by rw [hpred,← hf]; omega)
            (predecessor f).1 rfl
          exact supports_bind ht (fun r => supports_pure _)
  exact aux (value fuel) fuel rfl

theorem tracked_support (bound fuel : Bits) (positive : 0<value bound) (s : Ledger) :
    Supports ((trackedDraw bit bound positive fuel).run s)
      ((trackedDraw chance bound positive fuel).run s) :=
  supports_map (fun r => (r,record s r)) (draw_support bit chance hbit bound fuel positive)

theorem drawIndex_support (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) :
    Supports (BinaryRetainedTape.drawIndex bit fuel bound hb hN s)
      (BinaryRetainedTape.drawIndex chance fuel bound hb hN s) := by
  unfold BinaryRetainedTape.drawIndex
  exact supports_bind (tracked_support bit chance hbit bound fuel (by omega) s)
    (fun r => supports_pure _)

theorem permutation_support (fuel : Bits) {A : Type} (xs : List A)
    (bound : Bits) (hb : value bound=xs.length) (s : Ledger) :
    Supports (permutation bit fuel xs bound hb s) (permutation chance fuel xs bound hb s) := by
  induction xs generalizing bound s with
  | nil => exact supports_pure _
  | cons x xs ih =>
      simp only [permutation]
      apply supports_bind (drawIndex_support bit chance hbit fuel bound hb (by simp) s)
      intro j
      apply supports_bind (ih _ _ _)
      intro t
      exact supports_pure _

theorem cells_support (fuel cutoff : Bits) {L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) {A : Type} (xs : List A) (s : Ledger) :
    Supports (cells bit fuel cutoff hcut hL xs s) (cells chance fuel cutoff hcut hL xs s) := by
  induction xs generalizing s with
  | nil => exact supports_pure _
  | cons x xs ih =>
      simp only [cells]
      apply supports_bind (drawIndex_support bit chance hbit fuel cutoff hcut hL s)
      intro j
      exact supports_bind (ih j.2) (fun t => supports_pure _)

theorem tape_support (fuel cutoff : Bits) {L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) {A : Type} (xs : List A) (bound : Bits)
    (hb : value bound=xs.length) (s : Ledger) :
    Supports (tape bit fuel cutoff hcut hL xs bound hb s)
      (tape chance fuel cutoff hcut hL xs bound hb s) := by
  unfold tape
  apply supports_bind (permutation_support bit chance hbit fuel xs bound hb s)
  intro p
  exact supports_bind (cells_support bit chance hbit fuel cutoff hcut hL xs p.2)
    (fun c => supports_pure _)

theorem sampleTape_support (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : PairFlags n) (s : Ledger) :
    Supports (sampleTape bit fuel cutoff hcut hL a s)
      (sampleTape chance fuel cutoff hcut hL a s) := by
  unfold sampleTape
  exact supports_bind (tape_support bit chance hbit fuel cutoff hcut hL _ _ _ _)
    (fun r => supports_pure _)

theorem callback_support (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : PairFlags n) :
    StateSupports (callback bit fuel cutoff hcut hL a) (callback chance fuel cutoff hcut hL a) := by
  intro s
  unfold callback StateT.run
  exact supports_bind (sampleTape_support bit chance hbit fuel cutoff hcut hL a
    {s with operations := 0}) (fun r => supports_pure _)

section Controller
open IntegerAdaptiveExecution EncodedIntegerShortestPaths EncodedRoundingState
variable {n L : ℕ} (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
variable (horder : F.base.enumeration.vertices=List.finRange n) (hL : 0<L)
variable {demands : Finset (Pair n)}
local notation "H" => EncodedRoundingState.Witness (demands := demands) adjacency F hL

theorem execute_support (fuel cutoff : Bits) (hcut : value cutoff=L)
    (R restartFuel epochs : ℕ) (c : Cache H) :
    StateSupports (EncodedSampledRounding.executeSampled adjacency F horder hL
      (callback bit fuel cutoff hcut hL) R restartFuel epochs c)
      (EncodedSampledRounding.executeSampled adjacency F horder hL
        (callback chance fuel cutoff hcut hL) R restartFuel epochs c) := by
  induction epochs generalizing c with
  | zero => exact state_pure _
  | succ epochs ih =>
      simp only [EncodedSampledRounding.executeSampled]
      split
      · exact state_pure _
      · apply state_bind (callback_support bit chance hbit fuel cutoff hcut hL _)
        intro t
        exact state_map _ (ih _)

theorem runSampled_support (fuel cutoff : Bits) (hcut : value cutoff=L)
    (R restartFuel epochs : ℕ) (st : Code (graph adjacency) demands L) :
    StateSupports (EncodedSampledRounding.runSampled adjacency F horder hL
      (callback bit fuel cutoff hcut hL) R restartFuel epochs st)
      (EncodedSampledRounding.runSampled adjacency F horder hL
        (callback chance fuel cutoff hcut hL) R restartFuel epochs st) := by
  unfold EncodedSampledRounding.runSampled
  exact state_map _ (execute_support bit chance hbit adjacency F horder hL
    fuel cutoff hcut R restartFuel epochs _)

end Controller

theorem entry_support (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) :
    StateSupports (EncodedRoundingEntry.run (callback bit fuel cutoff hcut hL) adjacency hL)
      (EncodedRoundingEntry.run (callback chance fuel cutoff hcut hL) adjacency hL) := by
  unfold EncodedRoundingEntry.run
  exact state_map _ (runSampled_support bit chance hbit adjacency _ _ hL fuel cutoff hcut _ _ _ _)

set_option maxHeartbeats 1000000 in
theorem allRegime_support (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) :
    StateSupports (EncodedAllRegimeRounding.run (callback bit fuel cutoff hcut hL) adjacency hL)
      (EncodedAllRegimeRounding.run (callback chance fuel cutoff hcut hL) adjacency hL) := by
  by_cases hn : n=0
  · simp only [EncodedAllRegimeRounding.run,hn,ite_true]
    exact state_pure _
  · by_cases hLn : L ≤ n
    · by_cases hHard : 64*(EncodedEpochParameters.compute n).cap ≤ L ∧ n ≤ L^3
      · simp only [EncodedAllRegimeRounding.run,hn,ite_false,hLn,ite_true,hHard]
        exact state_map _ (entry_support bit chance hbit fuel cutoff hcut adjacency hL)
      · simp only [EncodedAllRegimeRounding.run,hn,ite_false,hLn,ite_true,hHard]
        exact state_pure _
    · simp only [EncodedAllRegimeRounding.run,hn,ite_false,hLn]
      exact state_pure _

theorem drawMany_support (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (entries : ℕ) :
    StateSupports (EncodedRoundingRepetition.drawMany
      (EncodedAllRegimeRounding.run (callback bit fuel cutoff hcut hL) adjacency hL) entries)
      (EncodedRoundingRepetition.drawMany
        (EncodedAllRegimeRounding.run (callback chance fuel cutoff hcut hL) adjacency hL) entries) := by
  induction entries with
  | zero => exact state_pure _
  | succ entries ih =>
      simp only [EncodedRoundingRepetition.drawMany]
      exact state_bind (allRegime_support bit chance hbit fuel cutoff hcut adjacency hL)
        (fun first => state_bind ih (fun tail => state_pure _))

/-- Full repeated output and final physical ledger, with all charge fields.
No independent distribution is assigned to those history-dependent records. -/
theorem repeat_support (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (extra : ℕ) :
    StateSupports (EncodedRoundingRepetition.run (callback bit fuel cutoff hcut hL) adjacency hL extra)
      (EncodedRoundingRepetition.run (callback chance fuel cutoff hcut hL) adjacency hL extra) := by
  unfold EncodedRoundingRepetition.run EncodedRoundingRepetition.repeatDraws
  exact state_bind (allRegime_support bit chance hbit fuel cutoff hcut adjacency hL)
    (fun first => state_bind (drawMany_support bit chance hbit fuel cutoff hcut adjacency hL extra)
      (fun rest => state_pure _))

end

/-- A fixed finite source: no requests are made except by the actual body.
Exhaustion supplies false and retains the empty suffix. -/
def next : StateM Bits Bool := fun xs =>
  match xs with
  | [] => (false,[])
  | b::bs => (b,bs)

theorem next_suffix (xs : Bits) : (next.run xs).2=xs.drop 1 := by
  cases xs <;> rfl

noncomputable section

theorem full_support {σ : Type} (bit : StateM σ Bool) :
    Supports bit (PMF.uniformOfFintype Bool) := by
  intro s
  exact PMF.mem_support_uniformOfFintype _

/-- Every actual source path is bounded by the same closed repeated-entry
charge. The exact returned source state is still the second component of
executed; this theorem neither re-executes nor replaces it. -/
theorem pathwise_bound {σ : Type} (bit : StateM σ Bool) (fuel cutoff : Bits)
    {n L : ℕ} [NeZero L] (hcut : value cutoff=L) (adjacency : PairFlags n)
    (hL : 0<L) (extra : ℕ) (ledger : Ledger) (source : σ) :
    let executed := ((EncodedRoundingRepetition.run (callback bit fuel cutoff hcut hL)
      adjacency hL extra).run ledger).run source
    let C := totalCallbacks n extra
    let K := commonCharge n fuel cutoff (ledgerWidth ledger) C
    ledgerWidth executed.1.2 ≤ reachedWidth n fuel cutoff (ledgerWidth ledger) C ∧
      value executed.1.2.draws ≤ value ledger.draws+drawBudget n*C ∧
      executed.1.2.operations=ledger.operations+executed.1.1.sampling ∧
      executed.1.1.sampling ≤ C*K ∧
      executed.1.1.operations ≤ (extra+1)*(EncodedAllRegimeRounding.operationBound n K+4*n+28)+10 := by
  have hs := repeat_support bit (PMF.uniformOfFintype Bool) (full_support bit)
    fuel cutoff hcut adjacency hL extra ledger source
  exact BinaryRetainedEntryCost.run_bound (PMF.uniformOfFintype Bool) fuel cutoff hcut
    adjacency hL extra ledger hs

/-- Specialization to the fixed literal-bit source. Metadata and the returned
suffix are those of the single actual nested-StateT execution. -/
theorem finite_source_support (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (extra : ℕ) (ledger : Ledger) (source : Bits) :
    (((EncodedRoundingRepetition.run (callback next fuel cutoff hcut hL)
      adjacency hL extra).run ledger).run source).1 ∈
      ((EncodedRoundingRepetition.run
        (callback (PMF.uniformOfFintype Bool) fuel cutoff hcut hL)
        adjacency hL extra).run ledger).support :=
  repeat_support next (PMF.uniformOfFintype Bool) (full_support next)
    fuel cutoff hcut adjacency hL extra ledger source

end
end DirectedFlowCutGap.BinaryRetainedPathwiseCost
