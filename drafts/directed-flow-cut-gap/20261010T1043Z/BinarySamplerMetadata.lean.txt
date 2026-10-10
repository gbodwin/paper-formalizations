import DirectedFlowCutGap.BinarySamplerCost

/-!
# Retained binary metadata for the actual bounded-draw callback

The state records physical rejection exhaustion, total trials, consumed bits,
and actual bounded-draw calls. Each update uses the checked binary adders and
charges their work once. `trackedDraw` runs the actual sampler once and returns
its entire result, so metadata does not substitute a new data law or discard
source-state effects. These are component charge fields, not a complete graph
runtime theorem; tape construction, callback composition and representation
cost certificates remain separate joins.
-/
namespace DirectedFlowCutGap.BinarySamplerMetadata
open BinaryArithmetic BinaryBoundedSampler

structure Ledger where
  failed : Bool
  trials : Bits
  consumed : Bits
  draws : Bits
  operations : ℕ

def empty : Ledger := ⟨false,[],[],[],0⟩

/-- Preserve every bounded-draw result while updating the cumulative ledger.
The state stores binary counters; decoded naturals occur only in specifications. -/
def record {bound : Bits} (s : Ledger) (r : Output bound) : Ledger :=
  let t := BinaryArithmetic.add false s.trials r.trials
  let b := BinaryArithmetic.add false s.consumed r.consumed
  let d := BinaryArithmetic.increment true s.draws
  ⟨s.failed || r.failed,t.1,b.1,d.1,
    s.operations+r.steps+t.2+b.2+d.2+20⟩

@[simp] theorem record_failed {bound : Bits} (s : Ledger) (r : Output bound) :
    (record s r).failed = (s.failed || r.failed) := rfl

@[simp] theorem record_trials {bound : Bits} (s : Ledger) (r : Output bound) :
    value (record s r).trials = value s.trials + value r.trials := by
  simpa only [record,Bool.toNat_false,Nat.add_zero] using
    (BinaryArithmetic.add_spec false s.trials r.trials).1

@[simp] theorem record_consumed {bound : Bits} (s : Ledger) (r : Output bound) :
    value (record s r).consumed = value s.consumed + value r.consumed := by
  simpa only [record,Bool.toNat_false,Nat.add_zero] using
    (BinaryArithmetic.add_spec false s.consumed r.consumed).1

@[simp] theorem record_draws {bound : Bits} (s : Ledger) (r : Output bound) :
    value (record s r).draws = value s.draws + 1 := by
  simpa only [record,Bool.toNat_true] using
    (BinaryArithmetic.increment_spec true s.draws).1

theorem record_lengths {bound : Bits} (s : Ledger) (r : Output bound) :
    (record s r).trials.length ≤ max s.trials.length r.trials.length+1 ∧
      (record s r).consumed.length ≤ max s.consumed.length r.consumed.length+1 ∧
      (record s r).draws.length ≤ s.draws.length+1 := by
  exact ⟨(BinaryArithmetic.add_spec false s.trials r.trials).2.1,
    (BinaryArithmetic.add_spec false s.consumed r.consumed).2.1,
    (BinaryArithmetic.increment_spec true s.draws).2.1⟩

theorem record_charge {bound : Bits} (s : Ledger) (r : Output bound) :
    (record s r).operations ≤ s.operations+r.steps+
      16*(max s.trials.length r.trials.length+1)+
      16*(max s.consumed.length r.consumed.length+1)+8*(s.draws.length+1)+20 := by
  have ht := (BinaryArithmetic.add_spec false s.trials r.trials).2.2
  have hb := (BinaryArithmetic.add_spec false s.consumed r.consumed).2.2
  have hd := (BinaryArithmetic.increment_spec true s.draws).2.2
  dsimp only [record]
  omega

/-- One actual sampler invocation, with its complete output and one ledger update.
The supplied bit action stays in the original monad, retaining its effects. -/
def trackedDraw {M : Type → Type} [Monad M] (bit : M Bool)
    (bound : Bits) (positive : 0 < value bound) (fuel : Bits) :
    StateT Ledger M (Output bound) := fun s =>
  (fun r => (r,record s r)) <$> BinaryBoundedSampler.draw bit bound positive fuel

/-- Equality of the actual monadic computations, not merely returned-index laws. -/
theorem trackedDraw_value {M : Type → Type} [Monad M] [LawfulMonad M]
    (bit : M Bool) (bound : Bits) (positive : 0 < value bound)
    (fuel : Bits) (s : Ledger) :
    Prod.fst <$> (trackedDraw bit bound positive fuel).run s =
      BinaryBoundedSampler.draw bit bound positive fuel := by
  simp only [trackedDraw,StateT.run,Functor.map_map]
  exact id_map _

def updateBound (s : Ledger) (bound fuel : Bits) : ℕ :=
  BinarySamplerCost.instructionBound bound fuel+
    16*(max s.trials.length (value fuel)+1)+
    16*(max s.consumed.length (value fuel+bound.length+1)+1)+
    8*(s.draws.length+1)+20

noncomputable section

/-- Metadata bounds cover every supported physical outcome, including exhaustion. -/
theorem record_draw_charge (bit : PMF Bool) (bound fuel : Bits)
    (positive : 0 < value bound) (s : Ledger) {r : Output bound}
    (hr : r ∈ (BinaryBoundedSampler.draw bit bound positive fuel).support) :
    (record s r).operations ≤ s.operations+updateBound s bound fuel := by
  have hb := BinarySamplerCost.draw_bounded bit bound fuel positive hr
  have ht := max_le_max_left s.trials.length hb.1
  have hc := max_le_max_left s.consumed.length hb.2.1
  have hs := hb.2.2
  have h := record_charge s r
  unfold updateBound
  omega

/-- The full returned sampler record is preserved, and the ledger equals the
actual binary update of that very record. No alternate random draw is used. -/
theorem trackedDraw_support (bit : PMF Bool) (bound fuel : Bits)
    (positive : 0 < value bound) (s : Ledger) {out : Output bound × Ledger}
    (hout : out ∈ ((trackedDraw bit bound positive fuel).run s).support) :
    out.1 ∈ (BinaryBoundedSampler.draw bit bound positive fuel).support ∧
      out.2 = record s out.1 := by
  change out ∈ ((BinaryBoundedSampler.draw bit bound positive fuel).map
    (fun r => (r,record s r))).support at hout
  obtain ⟨r,hr,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  subst out
  exact ⟨hr,rfl⟩

/-- A single callback's declared charge includes actual bit sampling and every
binary metadata update. It is not just a bound on decoded counter magnitudes. -/
theorem trackedDraw_charge (bit : PMF Bool) (bound fuel : Bits)
    (positive : 0 < value bound) (s : Ledger) {out : Output bound × Ledger}
    (hout : out ∈ ((trackedDraw bit bound positive fuel).run s).support) :
    out.2.operations ≤ s.operations+updateBound s bound fuel := by
  obtain ⟨hr,he⟩ := trackedDraw_support bit bound fuel positive s hout
  rw [he]
  exact record_draw_charge bit bound fuel positive s hr

end
end DirectedFlowCutGap.BinarySamplerMetadata
