import DirectedFlowCutGap.EncodedRoundingState
import DirectedFlowCutGap.RetainedClosureLaw

/-!
# Whole deterministic retained rounding cost composition

This is the counted concrete controller, not a charge assigned to an arbitrary
optimizer callback. The optimizer is the retained dictionary/early-stop backend
and every shortest cut uses the fully counted array implementation. Runtime
materialization, mass scans, Boolean mask copies, state construction, branch
arithmetic and recursion are included. The returned reference counters are the
actual families/candidates/restarts/rounds of this same execution.

Randomness remains an explicit boundary: this deterministic entry consumes an
already materialized input list. Its cost excludes producing that list and
sampling bits. The online composition must add the separately proved tape
materialization and sampler charges and must not replay this execution.
-/
namespace DirectedFlowCutGap.EncodedRoundingRuntime
open scoped BigOperators NNReal
open RetainedGridState IntegerAdaptiveExecution
open EncodedRoundingInput EncodedIntegerShortestPaths EncodedRoundingState

-- The two checked graph encodings are definitionally equal semireducible constants.
-- Permit tactic matching to unfold them; kernel conversion remains unchanged.
set_option backward.isDefEq.respectTransparency false

variable {n L : ℕ}
variable (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
variable (horder : F.base.enumeration.vertices = List.finRange n) (hL : 0<L)
variable {demands : Finset (Pair n)}
local notation "H" => EncodedRoundingState.Witness (demands := demands) adjacency F hL
local notation "Q" => RetainedCandidateSolver.optimizer (demands := demands) adjacency F horder hL
local notation "C" => cutOracle F.base.enumeration adjacency hL

/-- An additive upper charge on the literal executed events. -/
def price (n L : ℕ) (w : Work) : ℕ :=
  w.candidates*candidateBound n L+w.families*(familyOverhead n+16)+
  w.massScans*massBound n+w.gates*32+w.epochTests*96+
  w.rounds*(roundOverhead n+16)+w.restarts*16

@[simp] theorem price_zero (n L : ℕ) : price n L {} = 0 := by simp [price]

theorem price_add (n L : ℕ) (a b : Work) :
    price n L (a.add b) = price n L a+price n L b := by
  simp only [price,Work.add]
  ring

/-- Data references and proof fields do not copy retained arrays. -/
def advance (R : ℕ) (c : Cache H) : Result H × ℕ :=
  if c.ready R then (⟨c,{gates := 1}⟩,12) else
    let a := EncodedRoundingState.refresh adjacency F horder hL c.install
    (⟨a.1,({gates := 1,restarts := 1} : Work).add (refreshWork c.install)⟩,a.2+16)

theorem advance_value (R : ℕ) (c : Cache H) :
    (advance adjacency F horder hL R c).1 = IntegerAdaptiveExecution.advance Q R c := by
  simp only [advance,IntegerAdaptiveExecution.advance,EncodedRoundingState.refresh_value]
  split_ifs <;> rfl

theorem advance_bound (R : ℕ) (c : Cache H) :
    (advance adjacency F horder hL R c).2+4 ≤
      price n L (advance adjacency F horder hL R c).1.work := by
  have h := EncodedRoundingState.refresh_bound adjacency F horder hL c.install
  simp only [advance]
  split
  · simp [price]
  · simp only [price,Work.add,refreshWork,Nat.zero_add,Nat.one_mul,Nat.zero_mul,Nat.add_zero]
    omega

def stabilize (R : ℕ) : ℕ → Cache H → Result H × ℕ
  | 0,c => (⟨c,{}⟩,1)
  | fuel+1,c =>
      let a := advance adjacency F horder hL R c
      let b := stabilize R fuel a.1.cache
      (⟨b.1.cache,a.1.work.add b.1.work⟩,a.2+b.2+4)

theorem stabilize_value (R fuel : ℕ) (c : Cache H) :
    (stabilize adjacency F horder hL R fuel c).1 =
      IntegerAdaptiveExecution.stabilize Q R fuel c := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
      simp only [stabilize,IntegerAdaptiveExecution.stabilize,ih,advance_value]

theorem stabilize_bound (R fuel : ℕ) (c : Cache H) :
    (stabilize adjacency F horder hL R fuel c).2 ≤
      price n L (stabilize adjacency F horder hL R fuel c).1.work+1 := by
  induction fuel generalizing c with
  | zero => simp [stabilize,price]
  | succ fuel ih =>
      have ha := advance_bound adjacency F horder hL R c
      have hb := ih (advance adjacency F horder hL R c).1.cache
      simp only [stabilize,price_add]
      omega

def scan (R M : ℕ) (cells : Pair n → Fin L) : List (Pair n) → Cache H → Result H × ℕ
  | [],c => (⟨c,{}⟩,1)
  | p::ps,c =>
      if h : IntegerAdaptiveExecution.active R M c = true ∧ flag c.state.data.remaining p = true then
        let s := EncodedRoundingState.sampleRound adjacency F hL c.state p
          (membership_of_flag c.state p h.2) (cells p)
        let a := EncodedRoundingState.refresh adjacency F horder hL s.1
        let b := scan R M cells ps a.1
        (⟨b.1.cache,(({epochTests := 1,rounds := 1,massScans := 1} : Work).add
          (refreshWork s.1)).add b.1.work⟩,s.2+a.2+b.2+48)
      else (⟨c,{epochTests := 1}⟩,48)

theorem scan_value (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    (scan adjacency F horder hL R M cells order c).1 =
      IntegerAdaptiveExecution.scan Q hL C R M cells order c := by
  induction order generalizing c with
  | nil => rfl
  | cons p ps ih =>
      simp only [scan,IntegerAdaptiveExecution.scan]
      split_ifs with h
      · simp only [ih,EncodedRoundingState.refresh_value,EncodedRoundingState.sampleRound_value]
      · rfl

theorem scan_bound (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    (scan adjacency F horder hL R M cells order c).2 ≤
      price n L (scan adjacency F horder hL R M cells order c).1.work+1 := by
  induction order generalizing c with
  | nil => simp [scan,price]
  | cons p ps ih =>
      simp only [scan]
      split
      next h =>
        let s := EncodedRoundingState.sampleRound adjacency F hL c.state p
          (membership_of_flag c.state p h.2) (cells p)
        let a := EncodedRoundingState.refresh adjacency F horder hL s.1
        have hs := EncodedRoundingState.sampleRound_bound adjacency F hL c.state p
          (membership_of_flag c.state p h.2) (cells p)
        have ha := EncodedRoundingState.refresh_bound adjacency F horder hL s.1
        have hb := ih a.1
        change s.2+a.2+(scan adjacency F horder hL R M cells ps a.1).2+48 ≤ _
        rw [price_add,price_add]
        simp only [price,refreshWork,Nat.zero_add,Nat.one_mul,Nat.zero_mul,Nat.add_zero] at hb ⊢
        change s.2 ≤ roundOverhead n+massBound n at hs
        change a.2 ≤ (remainingSet s.1.data.remaining).card*candidateBound n L+
          familyOverhead n+massBound n+4 at ha
        dsimp only [a,s] at ha hb hs ⊢
        omega
      next h => simp [price]

/-- Supplied-input execution computes each stabilization and sampled round once. -/
def execute (R fuel : ℕ) : List (Input n L) → Cache H → Result H × ℕ
  | [],c => stabilize adjacency F horder hL R fuel c
  | i::inputs,c =>
      let a := stabilize adjacency F horder hL R fuel c
      if a.1.cache.optimal == 0 then (a.1,a.2+4) else
        let b := scan adjacency F horder hL R a.1.cache.state.data.current i.cell i.order a.1.cache
        let d := execute R fuel inputs b.1.cache
        (⟨d.1.cache,a.1.work.add (b.1.work.add d.1.work)⟩,a.2+b.2+d.2+8)

theorem execute_value (R fuel : ℕ) (inputs : List (Input n L)) (c : Cache H) :
    (execute adjacency F horder hL R fuel inputs c).1 =
      IntegerAdaptiveExecution.execute Q hL C R fuel inputs c := by
  induction inputs generalizing c with
  | nil => exact stabilize_value adjacency F horder hL R fuel c
  | cons i inputs ih =>
      simp only [execute,IntegerAdaptiveExecution.execute,stabilize_value]
      split
      · rfl
      · simp only [ih,scan_value]

theorem execute_bound (R fuel : ℕ) (inputs : List (Input n L)) (c : Cache H) :
    (execute adjacency F horder hL R fuel inputs c).2 ≤
      price n L (execute adjacency F horder hL R fuel inputs c).1.work+10*inputs.length+1 := by
  induction inputs generalizing c with
  | nil => simpa only [execute,List.length_nil,Nat.mul_zero,Nat.add_zero] using
      stabilize_bound adjacency F horder hL R fuel c
  | cons i inputs ih =>
      let a := stabilize adjacency F horder hL R fuel c
      have ha := stabilize_bound adjacency F horder hL R fuel c
      simp only [execute]
      split
      · change a.2+4 ≤ price n L a.1.work+10*(i::inputs).length+1
        change a.2 ≤ price n L a.1.work+1 at ha
        simp only [List.length_cons]
        omega
      · let b := scan adjacency F horder hL R a.1.cache.state.data.current i.cell i.order a.1.cache
        have hb := scan_bound adjacency F horder hL R a.1.cache.state.data.current i.cell i.order a.1.cache
        have hd := ih b.1.cache
        change a.2+b.2+(execute adjacency F horder hL R fuel inputs b.1.cache).2+8 ≤ _
        rw [price_add,price_add]
        change a.2 ≤ price n L a.1.work+1 at ha
        change b.2 ≤ price n L b.1.work+1 at hb
        simp only [List.length_cons]
        dsimp only [a,b] at ha hb hd ⊢
        omega

/-- Initial family materialization is included exactly once. The caller still
pays for input-mask/initial-state preparation and for sampled input generation. -/
def run (R fuel : ℕ) (inputs : List (Input n L)) (s : Code (graph adjacency) demands L) :
    Result H × ℕ :=
  let a := EncodedRoundingState.refresh adjacency F horder hL s
  let b := execute adjacency F horder hL R fuel inputs a.1
  (⟨b.1.cache,(refreshWork s).add b.1.work⟩,a.2+b.2+4)

theorem run_value (R fuel : ℕ) (inputs : List (Input n L)) (s : Code (graph adjacency) demands L) :
    (run adjacency F horder hL R fuel inputs s).1 =
      IntegerAdaptiveExecution.run Q hL C R fuel inputs s := by
  simp only [run,IntegerAdaptiveExecution.run,IntegerAdaptiveExecution.start,
    EncodedRoundingState.refresh_value]
  rw [execute_value adjacency F horder hL]

theorem run_bound (R fuel : ℕ) (inputs : List (Input n L)) (s : Code (graph adjacency) demands L) :
    (run adjacency F horder hL R fuel inputs s).2 ≤
      price n L (run adjacency F horder hL R fuel inputs s).1.work+10*inputs.length+1 := by
  have ha := EncodedRoundingState.refresh_bound adjacency F horder hL s
  have hb := execute_bound adjacency F horder hL R fuel inputs
    (EncodedRoundingState.refresh adjacency F horder hL s).1
  simp only [run,price_add]
  simp only [price,refreshWork] at hb ⊢
  omega

end DirectedFlowCutGap.EncodedRoundingRuntime
