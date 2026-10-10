import DirectedFlowCutGap.BinaryEntryTrees
import DirectedFlowCutGap.EncodedRoundingRepetition

/-! Complete repeated records and selection are interpreted under the same
bit stream and ledger. No independent-record or independent-ledger premise is
needed; only the literal primitive bit requests are lowered. -/
namespace DirectedFlowCutGap.BinaryRepetitionTrees
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler RetainedGridState
open EncodedRoundingRepetition
variable {n : ℕ}

section Execute
variable {M : Type → Type} [Monad M] [LawfulMonad M] (b : M (Fin 2))
variable (p : StateT Ledger FiniteDrawTrees.Tree (EncodedRoundingEntry.Output n))
  (q : StateT Ledger M (EncodedRoundingEntry.Output n))
  (hp : ∀ s,execute (liftBit b) (p.run s)=q.run s)
include hp

theorem many_execute (k : ℕ) (state : Ledger) :
    execute (liftBit b) ((drawMany p k).run state)=((drawMany q k).run state) := by
  induction k generalizing state with
  | zero => rfl
  | succ k ih =>
    unfold drawMany
    apply StatefulTreeInterpreter.bind_execute b _ _ _ _ hp
    intro o s
    apply StatefulTreeInterpreter.bind_execute b _ _ _ _ (fun s => ih s)
    intro tail state
    rfl

theorem repeat_execute (extra : ℕ) (state : Ledger) :
    execute (liftBit b) ((repeatDraws p extra).run state)=((repeatDraws q extra).run state) := by
  unfold repeatDraws
  apply StatefulTreeInterpreter.bind_execute b _ _ _ _ hp
  intro o s
  apply StatefulTreeInterpreter.bind_execute b _ _ _ _ (fun s => many_execute b p q hp extra s)
  intro tail state
  rfl
end Execute

section Binary
variable (p : StateT Ledger FiniteDrawTrees.Tree (EncodedRoundingEntry.Output n))
  (hp : ∀ s,Binary (p.run s))
include hp

theorem many_binary (k : ℕ) (state : Ledger) : Binary ((drawMany p k).run state) := by
  induction k generalizing state with
  | zero => exact .pure _
  | succ k ih =>
    unfold drawMany
    apply StatefulTreeInterpreter.binary_bind _ _ hp
    intro o s
    apply StatefulTreeInterpreter.binary_bind _ _ (fun s => ih s)
    intro tail state
    exact .pure _

theorem repeat_binary (extra : ℕ) (state : Ledger) : Binary ((repeatDraws p extra).run state) := by
  unfold repeatDraws
  apply StatefulTreeInterpreter.binary_bind _ _ hp
  intro o s
  apply StatefulTreeInterpreter.binary_bind _ _ (fun s => many_binary p hp extra s)
  intro tail state
  exact .pure _
end Binary

section Budget
variable (p : StateT Ledger FiniteDrawTrees.Tree (EncodedRoundingEntry.Output n))
  (K : ℕ) (hp : ∀ s,Within K (p.run s))
include hp

theorem many_within (k : ℕ) (state : Ledger) : Within (k*K) ((drawMany p k).run state) := by
  induction k generalizing state with
  | zero => exact .pure _ _
  | succ k ih =>
    unfold drawMany
    rw [Nat.succ_mul,Nat.add_comm]
    apply StatefulTreeInterpreter.within_bind _ _ hp
    intro o s
    apply StatefulTreeInterpreter.within_bind _ _ (r := 0) (fun s => ih s)
    intro tail state
    exact .pure _ _

theorem repeat_within (extra : ℕ) (state : Ledger) :
    Within ((extra+1)*K) ((repeatDraws p extra).run state) := by
  unfold repeatDraws
  rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]
  apply StatefulTreeInterpreter.within_bind _ _ hp
  intro o s
  apply StatefulTreeInterpreter.within_bind _ _ (r := 0) (fun s => many_within p K hp extra s)
  intro tail state
  exact .pure _ _
end Budget

end DirectedFlowCutGap.BinaryRepetitionTrees
