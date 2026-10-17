import LightEFTSpanners.ComputableVotingSamples
import LightEFTSpanners.ControllerTrace

namespace LightEFTSpanners.StoredRepetitions
open Controller
inductive State where
  | offset : ℕ → ℕ → State
  | scale : ℕ → ℕ → State
  | product : ℕ → ℕ → State
  | increment : ℕ → State
  | halt : ℕ → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .offset n s => some (.scale n (s+5))
  | .scale n a => some (.product n (32*a))
  | .product n a => some (.increment (a*n))
  | .increment a => some (.halt (a+1))
  | .halt _ => none

theorem trace (n s : ℕ) : Trace transition 4 (.offset n s)
    (.halt (SampledGreedy.polynomialRepetitions n s)) := by
  exact Trace.cons rfl (Trace.cons rfl (Trace.cons rfl (Trace.cons rfl (.refl _))))

def execute (n s : ℕ) : ℕ :=
  match Controller.run transition 4 (.offset n s) with | .halt m => m | _ => 0

theorem execute_eq (n s : ℕ) : execute n s=SampledGreedy.polynomialRepetitions n s := by
  unfold execute
  rw [(trace n s).run_eq]
end LightEFTSpanners.StoredRepetitions
