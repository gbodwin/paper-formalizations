import LightEFTSpanners.LinkedDistanceKernel

/-! A first-order linked-list controller, with no supplied functions, graph
oracles, finset operations, vector enumeration, or hidden list reversal in a
transition. One transition uses at most a fixed number of pointer-cell and
rational-atom operations. It is a rational-atom pointer-machine semantics,
not a physical execution or rational bit-complexity theorem. -/
namespace LightEFTSpanners.LinkedDistance
open RationalDistance

inductive State where
  | init : ℕ → ℕ → List Cell → State
  | revInit : List Cell → List Cell → State
  | round : ℕ → List Cell → State
  | row : ℕ → List Cell → Matrix → List Cell → List Cell → State
  | scan : ℕ → List Cell → Matrix → List Cell → List Cell → List Cell → List Cell → Cell → State
  | revRound : ℕ → List Cell → List Cell → State
  | lookup : ℕ → List Cell → State
  | halt : Bool → State
  deriving DecidableEq, Repr

/-- The matrix is a finite linked list of finite linked rows; list tails and
cons cells are pointer operations. Rational addition/minimum/test and natural
register comparisons are the explicitly chosen atomic operations. -/
def transition (size : ℕ) (M : Matrix) (source target : ℕ) (budget : ℚ) : State → Option State
  | .init 0 _ acc => some (.revInit acc [])
  | .init (k+1) i acc => some (.init k (i+1) ((if i=target then some 0 else none)::acc))
  | .revInit [] out => some (.round size out)
  | .revInit (x::xs) out => some (.revInit xs (x::out))
  | .round 0 d => some (.lookup source d)
  | .round (k+1) d => some (.row k d M d [])
  | .row k _ [] _ out => some (.revRound k out [])
  | .row k _ (_::_) [] out => some (.revRound k out [])
  | .row k d (r::rs) (a::as) out => some (.scan k d rs as out r d a)
  | .scan k d rs ds out (a::as) (b::bs) z =>
      some (.scan k d rs ds out as bs (best (addCell a b) z))
  | .scan k d rs ds out _ _ z => some (.row k d rs ds (z::out))
  | .revRound k [] out => some (.round k out)
  | .revRound k (x::xs) out => some (.revRound k xs (x::out))
  | .lookup _ [] => some (.halt false)
  | .lookup 0 (a::_) => some (.halt (test a budget))
  | .lookup (k+1) (_::as) => some (.lookup k as)
  | .halt _ => none

/-- A literal finite trace of successful controller transitions. -/
inductive Executes (step : State → Option State) : ℕ → State → State → Prop
  | refl (s) : Executes step 0 s s
  | cons {n s t u} : step s=some t → Executes step n t u → Executes step (n+1) s u

namespace Executes
 theorem trans {step : State → Option State} {a b c : State} {n m : ℕ}
    (h : Executes step n a b) (g : Executes step m b c) : Executes step (n+m) a c := by
  induction h with
  | refl => simpa using g
  | cons hs _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cons hs (ih g)

 theorem one {step : State → Option State} {a b : State} (h : step a=some b) :
    Executes step 1 a b := .cons h (.refl b)
end Executes

 def run (size : ℕ) (M : Matrix) (source target : ℕ) (budget : ℚ) : ℕ → State → State
  | 0,s => s
  | k+1,s => match transition size M source target budget s with
    | none => s
    | some t => run size M source target budget k t

 theorem Executes.run_eq {size : ℕ} {M : Matrix} {source target : ℕ} {budget : ℚ}
    {k : ℕ} {s t : State} (h : Executes (transition size M source target budget) k s t) :
    run size M source target budget k s=t := by
  induction h with
  | refl => rfl
  | cons he _ ih => simp only [run,he,ih]

end LightEFTSpanners.LinkedDistance
