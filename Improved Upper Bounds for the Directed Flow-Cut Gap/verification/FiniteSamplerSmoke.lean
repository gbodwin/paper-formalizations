import DirectedFlowCutGap.FiniteGridSampler

open DirectedFlowCutGap
open FinitePermutationSampler
namespace ExactFiniteSamplerTests

def tapes : (n : ℕ) → List (Tape n)
  | 0 => [()]
  | n + 1 => (List.finRange (n + 1)).flatMap fun j => (tapes n).map fun t => (j, t)

def cells (L : ℕ) : (n : ℕ) → List (FiniteGridSampler.Cells L n)
  | 0 => [()]
  | n + 1 => (List.finRange L).flatMap fun j => (cells L n).map fun t => (j, t)

def orders (n : ℕ) : List (List ℕ) :=
  (tapes n).map fun t => ((run n t).order.map Fin.val)

def outcomes (n L : ℕ) : List (List ℕ × List ℕ) :=
  (tapes n).flatMap fun t => (cells L n).map fun c =>
    let r := FiniteGridSampler.runInput (Equiv.refl (Fin n)) (t, c)
    (r.order.map Fin.val, r.cells.map Fin.val)

#guard orders 0 = [[]]
#guard orders 1 = [[0]]
#guard (orders 3).length = 6
#guard (orders 3).eraseDups.length = 6
#guard (orders 4).length = 24
#guard (orders 4).eraseDups.length = 24
#guard (tapes 5).all (fun t => (run 5 t).draws == 5 && (run 5 t).scans == 10)
#guard (outcomes 0 1).length = 1
#guard (outcomes 3 2).length = 48
#guard (outcomes 3 2).eraseDups.length = 48
#guard (tapes 3).all (fun t => (cells 2 3).all (fun c =>
  let r := FiniteGridSampler.runInput (Equiv.refl (Fin 3)) (t, c)
  r.draws == 6 && r.scans == 6))
#guard (tapes 3).all (fun t =>
  labelOrder (Equiv.refl (Fin 3)) t ==
    List.ofFn (fun i => relativePermutation (Equiv.refl (Fin 3)) (Equiv.swap 0 2) t
      (Equiv.swap 0 2 i)))

#eval IO.println s!"PASS: 0/1/3/4-label permutation tests; { (orders 4).length } distinct size-4 orders; 120 size-5 execution count checks; { (outcomes 3 2).length } distinct 3-label/2-cell joint outcomes; reference-enumeration alignment."

end ExactFiniteSamplerTests
