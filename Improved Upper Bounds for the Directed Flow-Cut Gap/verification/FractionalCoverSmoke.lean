import DirectedFlowCutGap.FractionalCoverAnalysis
import DirectedFlowCutGap.FractionalCoverEncoding
open DirectedFlowCutGap.FractionalCover

namespace FractionalCoverSmoke

def costs : Row 3 := #v[(1 : ℚ), 2, 4]
def p01 : Column 3 := {0, 1}
def p12 : Column 3 := {1, 2}
def p02 : Column 3 := {0, 2}

def choose (y : Row 3) : Choice 3 :=
  if length y p01 ≤ length y p12 ∧ length y p01 ≤ length y p02 then
    ⟨p01, 0⟩
  else if length y p12 ≤ length y p02 then ⟨p12, 1⟩ else ⟨p02, 0⟩

def family : Set (Column 3) := {p | p = p01 ∨ p = p12 ∨ p = p02}

theorem costs_positive : ∀ i, 0 < value costs i := by
  intro i
  fin_cases i <;> norm_num [value, costs]

theorem choose_correct : OracleCorrect costs family choose := by
  constructor
  · intro y _
    unfold choose
    split_ifs <;> simp [family]
  · intro y _
    unfold choose
    split_ifs <;> norm_num [p01, p12, p02]
  · intro y _ i hi
    unfold choose at *
    split_ifs at * <;> fin_cases i <;> norm_num [p01, p12, p02, value, costs] at *
  · intro y _ p hp
    rcases hp with rfl | rfl | rfl <;> unfold choose <;> split_ifs <;> grind

example : 1 ≤ objective costs (solve costs choose).weights :=
  solve_stopped costs family choose (by decide) costs_positive choose_correct

/-- Execute a genuinely changing three-column example with unequal costs. -/
def test : IO Unit := do
  let s := solve costs choose
  let selected := (s.events.map (fun e => e.choice.column)).eraseDups
  if !(1 ≤ objective costs s.weights) then throw (IO.userError "stop condition failed")
  if !(1 ≤ length s.best p01 ∧ 1 ≤ length s.best p12 ∧ 1 ≤ length s.best p02) then
    throw (IO.userError "returned vector is not feasible")
  if !(objective costs s.best ≤ 3 * (7/2 : ℚ)) then
    throw (IO.userError "three-approximation to half-cover comparator failed")
  if !(2 ≤ selected.length) then throw (IO.userError "example did not switch columns")
  if !(s.total = traceTotal s.events) then throw (IO.userError "trace amount mismatch")
  if !((List.finRange 3).all fun i => value s.loads i == traceLoad s.events i) then
    throw (IO.userError "trace load mismatch")
  IO.println s!"PASS: {s.events.length} actual updates, {selected.length} distinct columns, {oracleCalls s} oracle calls"
  IO.println s!"retained cover = {reprStr s.best}; objective = {objective costs s.best}"
  IO.println s!"final potential = {objective costs s.weights}; total packing amount = {s.total}"
  let smallCosts : Row 3 := #v[(1/10 : ℚ), 1/5, 2/5]
  let small := solve smallCosts choose
  if !(small.best == s.best) then throw (IO.userError "subunit cost scaling changed normalized cover")
  if !(small.total = s.total / 10) then throw (IO.userError "subunit packing amount mismatch")
  if !(objective smallCosts small.weights = objective costs s.weights) then
    throw (IO.userError "subunit potential mismatch")
  IO.println "PASS: subunit positive rational costs follow the same normalized trajectory"
  let oneCost : Row 1 := #v[(1/7 : ℚ)]
  let one := solve oneCost (fun _ => ⟨{0}, 0⟩)
  if !(one.events.length = 1 ∧ value one.best 0 = 1 ∧ objective oneCost one.weights = 1) then
    throw (IO.userError "one-resource exact stopping boundary failed")
  IO.println "PASS: one-resource instance stops exactly at potential one after one update"

#eval test
end FractionalCoverSmoke
