import DirectedFlowCutGap.RetainedDemandMask
import DirectedFlowCutGap.RetainedSampledExecution

open DirectedFlowCutGap
open RetainedGridState RetainedTapeInput RetainedSampledExecution
open scoped NNReal

def chain : Digraph (Fin 3) := ⟨fun s t => (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 2)⟩
instance : DecidableRel chain.Adj := fun s t => inferInstanceAs
  (Decidable ((s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 2)))

def vertices : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin 3) where
  vertices := [0, 1, 2]
  nodup := by decide
  complete := by intro v; fin_cases v <;> simp

def network : IntegralNetworkFlow.ResidualSearch.Enumeration
    (MinimumClosureCut.Vertex (CandidateThresholdClosure.Node
      (CandidateGridOptimizer.Point (Fin 3)) 1)) where
  vertices :=
    (([0, 1, 2] : List (Fin 3)).flatMap fun v =>
      [TerminalPorts.core v, TerminalPorts.source v, TerminalPorts.sink v]).flatMap
      (fun v => [false, true].flatMap fun b =>
        ([0, 1] : List (Fin 2)).map fun k => Sum.inl ((v, b), k)) ++
      [Sum.inr false, Sum.inr true]
  nodup := by decide
  complete := by
    intro v
    rcases v with ⟨⟨v, b⟩, k⟩ | b
    · rcases v with v | (v | v) <;> fin_cases v <;> cases b <;> fin_cases k <;> simp
    · cases b <;> simp

def zeroPermutation : (k : ℕ) → FinitePermutationSampler.Tape k
  | 0 => ()
  | k + 1 => (0, zeroPermutation k)

def zeroCells (L : ℕ) (hL : 0 < L) : (k : ℕ) → FiniteGridSampler.Cells L k
  | 0 => ()
  | k + 1 => (⟨0, hL⟩, zeroCells L hL k)

def fixedSample (a : PairFlags 3) : Id (RetainedTapeInput.Tape 1 a) :=
  (zeroPermutation _, zeroCells 1 (by decide) _)

/-- One unresolved demand, still requiring a real optimizer restart and cut. -/
def focused : Digraph (Fin 3) := ⟨fun s t => s ≠ t ∧ (s ≠ 0 ∨ t ≠ 2)⟩
instance : DecidableRel focused.Adj := fun s t => inferInstanceAs
  (Decidable (s ≠ t ∧ (s ≠ 0 ∨ t ≠ 2)))

#eval do
  let a := RetainedDemandMask.compute chain vertices 1
  unless flag a (0, 2) do throw (IO.userError "reachable long demand missing")
  unless flag a (2, 0) do throw (IO.userError "infinite demand missing")
  if flag a (0, 1) then throw (IO.userError "direct edge incorrectly demanded")
  if flag a (1, 1) then throw (IO.userError "diagonal incorrectly demanded")
  unless (remainingSet a).card == 4 do throw (IO.userError "demand mask cardinality")
  let t := fixedSample a
  let i := materialize (by decide : 0 < 1) a t
  unless i.order == [(0, 2), (1, 0), (2, 0), (2, 1)] do
    throw (IO.userError "concrete filtered enumeration and permutation")
  unless i.order.length == 4 do throw (IO.userError "materialized permutation length")
  IO.println "PASS computed reachable/infinite demand mask and concrete active tape materialization"

def emptyGraph : Digraph (Fin 1) := ⟨fun _ _ => False⟩
instance : DecidableRel emptyGraph.Adj := fun _ _ => isFalse id

def singletonVertices : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin 1) where
  vertices := [0]
  nodup := by simp
  complete := by intro v; fin_cases v; simp

def singletonNetwork : IntegralNetworkFlow.ResidualSearch.Enumeration
    (MinimumClosureCut.Vertex (CandidateThresholdClosure.Node
      (CandidateGridOptimizer.Point (Fin 1)) 1)) where
  vertices :=
    ([TerminalPorts.core (0 : Fin 1), TerminalPorts.source 0, TerminalPorts.sink 0].flatMap
      fun v => [false, true].flatMap fun b =>
        ([0, 1] : List (Fin 2)).map fun k => Sum.inl ((v, b), k)) ++
      [Sum.inr false, Sum.inr true]
  nodup := by decide
  complete := by
    intro v
    rcases v with ⟨⟨v, b⟩, k⟩ | b
    · rcases v with v | (v | v) <;> fin_cases v <;> cases b <;> fin_cases k <;> simp
    · cases b <;> simp

def singletonSample (a : PairFlags 1) : Id (RetainedTapeInput.Tape 1 a) :=
  (zeroPermutation _, zeroCells 1 (by decide) _)

#eval do
  let s := RetainedDemandMask.initial emptyGraph singletonVertices 1 (by decide)
  let out := runSampled singletonSample
    (tabulatedOptimizer (G := emptyGraph) (by decide : 0 < 1) singletonVertices singletonNetwork)
    (by decide : 0 < 1) (integerCutOracle (G := emptyGraph) (by decide) singletonVertices)
    2 5 5 s
  unless out.result.work.families == 1 do throw (IO.userError "single-pass initial refresh")
  unless out.result.work.gates == 5 do throw (IO.userError "single-pass terminal gates")
  unless out.result.cache.optimal == 0 do throw (IO.userError "single-pass terminal optimum")
  unless out.inputs.isEmpty do throw (IO.userError "terminal sampler consumed an epoch")
  IO.println "PASS generated single-pass monadic interpreter on a terminal computed-mask entry"

