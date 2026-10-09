import DirectedFlowCutGap.IntegerAdaptiveExecution

open DirectedFlowCutGap
open RetainedGridState IntegerAdaptiveExecution
open scoped NNReal

def exampleData : Data 2 :=
  let a := Vector.replicate 2 (Vector.replicate 2 true)
  let x := Vector.replicate 2 false
  let w := Vector.replicate 2 (Vector.replicate 2 (Vector.replicate 2 1))
  ⟨a, x, w, 1, massNumerator a x w⟩

#eval do
  unless exampleData.current == 8 do throw (IO.userError "initial mass scan")
  let s := exampleData.round (0,1) #v[true,false]
  unless s.current == 3 do throw (IO.userError "round mass scan")
  unless flag s.remaining (0,1) == false do throw (IO.userError "original label erase")
  unless flag s.remaining (1,0) == true do throw (IO.userError "other label retained")
  unless s.weights == exampleData.weights do throw (IO.userError "round weights frozen")
  unless s.scale == 1 do throw (IO.userError "round natural scale")
  let t := s.install s.weights 3
  unless t.scale == 4 do throw (IO.userError "integer installation scale")
  IO.println "PASS retained array, mass, original-label, frozen-weight and scale checks"

def emptyGraph : Digraph (Fin 1) := ⟨fun _ _ => False⟩
instance : DecidableRel emptyGraph.Adj := fun _ _ => isFalse id

def vertexEnum : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin 1) where
  vertices := [0]
  nodup := by simp
  complete := by intro v; fin_cases v; simp

def emptyData : Data 1 :=
  ⟨Vector.replicate 1 (Vector.replicate 1 false), Vector.replicate 1 false,
    Vector.replicate 1 (Vector.replicate 1 (Vector.replicate 1 0)), 1, 0⟩

def emptyCode : Code emptyGraph ∅ 1 where
  data := emptyData
  valid := by
    constructor <;> simp [emptyData, remainingSet, flag, massNumerator]

noncomputable def emptyProvider : FlexibleCandidateSchedule.FamilyProvider emptyGraph ∅ ((1 : ℕ) : ℝ≥0) where
  family := fun _ _ _ => 0
  feasible := by
    intro s p hp
    have hh := s.remaining_subset hp
    simp at hh
  minimal := by
    intro s p hp
    have hh := s.remaining_subset hp
    simp at hh

def emptyOptimizer : Optimizer (L := 1) (providerWitness emptyProvider) where
  solve := fun _ _ _ => Vector.replicate 1 0
  solve_eq := by intro s p hp v; simp [selectedProvider_eq, emptyProvider]
  inactive_eq := by intros; simp only [selectedProvider_eq]; rfl

#eval do
  let c := refresh emptyOptimizer emptyCode
  let out := execute emptyOptimizer (by decide : 0 < 1)
    (integerCutOracle (G := emptyGraph) (by decide) vertexEnum) 2 5 [] c
  unless out.cache.state.data == emptyData do throw (IO.userError "ready state changed")
  unless out.work.gates == 5 do throw (IO.userError "gate counter")
  unless out.work.families == 0 do throw (IO.userError "cached gate repeated optimizer")
  unless out.work.restarts == 0 do throw (IO.userError "spurious restart")
  let initial := start emptyOptimizer emptyCode
  unless initial.work.families == 1 do throw (IO.userError "initial refresh not counted")
  unless initial.work.candidates == 0 do throw (IO.userError "inactive label solved")
  IO.println "PASS executable retained control, cached gates and initial refresh accounting"

def closureEnum : IntegralNetworkFlow.ResidualSearch.Enumeration
    (MinimumClosureCut.Vertex (CandidateThresholdClosure.Node (CandidateGridOptimizer.Point (Fin 1)) 1)) where
  vertices :=
    ([TerminalPorts.core (0 : Fin 1), TerminalPorts.source 0, TerminalPorts.sink 0].flatMap
      fun v => [false, true].flatMap fun b =>
        ([0,1] : List (Fin 2)).map fun k => Sum.inl ((v,b),k)) ++
      [Sum.inr false, Sum.inr true]
  nodup := by decide
  complete := by
    intro v
    rcases v with ⟨⟨v,b⟩,k⟩ | b
    · rcases v with v | (v | v) <;> fin_cases v <;> cases b <;> fin_cases k <;> simp
    · cases b <;> simp

#eval do
  let out := IntegerAdaptiveExecution.run
    (tabulatedOptimizer (G := emptyGraph) (D := ∅) (by decide : 0 < 1) vertexEnum closureEnum)
    (by decide : 0 < 1) (integerCutOracle (G := emptyGraph) (by decide) vertexEnum)
    2 3 [] emptyCode
  unless out.work.families == 1 do throw (IO.userError "concrete initial refresh")
  unless out.work.gates == 3 do throw (IO.userError "concrete gate count")
  unless out.cache.optimal == 0 do throw (IO.userError "concrete integer termination")
  IO.println "PASS concrete tabulated closure and shortest-path adapters through public run"
