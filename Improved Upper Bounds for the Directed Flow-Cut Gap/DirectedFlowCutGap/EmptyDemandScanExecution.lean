import DirectedFlowCutGap.EmptyDemandScanTrace

namespace DirectedFlowCutGap.EmptyDemandScan
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def inputSteps (rows : List Bits) (ds : List (Bits × Bits)) : ℕ :=
  (ds.map fun e => EmptyDemandEdge.inputSteps rows e.1 e.2+12).sum+4

theorem steps_bound (rows : List Bits) (ds : List (Bits × Bits)) (valid : ∀ e∈ds,Valid rows e) :
    steps rows ds+1 ≤ inputSteps rows ds := by
  induction ds with
  | nil => simp [steps,inputSteps]
  | cons e es ih =>
    obtain ⟨hi,hj⟩ := valid e (by simp)
    have he := EmptyDemandEdge.steps_bound rows e.1 e.2 hi hj
    have ht := ih (fun e he => valid e (List.mem_cons_of_mem _ he))
    simp only [steps,inputSteps,List.map_cons,List.sum_cons] at *
    split <;> omega

theorem scan {heap : NaturalHeap} {a b : ℕ} {ds : List (Bits × Bits)} {rows : List Bits}
    (table : Table heap a ds) (hm : GraphAdjacencyProgram.Matrix heap b rows)
    (valid : ∀ e∈ds,Valid rows e)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext out,ext.length=cells rows ds ∧ NaturalRun program (steps rows ds+1)
      (state heap next a b c d stack source 158) []
      (state (heap++ext) (next+ext.length) a b c out stack source 159) ∧
      Result (heap++ext) out (result rows ds) := by
  obtain ⟨ext,out,len,run,rep⟩ := scan_return table hm valid next c d hn ⟨a,b,c,d⟩ 159 stack source
  have call : tickNatural program (state heap next a b c d stack source 158)=
      some ⟨state heap next a b c d (⟨159,.r3,⟨a,b,c,d⟩⟩::stack) source 136,[],0⟩ := by rfl
  exact ⟨ext,out,len,by simpa [Nat.add_comm] using NaturalRun.step call run,rep⟩

theorem result_original {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (ds : List (Fin n × Fin n)) :
    result (GraphRelaxationRefinement.matrix adjacency) (ds.map fun d => (label d.1,label d.2))=
      ((BinaryFractionalDispatch.emptyDemand adjacency ds).1.map fun d => (label d.1,label d.2)) := by
  induction ds with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,result,EmptyDemandEdge.bit_original adjacency label hlabel,BinaryFractionalDispatch.emptyDemand]
    by_cases h : e.1=e.2 ∨ (BinaryFractionalWalkOracle.graph adjacency).Adj e.1 e.2
    · simp [h,Bool.or_eq_true]
    · simp [h,Bool.or_eq_true,ih]
end DirectedFlowCutGap.EmptyDemandScan
