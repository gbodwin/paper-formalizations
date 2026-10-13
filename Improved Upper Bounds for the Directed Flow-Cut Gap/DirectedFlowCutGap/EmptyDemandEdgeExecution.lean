import DirectedFlowCutGap.EmptyDemandEdgeTrace

namespace DirectedFlowCutGap.EmptyDemandEdge
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def inputSteps (rows : List Bits) (u v : Bits) : ℕ :=
  26*(u.length+v.length+1)+6*rows.length+6*(rows.map List.length).sum+40

theorem row_le_total (rows : List Bits) {r : Bits} (hr : r∈rows) :
    r.length ≤ (rows.map List.length).sum := by
  induction rows with
  | nil => simp at hr
  | cons a rows ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · simp
    · have h := ih hr
      simp only [List.map_cons,List.sum_cons]
      omega

theorem steps_bound (rows : List Bits) (u v : Bits) (hi : value u<rows.length)
    (hj : value v<(rows[value u]).length) : steps u v+1 ≤ inputSteps rows u v := by
  have hc := BinaryComparisonProgram.steps_bound u v
  have hu := BinaryPointerListRead.steps_bound u
  have hv := BinaryPointerListRead.steps_bound v
  have hr := row_le_total rows (List.getElem_mem hi)
  unfold steps tailSteps inputSteps GraphAdjacencyProgram.steps
  split <;> omega

theorem scan {heap : NaturalHeap} {a b : ℕ} {u v : Bits} {rows : List Bits}
    (hd : Demand heap a u v) (hm : GraphAdjacencyProgram.Matrix heap b rows)
    (hi : value u<rows.length) (hj : value v<(rows[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 128)) (source : Bits) :
    ∃ ext out,ext.length=cells u v ∧ NaturalRun program (steps u v+1)
      (state heap next a b c d stack source 126) []
      (state (heap++ext) (next+ext.length) a b c out stack source 127) ∧
      (heap++ext)[out]?=some (.flag (bit rows u v)) := by
  obtain ⟨ext,out,len,run,rep⟩ := edge_return hd hm hi hj next c d hn ⟨a,b,c,d⟩ 127 stack source
  have call : tickNatural program (state heap next a b c d stack source 126)=
      some ⟨state heap next a b c d (⟨127,.r3,⟨a,b,c,d⟩⟩::stack) source 96,[],0⟩ := by rfl
  exact ⟨ext,out,len,by simpa [Nat.add_comm] using NaturalRun.step call run,rep⟩
theorem bit_or (rows : List Bits) (u v : Bits) :
    bit rows u v=(SupportRecoveryProgram.same u v || GraphRelaxationProgram.adjacent rows u v) := by
  by_cases h : BinaryComparisonProgram.order u v=.eq <;> simp [bit,SupportRecoveryProgram.same,h]

theorem bit_original {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (u v : Fin n) :
    bit (GraphRelaxationRefinement.matrix adjacency) (label u) (label v)=
      (decide (u=v) || (BinaryFractionalWalkOracle.adjacent adjacency u v).1) := by
  rw [bit_or,SupportSearchEncoding.same_label label hlabel,
    GraphRelaxationRefinement.adjacent_eq adjacency label hlabel]
end DirectedFlowCutGap.EmptyDemandEdge
