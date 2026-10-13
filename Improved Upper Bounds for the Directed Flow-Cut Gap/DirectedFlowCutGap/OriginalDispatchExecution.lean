import DirectedFlowCutGap.OriginalDispatchTrace

namespace DirectedFlowCutGap.OriginalDispatch
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def inputSteps (vs : List Bits) (cs : List (Bits × Bits)) (rows : List Bits) (ds : List (Bits × Bits)) (W : ℕ) : ℕ :=
  EmptyDemandScan.inputSteps rows ds+AvoidingDemandScan.inputSteps vs cs rows ds W+
    4*SourceRowTableProgram.bits cs+16*cs.length+25

theorem steps_bound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n)) (W : ℕ) (hW : 1≤W) (labels : ∀ i,(label i).length≤W) :
    steps (List.ofFn label) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)
      (ds.map fun e => (label e.1,label e.2))+1≤
    inputSteps (List.ofFn label) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)
      (ds.map fun e => (label e.1,label e.2)) W := by
  have he := EmptyDemandScan.steps_bound (GraphRelaxationRefinement.matrix adjacency)
    (ds.map fun e => (label e.1,label e.2)) (original_valid adjacency label hlabel ds)
  have ha := AvoidingDemandScan.steps_bound adjacency costs label hlabel ds W hW labels
  have hz := PackingZeroMask.steps_bound (IndexedRationalRead.fields costs.toList)
  unfold steps inputSteps
  split
  · omega
  · split <;> simp only [Nat.add_assoc] at * <;> omega

theorem dispatch {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n)) {heap : NaturalHeap} {a b : ℕ}
    (table : Table heap a (ds.map fun e => (label e.1,label e.2)))
    (context : Context heap b (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency))
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 2140)) (source : Bits) :
    ∃ ext out,ext.length=cells (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) ∧
      NaturalRun program (steps (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2))+1)
        (state heap next a b c d stack source 2138) []
        (state (heap++ext) (next+ext.length) a b c out stack source 2139) ∧
      Result (heap++ext) out (encode label (BinaryFractionalDispatch.dispatch adjacency ds costs).1) := by
  obtain ⟨ext,out,len,run,rep⟩ := dispatch_return adjacency costs label hlabel ds table context
    next c d hn ⟨a,b,c,d⟩ 2139 stack source
  have call : tickNatural program (state heap next a b c d stack source 2138)=
      some ⟨state heap next a b c d (⟨2139,.r3,⟨a,b,c,d⟩⟩::stack) source 2110,[],0⟩ := rfl
  exact ⟨ext,out,len,.step call run,by simpa only [result_original adjacency costs label hlabel ds] using rep⟩
end DirectedFlowCutGap.OriginalDispatch
