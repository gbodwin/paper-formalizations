import DirectedFlowCutGap.AvoidingKeptPathTrace

namespace DirectedFlowCutGap.AvoidingKeptPath
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

theorem result_original {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    result (label s) (label t) (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency)=
      (BinaryFractionalWalkOracle.shortest (ResidualSearch.Enumeration.fin n)
        (BinaryFractionalDispatch.keptAdjacency adjacency (BinaryFractionalDispatch.zeroMask costs).1 s t).1
        (fun _ => (BinaryRational.zero,1)) s t).1.map (GraphRelaxationRefinement.encode label) := by
  unfold result kept
  rw [KeptAdjacencyInput.result_original label hlabel]
  simpa only [enum_map] using AvoidingShortest.result_constant (ResidualSearch.Enumeration.fin n)
    (BinaryFractionalDispatch.keptAdjacency adjacency (BinaryFractionalDispatch.zeroMask costs).1 s t).1
    s t label hlabel

theorem search {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {heap : NaturalHeap} {a b : ℕ}
    (input : GraphDiscoveryProgram.Vertices heap a (List.ofFn label))
    (metadata : KeptAdjacencyInput.Context heap b (label s) (label t)
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency))
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 1800)) (source : Bits) :
    ∃ ext root,ext.length=cells (label s) (label t) (List.ofFn label)
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency) ∧
      NaturalRun program (steps (label s) (label t) (List.ofFn label)
        (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)+1)
        (state heap next a b c d stack source 1798) []
        (state (heap++ext) (next+ext.length) a b c root stack source 1799) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root
        ((BinaryFractionalWalkOracle.shortest (ResidualSearch.Enumeration.fin n)
          (BinaryFractionalDispatch.keptAdjacency adjacency (BinaryFractionalDispatch.zeroMask costs).1 s t).1
          (fun _ => (BinaryRational.zero,1)) s t).1.map (GraphRelaxationRefinement.encode label)) := by
  obtain ⟨ext,root,len,run,rep⟩ := search_return adjacency costs s t label hlabel input metadata next c d hn
    ⟨a,b,c,d⟩ 1799 stack source
  have call : tickNatural program (state heap next a b c d stack source 1798)=
      some ⟨state heap next a b c d (⟨1799,.r3,⟨a,b,c,d⟩⟩::stack) source 1770,[],0⟩ := rfl
  exact ⟨ext,root,len,.step call run,by simpa only [result_original adjacency costs s t label hlabel] using rep⟩

def inputSteps (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) (W : ℕ) : ℕ :=
  KeptAdjacencyInput.inputSteps s t vs costs rows+AvoidingShortest.inputSteps vs.length W s.length+11

theorem steps_bound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (W : ℕ) (hW : 1≤W) (labels : ∀ i,(label i).length≤W) :
    steps (label s) (label t) (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency)+1≤
    inputSteps (label s) (label t) (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) W := by
  have hk := KeptAdjacencyInput.steps_bound (label s) (label t) (List.ofFn label)
    (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)
  have hs := AvoidingShortest.steps_bound (ResidualSearch.Enumeration.fin n)
    (BinaryFractionalDispatch.keptAdjacency adjacency (BinaryFractionalDispatch.zeroMask costs).1 s t).1
    s t label hlabel W hW labels
  simp only [enum_map] at hs
  unfold steps inputSteps kept
  rw [KeptAdjacencyInput.result_original label hlabel]
  simp only [List.length_ofFn]
  omega
end DirectedFlowCutGap.AvoidingKeptPath
