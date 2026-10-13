import DirectedFlowCutGap.AvoidingDemandScanTrace

namespace DirectedFlowCutGap.AvoidingDemandScan
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

def encode {n : ℕ} (label : Fin n → Bits) (q : BinaryFractionalGraphOracle.Selected n) :
    (Bits × Bits) × GraphWalkExtension.Walk :=
  ((label q.demand.1,label q.demand.2),GraphRelaxationRefinement.encode label q.path)

theorem result_original {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n)) :
    result (List.ofFn label) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)
      (ds.map fun e => (label e.1,label e.2))=
    (BinaryFractionalDispatch.findAvoiding adjacency (BinaryFractionalDispatch.zeroMask costs).1 ds).1.map (encode label) := by
  induction ds with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,result,AvoidingKeptPath.result_original adjacency costs e.1 e.2 label hlabel,
      BinaryFractionalDispatch.findAvoiding]
    cases h : (BinaryFractionalWalkOracle.shortest (ResidualSearch.Enumeration.fin n)
      (BinaryFractionalDispatch.keptAdjacency adjacency (BinaryFractionalDispatch.zeroMask costs).1 e.1 e.2).1
      (fun _ => (BinaryRational.zero,1)) e.1 e.2).1 with
    | none => simpa only [Option.map_none] using ih
    | some q => rfl

def inputSteps (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) (ds : List (Bits × Bits)) (W : ℕ) : ℕ :=
  (ds.map fun e => AvoidingKeptPath.inputSteps e.1 e.2 vs costs rows W+20).sum+4

theorem steps_bound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n)) (W : ℕ) (hW : 1≤W) (labels : ∀ i,(label i).length≤W) :
    steps (List.ofFn label) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)
      (ds.map fun e => (label e.1,label e.2))+1≤
    inputSteps (List.ofFn label) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)
      (ds.map fun e => (label e.1,label e.2)) W := by
  induction ds with
  | nil => simp [steps,inputSteps]
  | cons e es ih =>
    have he := AvoidingKeptPath.steps_bound adjacency costs e.1 e.2 label hlabel W hW labels
    simp only [List.map_cons,steps]
    unfold inputSteps at *
    simp only [List.map_cons,List.sum_cons] at *
    split <;> simp only [Nat.add_assoc] at * <;> omega

theorem scan {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n)) {heap : NaturalHeap} {a b : ℕ}
    (table : Table heap a (ds.map fun e => (label e.1,label e.2)))
    (context : Context heap b (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency))
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 1900)) (source : Bits) :
    ∃ ext out,ext.length=cells (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) ∧
      NaturalRun program (steps (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2))+1)
        (state heap next a b c d stack source 1898) []
        (state (heap++ext) (next+ext.length) a b c out stack source 1899) ∧
      Result (heap++ext) out
        ((BinaryFractionalDispatch.findAvoiding adjacency (BinaryFractionalDispatch.zeroMask costs).1 ds).1.map (encode label)) := by
  obtain ⟨ext,out,len,run,rep⟩ := scan_return adjacency costs label hlabel ds table context next c d hn
    ⟨a,b,c,d⟩ 1899 stack source
  have call : tickNatural program (state heap next a b c d stack source 1898)=
      some ⟨state heap next a b c d (⟨1899,.r3,⟨a,b,c,d⟩⟩::stack) source 1810,[],0⟩ := rfl
  exact ⟨ext,out,len,.step call run,by simpa only [result_original adjacency costs label hlabel ds] using rep⟩
end DirectedFlowCutGap.AvoidingDemandScan
