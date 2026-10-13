import DirectedFlowCutGap.OriginalDispatchCalls

namespace DirectedFlowCutGap.OriginalDispatch
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def result (vs : List Bits) (cs : List (Bits × Bits)) (rows : List Bits) (ds : List (Bits × Bits)) : Value :=
  match EmptyDemandScan.result rows ds with
  | some e => .infeasible e
  | none => match AvoidingDemandScan.result vs cs rows ds with
    | some w => .positive w
    | none => .zero (PackingZeroMask.mask cs)

def steps (vs : List Bits) (cs : List (Bits × Bits)) (rows : List Bits) (ds : List (Bits × Bits)) : ℕ :=
  EmptyDemandScan.steps rows ds+
    match EmptyDemandScan.result rows ds with
    | some _ => 10
    | none => AvoidingDemandScan.steps vs cs rows ds+
      match AvoidingDemandScan.result vs cs rows ds with
      | some _ => 15
      | none => PackingZeroMask.steps cs+20

def cells (vs : List Bits) (cs : List (Bits × Bits)) (rows : List Bits) (ds : List (Bits × Bits)) : ℕ :=
  EmptyDemandScan.cells rows ds+3+
    match EmptyDemandScan.result rows ds with
    | some _ => 0
    | none => AvoidingDemandScan.cells vs cs rows ds+
      match AvoidingDemandScan.result vs cs rows ds with
      | some _ => 0
      | none => 2*cs.length+1

def encode {n : ℕ} (label : Fin n → Bits) : BinaryFractionalDispatch.Result n → Value
  | .infeasible e => .infeasible (label e.1,label e.2)
  | .zero mask => .zero mask.toList
  | .positive q => .positive (AvoidingDemandScan.encode label q)

theorem result_original {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n)) :
    result (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2))=
    encode label (BinaryFractionalDispatch.dispatch adjacency ds costs).1 := by
  simp only [result,EmptyDemandScan.result_original adjacency label hlabel,
    AvoidingDemandScan.result_original adjacency costs label hlabel,PackingZeroMask.mask_eq_original,
    BinaryFractionalDispatch.dispatch]
  cases he : (BinaryFractionalDispatch.emptyDemand adjacency ds).1 with
  | some e => rfl
  | none =>
    cases hw : (BinaryFractionalDispatch.findAvoiding adjacency (BinaryFractionalDispatch.zeroMask costs).1 ds).1 <;> rfl
end DirectedFlowCutGap.OriginalDispatch
