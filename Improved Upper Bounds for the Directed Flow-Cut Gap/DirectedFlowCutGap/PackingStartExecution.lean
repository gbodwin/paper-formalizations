import DirectedFlowCutGap.PackingStartInitialOracle
import DirectedFlowCutGap.PackingStartNormalizeState

namespace DirectedFlowCutGap.PackingStart
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem start_high {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (delta : Fraction) (label : Fin n → Bits)
    (hlabel : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (initialState : NaturalState 3060) (pc0 : initialState.pc=3020)
    (dense : initialState.next=initialState.heap.length) (empty : initialState.stack=[])
    (row : StoredList initialState.heap initialState.registers.a capacity.toList)
    (scalar : Stored initialState.heap initialState.registers.b delta)
    (input : Input initialState.heap initialState.registers.c label adjacency capacity xs) :
    ∃ ot out,NaturalRun program
      (ScalarQuotientRow.steps true delta capacity.toList+ot+25+
        finishSteps capacity (initial capacity delta).1
          (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn (initial capacity delta).1).1)
      initialState [] out ∧ out.source=initialState.source ∧ out.stack=[] ∧ out.pc=3057 ∧
      out.next=out.heap.length ∧ (∃ ext,out.heap=initialState.heap++ext) ∧
      StateRecord out.heap out.registers.d label
        (BinaryFractionalCore.start capacity delta (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).1 ∧
      ∀ W,1≤W → (∀ i,(label i).length≤W) →
        (∀ q∈(initial capacity delta).1.toList,StoredBounded q W) →
        (∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) →
        ot ≤ GraphOracleMachine.instructionBound ds.length n W+1 := by
  cases initialState with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 dense empty row scalar input
      subst pc;subst stack
      obtain ⟨ot,e0,dr,ctx,fr,wr,qr,firstRun,frame,weights,choice,bound⟩ :=
        initial_oracle adjacency capacity delta label hlabel hn encoded row scalar input next d dense source
      have dense0 : next+e0.length=(heap++e0).length := by simp [dense]
      obtain ⟨e1,out,tailRun,heapOut,nextOut,stackOut,sourceOut,pcOut,rep⟩ :=
        normalize_state label capacity (initial capacity delta).1
          (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn (initial capacity delta).1).1
          (a:=dr) (b:=ctx) (list_extend row e0) weights frame choice (next+e0.length) dense0 source
      refine ⟨ot,out,run_append firstRun tailRun,sourceOut,stackOut,pcOut,?_,?_,?_,bound⟩
      · rw [nextOut,heapOut];simp [dense,Nat.add_assoc]
      · exact ⟨e0++e1,by simpa [List.append_assoc] using heapOut⟩
      · exact rep
end DirectedFlowCutGap.PackingStart
