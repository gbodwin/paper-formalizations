import DirectedFlowCutGap.GraphOracleBounds

namespace DirectedFlowCutGap.GraphOracleMachine
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem oracle_high {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (initial : NaturalState 2120) (pc0 : initial.pc=2100)
    (dense : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : DemandCollection.DemandList initial.heap initial.registers.a xs)
    (context : Context initial.heap initial.registers.b label adjacency capacity y) :
    ∃ steps out,NaturalRun program steps initial [] out ∧
      OracleChoice.StoredChoice out.heap out.registers.d label
        (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn y).1 ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.next=out.heap.length ∧
      (∃ ext,out.heap=initial.heap++ext) ∧ program out.pc=.halt ∧
      ∀ W,1≤W → (∀ i,(label i).length≤W) → (∀ q∈y.toList,StoredBounded q W) →
        (∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) →
        steps ≤ instructionBound xs.length n W := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 dense empty input context
      subst pc;subst stack
      obtain ⟨steps,ext,selectedRoot,post,root,run,stored,bound⟩ := oracle_run adjacency capacity y label hlabel hn
        encoded input context next c d dense [] source
      refine ⟨steps,state (heap++ext) (next+ext.length) selectedRoot post next root [] source 2107,
        run,stored,rfl,rfl,by simp [state,dense],⟨ext,rfl⟩,by simp [program,state],?_⟩
      intro W hW labels rows capacities
      have hb := bound W labels capacities
      have hd := DemandCollection.graph_steps_bound adjacency y label hlabel encoded (next+1) W hW labels rows
      have hp := post_steps_bound adjacency y ds rows
      unfold instructionBound
      omega

/-- The same physical finite-table controller discovers all candidate paths,
selects the first minimum, constructs its mask and bottleneck, and pays its
terminal halt. Only original graph/demand/table representations are inputs. -/
theorem oracle_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (initial : BitState 2120) (bounded : initial.Bounded H A) (pc0 : initial.pc=2100)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : DemandCollection.DemandList (eraseState initial).heap (eraseState initial).registers.a xs)
    (context : Context (eraseState initial).heap (eraseState initial).registers.b label adjacency capacity y)
    (W : ℕ) (hW : 1≤W) (labels : ∀ i,(label i).length≤W)
    (rows : ∀ q∈y.toList,StoredBounded q W)
    (capacities : ∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) :
    ∃ steps charge out,Run program steps charge initial [] out ∧
      OracleChoice.StoredChoice (eraseState out).heap (eraseState out).registers.d label
        (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn y).1 ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations≤completeBound 2120 H A (instructionBound ds.length n W) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨steps,final,high,stored,source,stack,_,ext,halt,bound⟩ :=
    oracle_high adjacency capacity y label hlabel hn encoded (eraseState initial) pc0 dense' empty' input context
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have ht : tickNatural program final=none := by simp [tickNatural,halt]
    rw [ht] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  have size : xs.length=ds.length := encoded.length_eq
  have hb := bound W hW labels rows capacities
  rw [size] at hb
  refine ⟨steps,charge,out,run,?_,src.trans source,?_,?_,stop,
    (terminal_accounting run bounded stop).2.trans (SupportSearchEncoding.complete_mono 2120 H A _ _ hb)⟩
  · rw [erase];exact stored
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · rw [erase];exact ext

end DirectedFlowCutGap.GraphOracleMachine
