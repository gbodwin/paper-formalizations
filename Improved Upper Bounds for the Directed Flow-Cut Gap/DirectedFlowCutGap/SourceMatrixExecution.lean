import DirectedFlowCutGap.SourceMatrixProjection

namespace DirectedFlowCutGap.SourceMatrixProjection
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor WordPairTableRead GraphDiscoveryProgram

theorem vertices_matrix {heap : NaturalHeap} {p : ℕ} {rows : List Bits}
    (h : Vertices heap p rows) : GraphAdjacencyProgram.Matrix heap p rows := by
  induction h with
  | nil hp => exact ⟨[],rfl,.nil hp,by simp⟩
  | @cons root head tail word words hp hw ht ih =>
    obtain ⟨roots,len,rep,hr⟩ := ih
    refine ⟨head::roots,by simpa using len,.cons hp rep,?_⟩
    intro i hi
    cases i with
    | zero => exact hw
    | succ i => simpa using hr i (by simpa using hi)

theorem project {heap : NaturalHeap} {a : ℕ} {rows : List (Bits × Bits)}
    (table : Table heap a rows) (next b c d : ℕ) (hn : next=heap.length)
    (stack : List (Frame ℕ 16)) (source : Bits) :
    ∃ ext root, ext.length=rows.length+1 ∧
      NaturalRun program (7*rows.length+4) (state heap next a b c d stack source 14) []
        (state (heap++ext) (next+ext.length) a b c root stack source 15) ∧
      GraphAdjacencyProgram.Matrix (heap++ext) root (rows.map Prod.fst) := by
  obtain ⟨ext,root,len,run,rep⟩ := project_return table next b c d hn ⟨a,b,c,d⟩ 15 stack source
  have call : tickNatural program (state heap next a b c d stack source 14)=
      some ⟨state heap next a b c d (⟨15,.r3,⟨a,b,c,d⟩⟩::stack) source 0,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using NaturalRun.step call run,vertices_matrix rep⟩

theorem project_bit {H A : ℕ} {rows : List (Bits × Bits)}
    (initial : BitState 16) (bounded : initial.Bounded H A) (pc0 : initial.pc=14)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : Table (eraseState initial).heap (eraseState initial).registers.a rows) :
    ∃ charge out, Run program (7*rows.length+4) charge initial [] out ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap (eraseState out).registers.d
        (rows.map Prod.fst) ∧
      Table (eraseState out).heap (eraseState initial).registers.a rows ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=15 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=rows.length+1) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 16 H A (7*rows.length+4) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 14=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := project table (eraseState initial).next
    (eraseState initial).registers.b (eraseState initial).registers.c (eraseState initial).registers.d
    dense' (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 15)=none := by simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,sourceOut,?_,?_,⟨ext,?_,len⟩,stop,
    (terminal_accounting run bounded stop).2⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact BinaryIndexedPairRead.table_extend table ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=15 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.SourceMatrixProjection
