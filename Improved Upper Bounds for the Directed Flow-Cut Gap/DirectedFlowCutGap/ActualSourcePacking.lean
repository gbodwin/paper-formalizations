import DirectedFlowCutGap.SourcePackingExecution

namespace DirectedFlowCutGap.SourcePacking
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation ImmutableReferenceTerminal

def initial (source : Bits) : BitState 8490 := ⟨[],[],⟨[],[],[],[]⟩,[],48,source⟩

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

/-- The complete physical machine starts with only an encoded source and an
empty heap. The old state and all input-request events belong to this same run. -/
theorem solve_source_bit {n : ℕ} (capacity : Row n) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (hn : 0<n) (suffix : Bits) :
    ∃ k charge out, Run program k charge (initial (encode capacity adjacency ds++suffix))
      ((encode capacity adjacency ds).map Event.request) out ∧
      PackingStart.StateRecord (eraseState out).heap (eraseState out).registers.d RowVertices.vertexLabel
        (BinaryFractionalCore.solveInput capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).state ∧
      out.source=suffix ∧ out.stack=[] ∧ out.pc=8485 ∧ value out.next=out.heap.length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 8490 1 0
        (instructionBound capacity adjacency ds) := by
  obtain ⟨k,ext,cap,mat,root,high,rep,bound⟩ := solve_source capacity adjacency ds hn suffix [] 0 0 0 0 0 rfl
  have start : state [] 0 0 0 0 0 [] (encode capacity adjacency ds++suffix) 48=
      eraseState (initial (encode capacity adjacency ds++suffix)) := by rfl
  rw [start] at high
  have halt : tickNatural program (state ([]++ext) (0+ext.length) cap mat mat root [] suffix 8485)=none := by
    simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,_⟩ := polynomial_simulation
    (initial_bounded (encode capacity adjacency ds++suffix)) high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨k,charge,out,run,?_,?_,?_,?_,?_,stop,
    (terminal_accounting run (initial_bounded _) stop).2.trans
      (SupportSearchEncoding.complete_mono 8490 1 0 _ _ bound)⟩
  · simpa only [erase,state] using rep
  · have h : (eraseState out).source=suffix := by rw [erase];rfl
    exact h
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=8485 := by rw [erase];rfl
    exact h
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];simp [state]
    simpa [eraseState,State.map] using h

end DirectedFlowCutGap.SourcePacking
