import DirectedFlowCutGap.GraphRecoveryContext
import DirectedFlowCutGap.GraphDiscoveryExecution

namespace DirectedFlowCutGap.GraphRecoveryController
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

theorem discovery_call {heap : NaturalHeap} {a b c : ℕ} {vs adjacency : List Bits}
    {rows : List Fraction} {sw target u : Bits}
    (input : GraphDiscoveryProgram.Vertices heap a vs)
    (context : GraphDiscoveryProgram.GlobalContext heap b vs adjacency rows sw target)
    (word : BoolList heap c u)
    (hi : ∀ v∈vs,value v<adjacency.length) (hc : ∀ v∈vs,value v<rows.length)
    (targetCol : ∀ v,(hv : v∈vs) → value target<(adjacency[value v]'(hi v hv)).length)
    (columns : ∀ v,(hv : v∈vs) → ∀ z∈vs,value z<(adjacency[value v]'(hi v hv)).length)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1344)
    (stack : List (Frame ℕ 1344)) (source : Bits) :
    ∃ ext root,ext.length=GraphDiscoveryProgram.minimizeCells vs adjacency rows sw target u ∧
      NaturalRun program (GraphDiscoveryProgram.minimizeSteps vs adjacency rows sw target u+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 717) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root
        (GraphDiscoveryProgram.minimize vs adjacency rows sw target u) := by
  obtain ⟨ext,root,len,high,rep⟩ := GraphDiscoveryProgram.minimize_high
    (GraphDiscoveryProgram.state heap next a b c d [] source 717) rfl hn rfl input context word hi hc targetCol columns
  let frames := (⟨pc,.r3,saved⟩::stack)
  have mapped := ReferenceProgramLabels.run discoveryLabel GraphDiscoveryProgram.program program discovery_slots high
  have lifted := ReferenceProgramStack.run program frames mapped
  have body : NaturalRun program (GraphDiscoveryProgram.minimizeSteps vs adjacency rows sw target u+1)
      (state heap next a b c d frames source 717) []
      (state (heap++ext) (next+ext.length) a b c root frames source 719) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      GraphDiscoveryProgram.state,discoveryLabel,state] using lifted
  have ret : tickNatural program (state (heap++ext) (next+ext.length) a b c root frames source 719)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

theorem recovery_call {heap : NaturalHeap} {a b c : ℕ} {vs adjacency : List Bits}
    {es : List (Bits×Bits)} {sw target : Bits} {values : List Fraction} (N : ℕ)
    (vertices : SupportRecoveryProgram.Vertices heap a vs)
    (context : CostedSupportProgram.Context heap b vs adjacency es target values sw) (word : BoolList heap c sw)
    (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vs,value u<N) (ht : value target<N)
    (valid : ∀ w∈(CostedSupportProgram.edges vs adjacency es sw target).map Prod.fst,value w<values.length)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1344)
    (stack : List (Frame ℕ 1344)) (source : Bits) :
    ∃ ext root,ext.length=CostedSupportProgram.cells vs adjacency es sw target values ∧
      NaturalRun program (CostedSupportProgram.steps vs adjacency es sw target values+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1310) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredWalk (heap++ext) root (CostedSupportProgram.result vs adjacency es sw target values) := by
  obtain ⟨ext,root,len,high,rep⟩ := CostedSupportProgram.recover_high N
    (CostedSupportProgram.state heap next a b c d [] source 590) rfl hn rfl vertices context word rows cols hv ht valid
  let frames := (⟨pc,.r3,saved⟩::stack)
  have mapped := ReferenceProgramLabels.run recoveryLabel CostedSupportProgram.program program recovery_slots high
  have lifted := ReferenceProgramStack.run program frames mapped
  have body : NaturalRun program (CostedSupportProgram.steps vs adjacency es sw target values+1)
      (state heap next a b c d frames source 1310) []
      (state (heap++ext) (next+ext.length) a b c root frames source 1311) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CostedSupportProgram.state,recoveryLabel,state] using lifted
  have ret : tickNatural program (state (heap++ext) (next+ext.length) a b c root frames source 1311)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

end DirectedFlowCutGap.GraphRecoveryController
