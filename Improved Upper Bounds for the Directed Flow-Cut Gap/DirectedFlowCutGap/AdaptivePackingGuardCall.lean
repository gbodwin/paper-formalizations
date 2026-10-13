import DirectedFlowCutGap.AdaptivePackingStateProgram

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem guard_return {n : ℕ} (capacity : Row n) (s : BinaryFractionalCore.State n)
    (labels : Fin n → Bits) {heap : NaturalHeap} {a b : ℕ}
    (row : StoredList heap a capacity.toList) (record : PackingStart.StateRecord heap b labels s)
    (next c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 4800) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext flag,ext.length=PackingGuard.cells capacity.toList s.weights.toList ∧
      NaturalRun program (PackingGuard.steps capacity.toList s.weights.toList+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 470) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c flag stack source pc) ∧
      (heap++ext)[flag]?=some (.flag (BinaryRational.le one (objective capacity s.weights).1).1) ∧
      PackingStart.StateRecord (heap++ext) b labels s := by
  obtain ⟨ext,oneRoot,cost,flag,len,high,bit,_,rep,_⟩ :=
    PackingGuard.state_guard capacity s labels row record next c d dense source
  have lifted := ReferenceProgramLabels.run guardLabel PackingGuard.program program guard_slots high
  have lifted := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lifted
  have body : NaturalRun program (PackingGuard.steps capacity.toList s.weights.toList)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 470) []
      (state (heap++ext) (next+ext.length) oneRoot cost (next+1) flag (⟨pc,.r3,saved⟩::stack) source 480) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramStack.state,guardLabel,state,PackingGuard.state] using lifted
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) oneRoot cost (next+1) flag (⟨pc,.r3,saved⟩::stack) source 480)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c flag stack source pc,[],0⟩ := by
    simp [tickNatural,program,callable,PackingGuard.program,state,Registers.get,Registers.set]
  have append {s u v : NaturalState 4800} {t k : ℕ} {events more : List Event}
      (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
      NaturalRun program (t+k) s (events++more) v := by
    induction h with
    | done s => simpa using g
    | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
        using NaturalRun.step ht (ih g)
  exact ⟨ext,flag,len,by simpa using append body (.step ret (.done _)),bit,rep⟩

theorem stopped_high {n : ℕ} (capacity : Row n) (s : BinaryFractionalCore.State n)
    (labels : Fin n → Bits) (stopped : (BinaryRational.le one (objective capacity s.weights).1).1=true)
    {heap : NaturalHeap} {a b : ℕ} (row : StoredList heap a capacity.toList)
    (record : PackingStart.StateRecord heap b labels s)
    (next c d : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ ext,ext.length=PackingGuard.cells capacity.toList s.weights.toList ∧
      NaturalRun program (PackingGuard.steps capacity.toList s.weights.toList+4)
        (state heap next a b c d [] source 4400) []
        (state (heap++ext) (next+ext.length) a b c b [] source 4799) ∧
      PackingStart.StateRecord (heap++ext) b labels s := by
  obtain ⟨ext,flag,len,body,bit,rep⟩ :=
    guard_return capacity s labels row record next c d dense ⟨a,b,c,d⟩ 4401 [] source
  rw [stopped] at bit
  have slot4400 : program 4400=.call 470 4401 .r3 := rfl
  have slot4401 : program 4401=.branch .r3 4799 4402 4798 4799 := rfl
  have slot4798 : program 4798=.move .r3 .r1 4799 := rfl
  have t4400 : tickNatural program (state heap next a b c d [] source 4400)=
      some ⟨state heap next a b c d [⟨4401,.r3,⟨a,b,c,d⟩⟩] source 470,[],0⟩ := by
    simp [tickNatural,state,slot4400]
  have t4401 : tickNatural program (state (heap++ext) (next+ext.length) a b c flag [] source 4401)=
      some ⟨state (heap++ext) (next+ext.length) a b c flag [] source 4798,[],0⟩ := by
    simp [tickNatural,state,slot4401,Registers.get,tagBranch,bit]
  have t4798 : tickNatural program (state (heap++ext) (next+ext.length) a b c flag [] source 4798)=
      some ⟨state (heap++ext) (next+ext.length) a b c b [] source 4799,[],0⟩ := by
    simp [tickNatural,state,slot4798,Registers.get,Registers.set]
  have append {s u v : NaturalState 4800} {t k : ℕ} {events more : List Event}
      (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
      NaturalRun program (t+k) s (events++more) v := by
    induction h with
    | done s => simpa using g
    | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
        using NaturalRun.step ht (ih g)
  exact ⟨ext,len,by simpa [Nat.add_assoc] using
    (append (.step t4400 body) (.step t4401 (.step t4798 (.done _)))),rep⟩
end DirectedFlowCutGap.AdaptivePackingState
