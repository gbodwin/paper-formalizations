import DirectedFlowCutGap.BinaryIncrementProgram

/-! Actual Boolean input-word preparation joined to the literal sixteen-slot
increment program. The machine handles arbitrary stored padding and preserves
its input word and source. Input preparation remains paid Boolean/list code. -/
namespace DirectedFlowCutGap.PreparedBinaryIncrement
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def initial (word source : Bits) : BitState 16 × ℕ :=
  let s := construct word
  (⟨s.heap,s.next,⟨s.root,[],[],[]⟩,[],15,source⟩,s.operations+12)

def preparationBound (word : Bits) : ℕ := 128*(word.length+1)^3+12

theorem initial_spec (word source : Bits) :
    (initial word source).1.Bounded (2*word.length+2) (2*word.length+2) ∧
    value (initial word source).1.next = (initial word source).1.heap.length ∧
    BoolList (eraseState (initial word source).1).heap
      (eraseState (initial word source).1).registers.a word ∧
    (initial word source).2 ≤ preparationBound word := by
  have h := construct_valid word
  have hc := construct_charge word
  refine ⟨?_,h.next_value.trans h.heap_length.symm,h.table,?_⟩
  · simp only [initial,State.Bounded,State.records,List.length_nil,Nat.add_zero,
      Registers.All,List.not_mem_nil,false_implies]
    exact ⟨by rw [h.heap_length],h.next_width.trans (by omega),
      heapBound_mono h.heap_bound (by omega),
      ⟨h.root_width.trans (by omega),by omega,by omega,by omega⟩,fun _ => trivial⟩
  · change (construct word).operations+12 ≤ _
    unfold preparationBound
    omega

/-- No representation or caller hypothesis is supplied by the client. The exact
stored result and original input word coexist in the same resulting heap. -/
theorem increment (word source : Bits) :
    ∃ charge out, Run BinaryIncrementProgram.program (BinaryIncrementProgram.steps word+1)
        charge (initial word source).1 [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d
        (BinaryArithmetic.increment true word).1 ∧
      value (BinaryArithmetic.increment true word).1 = value word+1 ∧
      BoolList (eraseState out).heap (eraseState (initial word source).1).registers.a word ∧
      out.source = source ∧ out.pc = 14 ∧ out.stack = [] ∧
      out.heap.length = 2*word.length+1+BinaryIncrementProgram.cells word ∧
      value out.next = out.heap.length ∧
      (attempt BinaryIncrementProgram.program out).result = none ∧
      (initial word source).2+charge+(attempt BinaryIncrementProgram.program out).operations ≤
        preparationBound word+completeBound 16 (2*word.length+2) (2*word.length+2)
          (BinaryIncrementProgram.steps word+1) := by
  obtain ⟨bounded,hn,rep,cost⟩ := initial_spec word source
  obtain ⟨charge,out,run,stored,original,src,pc,frames,dense,⟨extra,ext,len⟩,_,_,_,halt,hcharge⟩ :=
    BinaryIncrementProgram.increment_bit (initial word source).1 bounded rfl hn rep rfl
  refine ⟨charge,out,run,stored,?_,original,src,pc,frames,?_,dense,halt,?_⟩
  · simpa using (increment_spec true word).1
  · have h := congrArg List.length ext
    simp only [List.length_append,len,eraseState,State.map,List.length_map,initial,
      (construct_valid word).heap_length] at h
    exact h
  · omega

/-- The complete setup, real machine execution, copied caller frames and paid
halt have a polynomial bound in the length of the stored input, not its value. -/
theorem total_bound (word : Bits) :
    preparationBound word+completeBound 16 (2*word.length+2) (2*word.length+2)
      (BinaryIncrementProgram.steps word+1) ≤ 1000000*(word.length+1)^3 := by
  let z := word.length+1
  have hz : 1 ≤ z := by dsimp [z];omega
  have ht : BinaryIncrementProgram.steps word+1 ≤ 8*z := by
    have := BinaryIncrementProgram.steps_bound word
    dsimp [z]
    omega
  have hh : 2*word.length+2 ≤ 2*z := by omega
  have hs : (2*word.length+2)+(2*word.length+2)+
      2*(BinaryIncrementProgram.steps word+1)+1 ≤ 21*z := by omega
  have hr : (2*word.length+2)+(BinaryIncrementProgram.steps word+1)+1 ≤ 11*z := by omega
  unfold preparationBound completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 128*z^3+12+(160*(8*z)*(21*z)^2+160*(11*z)*(11*z)) := by gcongr
    _ ≤ 1000000*z^3 := by
      have hz2 : 1 ≤ z^2 := by nlinarith
      have hz3 : z^2 ≤ z^3 := by nlinarith
      nlinarith

end DirectedFlowCutGap.PreparedBinaryIncrement
