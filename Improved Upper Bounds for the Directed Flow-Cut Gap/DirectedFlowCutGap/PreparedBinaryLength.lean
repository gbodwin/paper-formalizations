import DirectedFlowCutGap.BinaryLengthProgram

/-! An actual heap scan constructs a binary stored-length word. Only the input
Boolean-list packing remains outside the fixed24-slot instruction program. -/
namespace DirectedFlowCutGap.PreparedBinaryLength
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def initial (word source : Bits) : BitState 24 × ℕ :=
  let s := construct word
  (⟨s.heap,s.next,⟨s.root,[],[],[]⟩,[],16,source⟩,s.operations+12)

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

/-- The result is a concrete represented binary count of every input cell,
including padding, obtained by the same real scan and recursive increments. -/
theorem measure (word source : Bits) :
    ∃ charge out, Run BinaryLengthProgram.program
        (1+BinaryLengthProgram.scanSteps word.length []) charge (initial word source).1 [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.b
        (BinaryLengthProgram.countWord word.length []) ∧
      value (BinaryLengthProgram.countWord word.length []) = word.length ∧
      BoolList (eraseState out).heap (eraseState (initial word source).1).registers.a word ∧
      out.source = source ∧ out.pc = 22 ∧ out.stack = [] ∧
      out.heap.length = 2*word.length+2+BinaryLengthProgram.scanCells word.length [] ∧
      value out.next = out.heap.length ∧
      (attempt BinaryLengthProgram.program out).result = none ∧
      (initial word source).2+charge+(attempt BinaryLengthProgram.program out).operations ≤
        preparationBound word+completeBound 24 (2*word.length+2) (2*word.length+2)
          (1+BinaryLengthProgram.scanSteps word.length []) := by
  obtain ⟨bounded,hn,rep,cost⟩ := initial_spec word source
  obtain ⟨charge,out,run,stored,count,original,len,dense,frames,src,pc,halt,hcharge⟩ :=
    BinaryLengthProgram.length_bit (initial word source).1 bounded rfl hn rep rfl
  refine ⟨charge,out,run,stored,count,original,src,pc,frames,?_,dense,halt,?_⟩
  · simp only [initial,(construct_valid word).heap_length] at len
    omega
  · omega

/-- A coarse stored-length polynomial pays input preparation, actual scanning,
all binary carry calls and one final halt. No logarithmic-cost claim is made. -/
theorem total_bound (word : Bits) :
    preparationBound word+completeBound 24 (2*word.length+2) (2*word.length+2)
      (1+BinaryLengthProgram.scanSteps word.length []) ≤ 15000000*(word.length+1)^6 := by
  let z := word.length+1
  have hz : 1 ≤ z := by dsimp [z];omega
  have hz2 : z ≤ z^2 := by nlinarith
  have ht : 1+BinaryLengthProgram.scanSteps word.length [] ≤ 22*z^2 := by
    have h := BinaryLengthProgram.scanSteps_bound word.length []
    simp only [List.length_nil,Nat.zero_add] at h
    dsimp [z]
    nlinarith
  have hh : 2*word.length+2 ≤ 2*z^2 := by dsimp [z] at *;nlinarith
  have hs : (2*word.length+2)+(2*word.length+2)+
      2*(1+BinaryLengthProgram.scanSteps word.length [])+1 ≤ 49*z^2 := by nlinarith
  have hr : (2*word.length+2)+(1+BinaryLengthProgram.scanSteps word.length [])+1 ≤ 25*z^2 := by nlinarith
  unfold preparationBound completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 128*z^3+12+(168*(22*z^2)*(49*z^2)^2+168*(25*z^2)*(25*z^2)) := by gcongr
    _ ≤ 15000000*z^6 := by
      have hz3 : 1 ≤ z^3 := by nlinarith
      have hz4 : z^3 ≤ z^4 := by nlinarith [sq_nonneg (z^2-z)]
      have hz6 : z^4 ≤ z^6 := by nlinarith [sq_nonneg (z^3-z^2)]
      nlinarith

end DirectedFlowCutGap.PreparedBinaryLength
