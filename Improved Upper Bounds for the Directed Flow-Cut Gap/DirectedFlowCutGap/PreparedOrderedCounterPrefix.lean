import DirectedFlowCutGap.OrderedCounterPrefix

/-! Prepare only the incoming binary word, then execute the single actual
counter/source/ordered-storage program. Unary expansion is performed by the instruction table.
The remaining initial representation constructor is charged Boolean/list code. -/
namespace DirectedFlowCutGap.PreparedOrderedCounterPrefix
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def initial (word source : Bits) : BitState 30 × ℕ :=
  let s := construct word
  (⟨s.heap,s.next,⟨s.root,[],[],[]⟩,[],23,source⟩,s.operations+12)

def preparationBound (word : Bits) : ℕ := 128*(word.length+1)^3+12

theorem initial_spec (word source : Bits) :
    (initial word source).1.Bounded (2*word.length+2) (2*word.length+2) ∧
    value (initial word source).1.next=(initial word source).1.heap.length ∧
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

/-- Actual construction supplies every input-word representation premise.
The stored result is the literal requested prefix, not its reversal. -/
theorem materialize (word source : Bits) (enough : value word ≤ source.length) :
    ∃ charge out, Run OrderedCounterPrefix.program (OrderedCounterPrefix.steps word) charge
        (initial word source).1 ((source.take (value word)).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.b (source.take (value word)) ∧
      out.source=source.drop (value word) ∧ out.pc=29 ∧
      out.heap.length=2*word.length+4*value word+4 ∧
      value out.next=out.heap.length ∧ out.stack=[] ∧
      (attempt OrderedCounterPrefix.program out).result=none ∧
      (initial word source).2+charge+(attempt OrderedCounterPrefix.program out).operations ≤
        preparationBound word+completeBound 30 (2*word.length+2) (2*word.length+2)
          (OrderedCounterPrefix.steps word) := by
  obtain ⟨bounded,hn,rep,cost⟩ := initial_spec word source
  obtain ⟨charge,out,run,stored,src,pc,len,dense,frames,halt,hcharge⟩ :=
    OrderedCounterPrefix.materialize_bit (initial word source).1 bounded rfl hn rep rfl enough
  refine ⟨charge,out,run,stored,src,pc,?_,dense,frames,halt,?_⟩
  · simp only [initial,(construct_valid word).heap_length] at len
    omega
  · omega

/-- One output-sensitive polynomial includes actual word preparation, all
counter/request/reversal instructions and the final halt. -/
theorem total_bound (word : Bits) :
    preparationBound word+completeBound 30 (2*word.length+2) (2*word.length+2)
      (OrderedCounterPrefix.steps word) ≤ 2000000*(value word+word.length+1)^3 := by
  let z := value word+word.length+1
  have hz : 1 ≤ z := by dsimp [z];omega
  have hl : word.length+1 ≤ z := by dsimp [z];omega
  have ht : OrderedCounterPrefix.steps word ≤ 11*z := by
    have := OrderedCounterPrefix.steps_bound word
    dsimp [z]
    omega
  have hh : 2*word.length+2 ≤ 2*z := by omega
  have hs : (2*word.length+2)+(2*word.length+2)+2*OrderedCounterPrefix.steps word+1 ≤ 27*z := by omega
  have hr : (2*word.length+2)+OrderedCounterPrefix.steps word+1 ≤ 14*z := by omega
  unfold preparationBound completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 128*z^3+12+(174*(11*z)*(27*z)^2+174*(14*z)*(14*z)) := by gcongr
    _ ≤ 2000000*z^3 := by
      have hz2 : 1 ≤ z^2 := by nlinarith
      have hz3 : z^2 ≤ z^3 := by nlinarith
      nlinarith

end DirectedFlowCutGap.PreparedOrderedCounterPrefix
