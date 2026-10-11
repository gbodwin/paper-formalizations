import DirectedFlowCutGap.CounterPrefixProgram

/-! Prepare only the incoming binary word, then execute the single actual
counter/source program. Unary expansion is performed by the instruction table.
The remaining initial representation constructor is charged Boolean/list code. -/
namespace DirectedFlowCutGap.PreparedCounterPrefix
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def initial (word source : Bits) : BitState 24 × ℕ :=
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

/-- Actual input-word construction discharges every representation and width
premise. The successful instruction count depends on the represented number,
but no decoded natural drives the executed instruction table. -/
theorem materialize (word source : Bits) (enough : value word ≤ source.length) :
    ∃ charge out,
      Run CounterPrefixProgram.program (CounterPrefixProgram.steps word) charge
        (initial word source).1 ((source.take (value word)).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a
        (source.take (value word)).reverse ∧
      out.source=source.drop (value word) ∧ out.pc=22 ∧
      out.heap.length=2*word.length+3*value word+3 ∧
      value out.next=out.heap.length ∧ out.stack=[] ∧
      out.Bounded ((2*word.length+2)+CounterPrefixProgram.steps word)
        ((2*word.length+2)+CounterPrefixProgram.steps word) ∧
      (attempt CounterPrefixProgram.program out).result=none ∧
      (initial word source).2+charge+(attempt CounterPrefixProgram.program out).operations ≤
        preparationBound word+completeBound 24 (2*word.length+2) (2*word.length+2)
          (CounterPrefixProgram.steps word) := by
  obtain ⟨bounded,hn,table,cost⟩ := initial_spec word source
  obtain ⟨charge,out,run,rep,src,pc,len,dense,frames,_,bound,halt,hc⟩ :=
    CounterPrefixProgram.materialize_bit (initial word source).1 bounded rfl hn table rfl enough
  refine ⟨charge,out,run,rep,src,pc,?_,dense,frames,bound,halt,?_⟩
  · simp only [initial,(construct_valid word).heap_length] at len
    omega
  · omega

/-- A coarse output-sensitive polynomial for this complete materializer,
including the paid input-word heap construction and final halt. -/
theorem total_bound (word : Bits) :
    preparationBound word+completeBound 24 (2*word.length+2) (2*word.length+2)
      (CounterPrefixProgram.steps word) ≤ 2000000*(value word+word.length+1)^3 := by
  let z := value word+word.length+1
  have hz : 1 ≤ z := by dsimp [z]; omega
  have hl : word.length+1 ≤ z := by dsimp [z]; omega
  have ht : CounterPrefixProgram.steps word ≤ 10*z := by
    have := CounterPrefixProgram.steps_bound word
    dsimp [z]
    omega
  have hh : 2*word.length+2 ≤ 2*z := by omega
  have hs : (2*word.length+2)+(2*word.length+2)+2*CounterPrefixProgram.steps word+1 ≤ 25*z := by omega
  have hr : (2*word.length+2)+CounterPrefixProgram.steps word+1 ≤ 13*z := by omega
  unfold preparationBound completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 128*z^3+12+(168*(10*z)*(25*z)^2+168*(13*z)*(13*z)) := by gcongr
    _ ≤ 2000000*z^3 := by
      have hz2 : 1 ≤ z^2 := by nlinarith
      have hz3 : z^2 ≤ z^3 := by nlinarith
      nlinarith

end DirectedFlowCutGap.PreparedCounterPrefix
