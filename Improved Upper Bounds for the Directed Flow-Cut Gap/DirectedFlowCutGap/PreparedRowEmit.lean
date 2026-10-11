import DirectedFlowCutGap.PreparedIndexedPairRead
import DirectedFlowCutGap.IndexedPairEmit

/-! Exact selected-field output from the constructed row heap. Setup uses the
same declared Boolean/list constructor; one36-slot lower run emits every stored
bit and pays its halt. Concatenation is specified, not self-delimiting encoding. -/
namespace DirectedFlowCutGap.PreparedRowEmit
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def initial (rows : List (Bits × Bits)) (word source : Bits) : BitState 36 × ℕ :=
  let p := PreparedIndexedPairRead.initial rows word source
  (⟨p.1.heap,p.1.next,p.1.registers,[],25,p.1.source⟩,p.2+12)

theorem field_length (rows : List (Bits × Bits)) (q : ℕ) (hq : q<rows.length) :
    rows[q].1.length+rows[q].2.length ≤ PackedWordPairTable.storedBits rows := by
  induction rows generalizing q with
  | nil => simp at hq
  | cons row rows ih =>
      cases q with
      | zero => simp [PackedWordPairTable.storedBits_cons]
      | succ q =>
          have h := ih q (by simpa using hq)
          simpa only [List.getElem_cons_succ,PackedWordPairTable.storedBits_cons] using
            h.trans (Nat.le_add_left _ _)

theorem initial_spec (rows : List (Bits × Bits)) (word source : Bits) :
    (initial rows word source).1.Bounded
      (5*PreparedIndexedPairRead.inputSize rows word) (5*PreparedIndexedPairRead.inputSize rows word) ∧
    value (initial rows word source).1.next=(initial rows word source).1.heap.length ∧
    BoolList (eraseState (initial rows word source).1).heap
      (eraseState (initial rows word source).1).registers.a word ∧
    WordPairTableRead.Table (eraseState (initial rows word source).1).heap
      (eraseState (initial rows word source).1).registers.b rows ∧
    (initial rows word source).2 ≤ 4096*(PreparedIndexedPairRead.inputSize rows word)^3+24 := by
  obtain ⟨bounded,dense,wordRep,table,_,cost⟩ := PreparedIndexedPairRead.initial_spec rows word source
  refine ⟨?_,dense,wordRep,table,?_⟩
  · simpa [initial,PreparedIndexedPairRead.initial,State.Bounded,State.records] using bounded
  · change (PreparedIndexedPairRead.initial rows word source).2+12 ≤ _
    omega

theorem total_bound (rows : List (Bits × Bits)) (word : Bits) (hi : value word<rows.length) :
    4096*(PreparedIndexedPairRead.inputSize rows word)^3+24+
      completeBound 36 (5*PreparedIndexedPairRead.inputSize rows word) (5*PreparedIndexedPairRead.inputSize rows word)
        (IndexedPairEmit.steps word rows[value word].1 rows[value word].2) ≤
      10000000*(PreparedIndexedPairRead.inputSize rows word)^3 := by
  let z := PreparedIndexedPairRead.inputSize rows word
  let t := IndexedPairEmit.steps word rows[value word].1 rows[value word].2
  have hz : 1≤z := by dsimp [z,PreparedIndexedPairRead.inputSize];omega
  have ht : t≤18*z := by
    have hr := BinaryIndexedPairRead.steps_bound word
    have hl := field_length rows (value word) hi
    dsimp [t,IndexedPairEmit.steps,z,PreparedIndexedPairRead.inputSize]
    omega
  have hs : 5*z+5*z+2*t+1≤47*z := by omega
  have hb : 5*z+t+1≤24*z := by omega
  unfold completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 4096*z^3+24+(180*(18*z)*(47*z)^2+180*(24*z)*(24*z)) := by gcongr
    _ ≤ 10000000*z^3 := by
      have hz2 : 1≤z^2 := by nlinarith
      have hz3 : z^2≤z^3 := by nlinarith
      nlinarith

/-- The only data-validity premise is a finite index bound. The source is
unchanged; every output bit belongs to the exact selected padded stored words. -/
theorem emit (rows : List (Bits × Bits)) (word source : Bits) (hi : value word<rows.length) :
    ∃ charge out, Run IndexedPairEmit.program
        (IndexedPairEmit.steps word rows[value word].1 rows[value word].2) charge
        (initial rows word source).1 ((rows[value word].1++rows[value word].2).map Event.emit) out ∧
      out.source=source ∧ out.pc=35 ∧ out.stack=[] ∧
      value out.next=out.heap.length ∧
      (attempt IndexedPairEmit.program out).result=none ∧
      (initial rows word source).2+charge+(attempt IndexedPairEmit.program out).operations ≤
        10000000*(PreparedIndexedPairRead.inputSize rows word)^3 := by
  obtain ⟨bound,dense,wordRep,table,cost⟩ := initial_spec rows word source
  obtain ⟨charge,out,run,_,hn,hs,hsrc,hpc,halt,hcharge⟩ :=
    IndexedPairEmit.emit_bit (initial rows word source).1 bound rfl dense rfl wordRep table hi
  refine ⟨charge,out,run,hsrc,hpc,hs,hn,halt,?_⟩
  have h := total_bound rows word hi
  omega

end DirectedFlowCutGap.PreparedRowEmit
