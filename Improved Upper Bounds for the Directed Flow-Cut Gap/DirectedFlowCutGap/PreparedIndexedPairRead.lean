import DirectedFlowCutGap.PackedWordPairTable
import DirectedFlowCutGap.BinaryIndexedPairRead

/-! Construct the actual stored row and padded index word, then invoke one
concrete indexed-record program. Representation preparation has its explicit
Boolean/list primitive charge; the reader itself is a single instruction run.
No graph-level callback substitution or uncharged natural index conversion is
asserted. -/
namespace DirectedFlowCutGap.PreparedIndexedPairRead
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor


def inputSize (rows : List (Bits × Bits)) (word : Bits) : ℕ :=
  rows.length+PackedWordPairTable.storedBits rows+word.length+1

def initial (rows : List (Bits × Bits)) (word source : Bits) : BitState 26 × ℕ :=
  let table := PackedWordPairTable.construct rows
  let index := PackedWordPairTable.word word table
  (⟨index.heap,index.next,⟨index.root,table.root,[],[]⟩,[],25,source⟩,index.operations+12)

theorem initial_spec (rows : List (Bits × Bits)) (word source : Bits) :
    (initial rows word source).1.Bounded (5*inputSize rows word) (5*inputSize rows word) ∧
    value (initial rows word source).1.next=(initial rows word source).1.heap.length ∧
    BoolList (eraseState (initial rows word source).1).heap
      (eraseState (initial rows word source).1).registers.a word ∧
    WordPairTableRead.Table (eraseState (initial rows word source).1).heap
      (eraseState (initial rows word source).1).registers.b rows ∧
    (initial rows word source).1.heap.length=
      2+4*rows.length+2*PackedWordPairTable.storedBits rows+2*word.length ∧
    (initial rows word source).2 ≤ 4096*(inputSize rows word)^3+12 := by
  have ht := PackedWordPairTable.construct_valid rows
  have hw := PackedWordPairTable.word_spec word ht.bound
  have hsize : (PackedWordPairTable.word word (PackedWordPairTable.construct rows)).heap.length=
      2+4*rows.length+2*PackedWordPairTable.storedBits rows+2*word.length := by
    rw [hw.length,ht.length]
    omega
  have hs : (PackedWordPairTable.word word (PackedWordPairTable.construct rows)).heap.length ≤
      4*inputSize rows word := by rw [hsize]; unfold inputSize; omega
  have hz : 1 ≤ inputSize rows word := by unfold inputSize; omega
  have hroot := ht.bound.root_width.trans hw.extension.length_le
  refine ⟨?_,hw.bound.next_value,hw.representation,hw.extension.table ht.representation,hsize,?_⟩
  · simp only [initial,State.Bounded,State.records,List.length_nil,Nat.add_zero,
      Registers.All,List.not_mem_nil,false_implies]
    exact ⟨by omega,hw.bound.next_width.trans (by omega),
      heapBound_mono hw.bound.heap_bound (by omega),
      ⟨hw.bound.root_width.trans (by omega),hroot.trans (by omega),by omega,by omega⟩,
      fun _ => trivial⟩
  · change (PackedWordPairTable.word word (PackedWordPairTable.construct rows)).operations+12 ≤ _
    have hh := hw.bound.charge
    have hp := Nat.pow_le_pow_left hs 3
    nlinarith

theorem total_bound (rows : List (Bits × Bits)) (word : Bits) (hi : value word < rows.length) :
    4096*(inputSize rows word)^3+12+
      completeBound 26 (5*inputSize rows word) (5*inputSize rows word)
        (BinaryIndexedPairRead.steps word) ≤ 3000000*(inputSize rows word)^3 := by
  let z := inputSize rows word
  have hz : 1 ≤ z := by dsimp [z,inputSize]; omega
  have ht : BinaryIndexedPairRead.steps word ≤ 10*z := by
    have := BinaryIndexedPairRead.steps_bound word
    dsimp [z,inputSize]
    omega
  have hs : 5*z+5*z+2*BinaryIndexedPairRead.steps word+1 ≤ 31*z := by omega
  have hr : 5*z+BinaryIndexedPairRead.steps word+1 ≤ 16*z := by omega
  unfold completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 4096*z^3+12+(170*(10*z)*(31*z)^2+170*(16*z)*(16*z)) := by gcongr
    _ ≤ 3000000*z^3 := by
      have hz2 : 1 ≤ z^2 := by nlinarith
      have hz3 : z^2 ≤ z^3 := by nlinarith
      nlinarith

/-- All row/index representation, dense cursor and bounded-state premises are
supplied by the actual constructor. Padding counts in the single input-size
bound, and the finite index bound stays explicit. -/
theorem read (rows : List (Bits × Bits)) (word source : Bits) (hi : value word < rows.length) :
    ∃ charge out, Run BinaryIndexedPairRead.program (BinaryIndexedPairRead.steps word) charge
        (initial rows word source).1 [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a rows[value word].1 ∧
      BoolList (eraseState out).heap (eraseState out).registers.b rows[value word].2 ∧
      (∃ extra,(eraseState out).heap=(eraseState (initial rows word source).1).heap++extra ∧
        extra.length=value word+1) ∧
      value out.next=out.heap.length ∧ out.stack=[] ∧ out.source=source ∧ out.pc=24 ∧
      (attempt BinaryIndexedPairRead.program out).result=none ∧
      (initial rows word source).2+charge+(attempt BinaryIndexedPairRead.program out).operations ≤
        3000000*(inputSize rows word)^3 := by
  obtain ⟨bounded,hn,wordRep,table,_,cost⟩ := initial_spec rows word source
  obtain ⟨charge,out,run,ra,rb,ext,dense,frames,src,pc,_,_,halt,hc⟩ :=
    BinaryIndexedPairRead.read_bit (initial rows word source).1 bounded rfl hn rfl wordRep table hi
  refine ⟨charge,out,run,ra,rb,ext,dense,frames,src,pc,halt,?_⟩
  have hb := total_bound rows word hi
  omega

end DirectedFlowCutGap.PreparedIndexedPairRead
