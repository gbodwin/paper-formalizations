import DirectedFlowCutGap.SourceRowTableProgram
import DirectedFlowCutGap.FractionalHeapRead

/-! One actual program builds the rational-field table and its binary index
from the source, constructs the unary index, and reads the selected stored
pair. No host table constructor, represented input heap or cursor is supplied. -/
namespace DirectedFlowCutGap.SourceRowReadProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def rowLabel (pc : Fin 32) : Fin 68 := ⟨pc.val,by omega⟩
def wordLabel (pc : Fin 10) : Fin 68 := ⟨pc.val+32,by omega⟩
def readLabel (pc : Fin 26) : Fin 68 := ⟨pc.val+42,by omega⟩
def program : Program 68 := fun pc =>
  if pc.val=31 then .move .r1 .r3 41
  else if pc.val=40 then .move .r0 .r3 67
  else if h : pc.val < 32 then
    ReferenceProgramLabels.instruction rowLabel (SourceRowTableProgram.program ⟨pc.val,h⟩)
  else if h : pc.val < 42 then
    ReferenceProgramLabels.instruction wordLabel (SelfDelimitedWordProgram.program ⟨pc.val-32,by omega⟩)
  else ReferenceProgramLabels.instruction readLabel (BinaryIndexedPairRead.program ⟨pc.val-42,by omega⟩)

def initial (source : Bits) : BitState 68 := ⟨[],[],⟨[],[],[],[]⟩,[],30,source⟩
def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 68) : NaturalState 68 :=
  ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩
def instructions (rows : List (Bits × Bits)) (word : Bits) : ℕ :=
  SourceRowTableProgram.steps rows+1+1+(6*word.length+5)+1+BinaryIndexedPairRead.steps word

theorem row_slots (pc : Fin 32) (h : SourceRowTableProgram.program pc ≠ .halt) :
    program (rowLabel pc)=ReferenceProgramLabels.instruction rowLabel (SourceRowTableProgram.program pc) := by
  have hn : pc.val ≠ 31 := by
    intro he
    have eq : pc=31 := Fin.ext he
    subst pc
    exact h rfl
  simp [program,rowLabel,hn,pc.isLt,show pc.val ≠ 40 by omega]

theorem word_slots (pc : Fin 10) (h : SelfDelimitedWordProgram.program pc ≠ .halt) :
    program (wordLabel pc)=ReferenceProgramLabels.instruction wordLabel (SelfDelimitedWordProgram.program pc) := by
  fin_cases pc <;> simp_all [program,wordLabel,SelfDelimitedWordProgram.program]

theorem read_slots (pc : Fin 26) :
    program (readLabel pc)=ReferenceProgramLabels.instruction readLabel (BinaryIndexedPairRead.program pc) := by
  have hn : ¬ pc.val+42 < 32 := by omega
  have hn' : ¬ pc.val+42 < 42 := by omega
  simp [program,readLabel,hn,hn',show pc.val+42 ≠ 31 by omega,show pc.val+42 ≠ 40 by omega]

theorem run_append {s u v : NaturalState 68} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- Literal table construction, source index decoding, unary conversion and
selected read share one heap and source stream. The index bound is explicit. -/
theorem run_high (rows : List (Bits × Bits)) (word suffix : Bits)
    (hi : value word < rows.length) :
    ∃ final, NaturalRun program (instructions rows word)
        (eraseState (initial (SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word++suffix)))
        ((SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word).map Event.request) final ∧
      BoolList final.heap final.registers.a rows[value word].1 ∧
      BoolList final.heap final.registers.b rows[value word].2 ∧
      final.source=suffix ∧ final.pc=66 ∧ final.stack=[] ∧
      final.heap.length=SourceRowTableProgram.cells rows+3*word.length+value word+3 ∧
      final.next=final.heap.length ∧ tickNatural program final=none := by
  obtain ⟨rowsHeap,rowsRoot,rowsLen,rowsRun,rowsRep⟩ := SourceRowTableProgram.read_return rows
    (SelfDelimitedWordProgram.encode word++suffix) [] 0 0 0 0 0 rfl ⟨0,0,0,0⟩ 31 []
  have top : tickNatural SourceRowTableProgram.program
      (SourceRowTableProgram.state [] 0 0 0 0 0 []
        (SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word++suffix) 30)=
      some ⟨SourceRowTableProgram.state [] 0 0 0 0 0 [⟨31,.r3,⟨0,0,0,0⟩⟩]
        (SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word++suffix) 0,[],0⟩ := by
    simp [tickNatural,SourceRowTableProgram.program,SourceRowTableProgram.state]
  have rowsRun' := rowsRun
  simp only [List.nil_append,zero_add] at rowsRun'
  simp only [List.append_assoc] at top
  have relRows := ReferenceProgramLabels.run rowLabel SourceRowTableProgram.program program
    row_slots (NaturalRun.step top rowsRun')
  have nr : SourceRowTableProgram.cells rows=rowsHeap.length := rowsLen.symm
  obtain ⟨wordsHeap,wordRoot,wordLen,wordRun,wordRep⟩ := InputAdditionProgram.reader_high word suffix
    rowsHeap (SourceRowTableProgram.cells rows) 0 rowsRoot 0 rowsRoot nr
  let hw := rowsHeap++wordsHeap
  let nw := SourceRowTableProgram.cells rows+3*word.length+2
  have hn : nw=hw.length := by simp [nw,hw,rowsLen,wordLen,Nat.add_assoc]
  have table : WordPairTableRead.Table hw rowsRoot rows :=
    BinaryIndexedPairRead.table_extend (by simpa using rowsRep) wordsHeap
  obtain ⟨out,readRun,numRep,denRep,ext,dense,frames,source,pc,halt⟩ :=
    BinaryIndexedPairRead.read wordRep table hi nw 0 wordRoot hn suffix
  have relWord := ReferenceProgramLabels.run wordLabel SelfDelimitedWordProgram.program program word_slots wordRun
  have relRead := ReferenceProgramLabels.run readLabel BinaryIndexedPairRead.program program
    (fun pc _ => read_slots pc) readRun
  have first : NaturalRun program (SourceRowTableProgram.steps rows+1)
      (eraseState (initial (SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word++suffix)))
      ((SourceRowTableProgram.encode rows).map Event.request)
      (state rowsHeap (SourceRowTableProgram.cells rows) 0 0 0 rowsRoot
        (SelfDelimitedWordProgram.encode word++suffix) 31) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,rowLabel,
      SourceRowTableProgram.state,state,initial,eraseState,State.map,Registers.map,value,List.append_assoc] using relRows
  have move1 : tickNatural program
      (state rowsHeap (SourceRowTableProgram.cells rows) 0 0 0 rowsRoot
        (SelfDelimitedWordProgram.encode word++suffix) 31)=
      some ⟨state rowsHeap (SourceRowTableProgram.cells rows) 0 rowsRoot 0 rowsRoot
        (SelfDelimitedWordProgram.encode word++suffix) 41,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have second : NaturalRun program (6*word.length+5)
      (state rowsHeap (SourceRowTableProgram.cells rows) 0 rowsRoot 0 rowsRoot
        (SelfDelimitedWordProgram.encode word++suffix) 41)
      ((SelfDelimitedWordProgram.encode word).map Event.request)
      (state hw nw 0 rowsRoot 0 wordRoot suffix 40) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,wordLabel,
      SelfDelimitedWordProgram.state,state,hw,nw] using relWord
  have move2 : tickNatural program (state hw nw 0 rowsRoot 0 wordRoot suffix 40)=
      some ⟨state hw nw wordRoot rowsRoot 0 wordRoot suffix 67,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  let final := ReferenceProgramLabels.state readLabel out
  have third : NaturalRun program (BinaryIndexedPairRead.steps word)
      (state hw nw wordRoot rowsRoot 0 wordRoot suffix 67) [] final := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,readLabel,
      BinaryIndexedPairRead.state,state,final] using relRead
  refine ⟨final,?_,numRep,denRep,source,?_,?_,?_,dense,?_⟩
  · have all := run_append first (NaturalRun.step move1
        (run_append second (NaturalRun.step move2 third)))
    convert all using 1 <;> simp [instructions,List.map_append]; omega
  · simp [final,ReferenceProgramLabels.state,readLabel,pc]
  · simp [final,ReferenceProgramLabels.state,frames]
  · obtain ⟨extra,he,le⟩ := ext
    simp [final,ReferenceProgramLabels.state,he,rowsLen,wordLen,le];omega
  · simp [tickNatural,program,final,ReferenceProgramLabels.state,readLabel,pc,
      ReferenceProgramLabels.instruction,BinaryIndexedPairRead.program]

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

theorem instructions_bound (rows : List (Bits × Bits)) (word : Bits)
    (hi : value word < rows.length) :
    instructions rows word ≤ 40*(SourceRowTableProgram.bits rows+rows.length+word.length+1) := by
  have h := BinaryIndexedPairRead.steps_bound word
  dsimp [instructions,SourceRowTableProgram.steps]
  omega

/-- Same-output paid lower execution from just the specified source encoding.
Denominator validity is not inferred from arbitrary stored field bits. -/
theorem read_from_source (rows : List (Bits × Bits)) (word suffix : Bits)
    (hi : value word < rows.length) :
    ∃ charge out, Run program (instructions rows word) charge
        (initial (SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word++suffix))
        ((SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a rows[value word].1 ∧
      BoolList (eraseState out).heap (eraseState out).registers.b rows[value word].2 ∧
      out.source=suffix ∧ out.pc=66 ∧ out.stack=[] ∧
      out.heap.length=SourceRowTableProgram.cells rows+3*word.length+value word+3 ∧
      value out.next=out.heap.length ∧ (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 68 1 0 (instructions rows word) := by
  obtain ⟨final,high,num,den,src,pc,frames,len,dense,halt⟩ := run_high rows word suffix hi
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation (initial_bounded _) high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,source.trans src,?_,?_,?_,?_,stop,
    (terminal_accounting run (initial_bounded _) stop).2⟩
  · rw [erase];exact num
  · rw [erase];exact den
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).heap.length=SourceRowTableProgram.cells rows+3*word.length+value word+3 := by rw [erase];exact len
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];exact dense
    simpa [eraseState,State.map] using h

theorem total_bound (rows : List (Bits × Bits)) (word : Bits)
    (hi : value word < rows.length) :
    completeBound 68 1 0 (instructions rows word) ≤
      100000000*(SourceRowTableProgram.bits rows+rows.length+word.length+1)^3 := by
  let z := SourceRowTableProgram.bits rows+rows.length+word.length+1
  have hz : 1 ≤ z := by dsimp [z];omega
  have ht : instructions rows word ≤ 40*z := instructions_bound rows word hi
  have hs : 2*instructions rows word+2 ≤ 82*z := by omega
  have hr : instructions rows word+2 ≤ 42*z := by omega
  unfold completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 212*(40*z)*(82*z)^2+212*(42*z)*(42*z) := by gcongr <;> omega
    _ ≤ 100000000*z^3 := by
      have hz2 : z^2 ≤ z^3 := by nlinarith
      nlinarith

/-- Alignment with the actual stored fractional row. This paid source-to-read
execution returns precisely its padded numerator and denominator fields; it
makes no substitution for the graph oracle's abstract fixed read charge. -/
theorem read_stored_row {n : ℕ} (w : BinaryFractionalRows.Row n) (i : Fin n)
    (word suffix : Bits) (hvalue : value word=i.val) :
    ∃ charge out, Run program (instructions (RowInputBudgets.fields w) word) charge
        (initial (SourceRowTableProgram.encode (RowInputBudgets.fields w)++
          SelfDelimitedWordProgram.encode word++suffix))
        ((SourceRowTableProgram.encode (RowInputBudgets.fields w)++
          SelfDelimitedWordProgram.encode word).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a (BinaryFractionalRows.get w i).num ∧
      BoolList (eraseState out).heap (eraseState out).registers.b (BinaryFractionalRows.get w i).den ∧
      out.source=suffix ∧ (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤
        100000000*(SourceRowTableProgram.bits (RowInputBudgets.fields w)+n+word.length+1)^3 := by
  have hi : value word < (RowInputBudgets.fields w).length := by
    rw [hvalue,RowInputBudgets.fields_length]
    exact i.isLt
  have he : (RowInputBudgets.fields w)[value word]=
      ((BinaryFractionalRows.get w i).num,(BinaryFractionalRows.get w i).den) := by
    simp only [hvalue]
    exact FractionalHeapRead.fields_get w i (by rw [RowInputBudgets.fields_length];exact i.isLt)
  obtain ⟨charge,out,run,num,den,src,_,_,_,_,halt,cost⟩ :=
    read_from_source (RowInputBudgets.fields w) word suffix hi
  refine ⟨charge,out,run,?_,?_,src,halt,?_⟩
  · simpa only [he] using num
  · simpa only [he] using den
  · have h := cost.trans (total_bound (RowInputBudgets.fields w) word hi)
    simpa only [RowInputBudgets.fields_length] using h

end DirectedFlowCutGap.SourceRowReadProgram
