import DirectedFlowCutGap.BinaryIndexedPairRead
import DirectedFlowCutGap.RationalComparisonProgram

/-! A real binary-indexed table lookup returns a newly allocated rational
record sharing the selected original padded fields. The table and binary
index are represented inputs; the result is constructed by the machine. -/
namespace DirectedFlowCutGap.IndexedRationalRead
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def fields (rows : List Fraction) : List (Bits×Bits) := rows.map fun x => (x.num,x.den)
def lookup (rows : List Fraction) (word : Bits) : Fraction := (rows[value word]?).getD zero

theorem lookup_fields (rows : List Fraction) (word : Bits) (hi : value word<rows.length) :
    (fields rows)[value word]'(by simpa [fields] using hi)=((lookup rows word).num,(lookup rows word).den) := by
  simp [fields,lookup,List.getElem?_eq_getElem hi]

def label (pc : Fin 26) : Fin 30 := ⟨pc.val,by omega⟩
def program : Program 30 := fun pc =>
  if pc.val=24 then .make .r3 (.pair .r0 .r1) 26
  else if h : pc.val<26 then
    ReferenceProgramLabels.instruction label (BinaryIndexedPairRead.program ⟨pc.val,h⟩)
  else if pc.val=26 then .ret .r3
  else if pc.val=28 then .call 25 29 .r3 else .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 30)) (source : Bits) (pc : Fin 30) : NaturalState 30 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem slots (pc : Fin 26) (h : BinaryIndexedPairRead.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (BinaryIndexedPairRead.program pc) := by
  by_cases hp : pc.val=24
  · have he : pc=24 := Fin.ext hp
    subst pc;simp [BinaryIndexedPairRead.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append {s u v : NaturalState 30} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The actual old reader halt becomes a paid record allocation and return. -/
theorem read_return {word : Bits} {rows : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (input : BoolList heap a word) (table : WordPairTableRead.Table heap b (fields rows))
    (hi : value word<rows.length) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 30) (stack : List (Frame ℕ 30)) (source : Bits) :
    ∃ ext root,ext.length=value word+2 ∧
      NaturalRun program (BinaryIndexedPairRead.steps word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 25) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (lookup rows word) := by
  obtain ⟨out,core,ra,rb,⟨ext,he,len⟩,dense,hs,src,hpc,_⟩ :=
    BinaryIndexedPairRead.read input table (by simpa [fields] using hi) next c d hn source
  have shape : out=BinaryIndexedPairRead.state (heap++ext) (next+ext.length)
      out.registers.a out.registers.b out.registers.c out.registers.d source 24 := by
    cases out with
    | mk oh on regs frames pc src =>
      cases regs
      simp_all [BinaryIndexedPairRead.state]
  have lift := ReferenceProgramLabels.run label BinaryIndexedPairRead.program program slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (BinaryIndexedPairRead.steps word)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 25) []
      (state (heap++ext) (next+ext.length) out.registers.a out.registers.b
        out.registers.c out.registers.d (⟨pc,.r3,saved⟩::stack) source 24) := by
    rw [shape] at lift
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryIndexedPairRead.state,label,state] using lift
  have make : tickNatural program
      (state (heap++ext) (next+ext.length) out.registers.a out.registers.b
        out.registers.c out.registers.d (⟨pc,.r3,saved⟩::stack) source 24)=
      some ⟨state ((heap++ext)++[.pair out.registers.a out.registers.b]) (next+ext.length+1)
        out.registers.a out.registers.b out.registers.c (next+ext.length)
        (⟨pc,.r3,saved⟩::stack) source 26,[],0⟩ := by
    simp [tickNatural,program,state,Recipe.cell,allocateNatural,Registers.get,Registers.set]
  have ret : tickNatural program
      (state ((heap++ext)++[.pair out.registers.a out.registers.b]) (next+ext.length+1)
        out.registers.a out.registers.b out.registers.c (next+ext.length)
        (⟨pc,.r3,saved⟩::stack) source 26)=
      some ⟨state ((heap++ext)++[.pair out.registers.a out.registers.b]) (next+ext.length+1)
        saved.a saved.b saved.c (next+ext.length) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext++[.pair out.registers.a out.registers.b],next+ext.length,by simp [len],?_,?_⟩
  · simpa [List.append_assoc,Nat.add_assoc] using run_append body (.step make (.step ret (.done _)))
  · rw [lookup_fields rows word hi] at ra rb
    have nr := boolList_extend ra [.pair out.registers.a out.registers.b]
    have dr := boolList_extend rb [.pair out.registers.a out.registers.b]
    rw [he] at nr dr
    refine ⟨out.registers.a,out.registers.b,?_,?_,?_⟩
    · simp [← List.append_assoc,hn]
    · simpa [List.append_assoc] using nr
    · simpa [List.append_assoc] using dr

/-- The actual top-level call preserves all three input registers. -/
theorem read_high {word : Bits} {rows : List Fraction} (initial : NaturalState 30)
    (pc0 : initial.pc=28) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : BoolList initial.heap initial.registers.a word)
    (table : WordPairTableRead.Table initial.heap initial.registers.b (fields rows))
    (hi : value word<rows.length) :
    ∃ ext root,ext.length=value word+2 ∧
      NaturalRun program (BinaryIndexedPairRead.steps word+3) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          initial.registers.b initial.registers.c root [] initial.source 29) ∧
      Stored (initial.heap++ext) root (lookup rows word) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input table
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 28)=
          some ⟨state heap next a b c d [⟨29,.r3,⟨a,b,c,d⟩⟩] source 25,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := read_return input table hi next c d hn ⟨a,b,c,d⟩ 29 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_assoc,state] using NaturalRun.step first run,rep⟩

end DirectedFlowCutGap.IndexedRationalRead
