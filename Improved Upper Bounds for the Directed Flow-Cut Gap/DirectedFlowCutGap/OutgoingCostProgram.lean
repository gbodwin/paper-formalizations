import DirectedFlowCutGap.IndexedRationalRead
import DirectedFlowCutGap.BinaryComparisonProgram

/-! Actual outgoing vertex-cost access. Both directions of padded binary
comparison are executed to identify the original source. The source branch
constructs zero; the other branch reads the stored row and constructs its record. -/
namespace DirectedFlowCutGap.OutgoingCostProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def cmpLabel (pc : Fin 48) : Fin 111 := ⟨pc.val,by omega⟩
def readLabel (pc : Fin 30) : Fin 111 := ⟨pc.val+48,by omega⟩
def program : Program 111 := fun pc =>
  if pc.val=46 ∨ pc.val=77 then .ret .r3
  else if h : pc.val<48 then
    ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<78 then
    ReferenceProgramLabels.instruction readLabel (IndexedRationalRead.program ⟨pc.val-48,by omega⟩)
  else match pc.val with
  | 78 => .move .r3 .r0 79
  | 79 => .move .r0 .r1 80
  | 80 => .move .r1 .r3 81
  | 81 => .call 30 82 .r3
  | 82 => .ret .r3
  | 90 => .field .r2 .r1 false 91
  | 91 => .field .r1 .r1 true 92
  | 92 => .call 30 93 .r3
  | 93 => .make .r2 (.pair .r3 .r2) 94
  | 94 => .call 78 95 .r3
  | 95 => .branch .r3 110 99 96 110
  | 96 => .field .r3 .r2 false 97
  | 97 => .branch .r3 110 99 104 110
  | 99 => .field .r1 .r2 true 100
  | 100 => .call 76 101 .r3
  | 101 => .ret .r3
  | 104 => .make .r3 .nil 105
  | 105 => .make .r0 (.flag true) 106
  | 106 => .make .r0 (.pair .r0 .r3) 107
  | 107 => .make .r3 (.pair .r3 .r0) 108
  | 108 => .ret .r3
  | 109 => .call 90 110 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 111)) (source : Bits) (pc : Fin 111) : NaturalState 111 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def Context (heap : NaturalHeap) (p : ℕ) (rows : List Fraction) (sourceWord : Bits) : Prop :=
  ∃ table word,heap[p]?=some (.pair table word) ∧
    WordPairTableRead.Table heap table (IndexedRationalRead.fields rows) ∧ BoolList heap word sourceWord

def same (index sourceWord : Bits) : Bool :=
  (lessEqual index sourceWord).1 && (lessEqual sourceWord index).1

def result (rows : List Fraction) (sourceWord index : Bits) : Fraction :=
  if same index sourceWord then zero else IndexedRationalRead.lookup rows index

theorem same_spec (index sourceWord : Bits) : same index sourceWord=true ↔ value index=value sourceWord := by
  simp only [same,Bool.and_eq_true,(lessEqual_spec _ _).1]
  exact ⟨fun h => Nat.le_antisymm h.1 h.2,fun h => ⟨h.le,h.ge⟩⟩

theorem cmp_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (cmpLabel pc)=ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=46
  · have he : pc=46 := Fin.ext hp
    subst pc;simp [BinaryComparisonProgram.program] at h
  · simp [program,cmpLabel,pc.isLt,hp,show ¬pc.val=77 by omega]

theorem read_slots (pc : Fin 30) (h : IndexedRationalRead.program pc≠.halt) :
    program (readLabel pc)=ReferenceProgramLabels.instruction readLabel (IndexedRationalRead.program pc) := by
  by_cases hp : pc.val=29
  · have he : pc=29 := Fin.ext hp
    subst pc;simp [IndexedRationalRead.program] at h
  · simp [program,readLabel,show ¬pc.val+48=46 by omega,show ¬pc.val+48=77 by omega,
      show ¬pc.val+48<48 by omega,show pc.val+48<78 by omega]

theorem run_append {s u v : NaturalState 111} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The comparison body is callable with the same input heap and arbitrary
saved caller. The true/false result is the root actually returned by its code. -/
theorem compare_return {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 111)
    (stack : List (Frame ℕ 111)) (source : Bits) :
    ∃ ext root, ext.length=BinaryComparisonProgram.cells xs ys+1 ∧
      NaturalRun program (BinaryComparisonProgram.steps xs ys+4)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 30) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (lessEqual xs ys).1) := by
  obtain ⟨out,run,flag,_,_,ha,hb,hc,frames,src,hpc,dense,ext,halt⟩ :=
    BinaryComparisonProgram.compare_high (BinaryComparisonProgram.state heap next a b c d [] source 30)
      rfl hn left right rfl
  obtain ⟨ext,he,le⟩ := ext
  have lifted := ReferenceProgramLabels.run cmpLabel BinaryComparisonProgram.program program cmp_slots run
  have lifted := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lifted
  have shape : out=BinaryComparisonProgram.state (heap++ext) (next+ext.length)
      a b c out.registers.d [] source 46 := by
    cases out with
    | mk oh on regs frames pc src =>
      cases regs
      simp_all [BinaryComparisonProgram.state]
  have body : NaturalRun program (BinaryComparisonProgram.steps xs ys+3)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 30) []
      (state (heap++ext) (next+ext.length) a b c out.registers.d (⟨pc,.r3,saved⟩::stack) source 46) := by
    rw [shape] at lifted
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryComparisonProgram.state,cmpLabel,state] using lifted
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c out.registers.d (⟨pc,.r3,saved⟩::stack) source 46)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c out.registers.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,out.registers.d,le,?_,?_⟩
  · simpa [Nat.add_assoc] using run_append body (.step ret (.done _))
  · simpa only [he,BinaryComparisonProgram.state] using flag

/-- This real subroutine swaps the two argument registers before comparison,
then the actual saved frame restores the original caller. -/
theorem reverse_return {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 111)
    (stack : List (Frame ℕ 111)) (source : Bits) :
    ∃ ext root,ext.length=BinaryComparisonProgram.cells ys xs+1 ∧
      NaturalRun program (BinaryComparisonProgram.steps ys xs+9)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 78) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (lessEqual ys xs).1) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  obtain ⟨ext,root,len,body,flag⟩ := compare_return right left next c a hn ⟨b,a,c,a⟩ 82 frames source
  have t78 : tickNatural program (state heap next a b c d frames source 78)=
      some ⟨state heap next a b c a frames source 79,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t79 : tickNatural program (state heap next a b c a frames source 79)=
      some ⟨state heap next b b c a frames source 80,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t80 : tickNatural program (state heap next b b c a frames source 80)=
      some ⟨state heap next b a c a frames source 81,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t81 : tickNatural program (state heap next b a c a frames source 81)=
      some ⟨state heap next b a c a (⟨82,.r3,⟨b,a,c,a⟩⟩::frames) source 30,[],0⟩ := by
    simp [tickNatural,program,state]
  have ret : tickNatural program (state (heap++ext) (next+ext.length) b a c root frames source 82)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  have pre : NaturalRun program 4 (state heap next a b c d frames source 78) []
      (state heap next b a c a (⟨82,.r3,⟨b,a,c,a⟩⟩::frames) source 30) :=
    .step t78 (.step t79 (.step t80 (.step t81 (.done _))))
  exact ⟨ext,root,len,by
    convert run_append pre (run_append body (.step ret (.done _))) using 1 <;>
      simp [Nat.add_comm,Nat.add_left_comm]; omega,flag⟩

/-- The indexed reader's real final halt is replaced by a paid return. -/
theorem indexed_return {word : Bits} {rows : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (input : BoolList heap a word) (table : WordPairTableRead.Table heap b (IndexedRationalRead.fields rows))
    (hi : value word<rows.length) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 111) (stack : List (Frame ℕ 111)) (source : Bits) :
    ∃ ext root,ext.length=value word+2 ∧
      NaturalRun program (BinaryIndexedPairRead.steps word+4)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 76) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (IndexedRationalRead.lookup rows word) := by
  obtain ⟨ext,root,len,core,rep⟩ := IndexedRationalRead.read_high
    (IndexedRationalRead.state heap next a b c d [] source 28) rfl hn rfl input table hi
  have lift := ReferenceProgramLabels.run readLabel IndexedRationalRead.program program read_slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (BinaryIndexedPairRead.steps word+3)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 76) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 77) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      IndexedRationalRead.state,readLabel,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 77)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

/-- The source branch builds the literal padded rational zero. -/
theorem zero_return (heap : NaturalHeap) (next a b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 111) (stack : List (Frame ℕ 111)) (source : Bits) :
    ∃ ext root,ext.length=4 ∧ NaturalRun program 5
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 104) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root zero := by
  let ext : NaturalHeap := [.nil,.flag true,.pair (next+1) next,.pair next (next+2)]
  let frames := (⟨pc,.r3,saved⟩::stack)
  have t104 : tickNatural program (state heap next a b c d frames source 104)=
      some ⟨state (heap++[.nil]) (next+1) a b c next frames source 105,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
  have t105 : tickNatural program (state (heap++[.nil]) (next+1) a b c next frames source 105)=
      some ⟨state (heap++[.nil,.flag true]) (next+2) (next+1) b c next frames source 106,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,List.append_assoc]
  have t106 : tickNatural program (state (heap++[.nil,.flag true]) (next+2) (next+1) b c next frames source 106)=
      some ⟨state (heap++[.nil,.flag true,.pair (next+1) next]) (next+3) (next+2) b c next frames source 107,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,List.append_assoc]
  have t107 : tickNatural program (state (heap++[.nil,.flag true,.pair (next+1) next]) (next+3) (next+2) b c next frames source 107)=
      some ⟨state (heap++ext) (next+4) (next+2) b c (next+3) frames source 108,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,List.append_assoc,ext]
  have t108 : tickNatural program (state (heap++ext) (next+4) (next+2) b c (next+3) frames source 108)=
      some ⟨state (heap++ext) (next+4) saved.a saved.b saved.c (next+3) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.set,Registers.get,frames]
  refine ⟨ext,next+3,rfl,?_,?_⟩
  · exact .step t104 (.step t105 (.step t106 (.step t107 (.step t108 (.done _)))))
  · refine ⟨next,next+2,?_,.nil ?_,.cons (head:=next+1) (tail:=next) ?_ ?_ (.nil ?_)⟩ <;>
      simp [ext,hn]
def finishSteps (forward backward : Bool) (word : Bits) : ℕ :=
  (if backward then 3 else 1)+(if forward && backward then 5 else BinaryIndexedPairRead.steps word+7)
def finishCells (forward backward : Bool) (word : Bits) : ℕ :=
  if forward && backward then 4 else value word+2

theorem decision_run (heap : NaturalHeap) (next a b p rf rg table : ℕ)
    (f g : Bool) (hp : heap[p]?=some (.pair rf table))
    (hf : heap[rf]?=some (.flag f)) (hg : heap[rg]?=some (.flag g))
    (stack : List (Frame ℕ 111)) (source : Bits) :
    NaturalRun program (if g then 3 else 1) (state heap next a b p rg stack source 95) []
      (state heap next a b p (if g then rf else rg) stack source (if f && g then 104 else 99)) := by
  have t95 : tickNatural program (state heap next a b p rg stack source 95)=
      some ⟨state heap next a b p rg stack source (if g then 96 else 99),[],0⟩ := by
    cases g <;> simp [tickNatural,program,state,Registers.get,hg,tagBranch]
  have t96 : tickNatural program (state heap next a b p rg stack source 96)=
      some ⟨state heap next a b p rf stack source 97,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp]
  have t97 : tickNatural program (state heap next a b p rf stack source 97)=
      some ⟨state heap next a b p rf stack source (if f then 104 else 99),[],0⟩ := by
    cases f <;> simp [tickNatural,program,state,Registers.get,hf,tagBranch]
  cases g
  · simpa using NaturalRun.step t95 (.done _)
  · simpa using NaturalRun.step t95 (.step t96 (.step t97 (.done _)))

theorem read_tail {word : Bits} {rows : List Fraction} {heap : NaturalHeap} {a p table : ℕ}
    (input : BoolList heap a word) (ht : WordPairTableRead.Table heap table (IndexedRationalRead.fields rows))
    (rf : ℕ) (hp : heap[p]?=some (.pair rf table)) (hi : value word<rows.length)
    (next b d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 111) (stack : List (Frame ℕ 111)) (source : Bits) :
    ∃ ext root,ext.length=value word+2 ∧
      NaturalRun program (BinaryIndexedPairRead.steps word+7)
        (state heap next a b p d (⟨pc,.r3,saved⟩::stack) source 99) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (IndexedRationalRead.lookup rows word) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  obtain ⟨ext,root,len,body,rep⟩ := indexed_return input ht hi next p d hn ⟨a,table,p,d⟩ 101 frames source
  have t99 : tickNatural program (state heap next a b p d frames source 99)=
      some ⟨state heap next a table p d frames source 100,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp]
  have t100 : tickNatural program (state heap next a table p d frames source 100)=
      some ⟨state heap next a table p d (⟨101,.r3,⟨a,table,p,d⟩⟩::frames) source 76,[],0⟩ := by
    simp [tickNatural,program,state]
  have ret : tickNatural program (state (heap++ext) (next+ext.length) a table p root frames source 101)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  have pre : NaturalRun program 2 (state heap next a b p d frames source 99) []
      (state heap next a table p d (⟨101,.r3,⟨a,table,p,d⟩⟩::frames) source 76) :=
    .step t99 (.step t100 (.done _))
  exact ⟨ext,root,len,by
    convert run_append pre (run_append body (.step ret (.done _))) using 1 <;>
      simp [Nat.add_comm,Nat.add_left_comm]; omega,rep⟩

theorem finish_return {word : Bits} {rows : List Fraction} {heap : NaturalHeap} {a p table : ℕ}
    (input : BoolList heap a word) (ht : WordPairTableRead.Table heap table (IndexedRationalRead.fields rows))
    (rf rg : ℕ) (f g : Bool) (hp : heap[p]?=some (.pair rf table))
    (hf : heap[rf]?=some (.flag f)) (hg : heap[rg]?=some (.flag g)) (hi : value word<rows.length)
    (next b : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 111) (stack : List (Frame ℕ 111)) (source : Bits) :
    ∃ ext root,ext.length=finishCells f g word ∧
      NaturalRun program (finishSteps f g word)
        (state heap next a b p rg (⟨pc,.r3,saved⟩::stack) source 95) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (if f && g then zero else IndexedRationalRead.lookup rows word) := by
  have decision := decision_run heap next a b p rf rg table f g hp hf hg (⟨pc,.r3,saved⟩::stack) source
  cases h : f && g
  · obtain ⟨ext,root,len,tail,rep⟩ := read_tail input ht rf hp hi next b (if g then rf else rg) hn saved pc stack source
    simp only [h,Bool.false_eq_true,↓reduceIte] at decision
    exact ⟨ext,root,by simpa [finishCells,h] using len,
      by simpa [finishSteps,h] using run_append decision tail,by simpa [h] using rep⟩
  · obtain ⟨ext,root,len,tail,rep⟩ := zero_return heap next a b p (if g then rf else rg) hn saved pc stack source
    simp only [h,↓reduceIte] at decision
    exact ⟨ext,root,by simpa [finishCells,h] using len,
      by simpa [finishSteps,h] using run_append decision tail,by simpa [h] using rep⟩
def instructions (sourceWord index : Bits) : ℕ :=
  BinaryComparisonProgram.steps index sourceWord+BinaryComparisonProgram.steps sourceWord index+18+
    finishSteps (lessEqual index sourceWord).1 (lessEqual sourceWord index).1 index

def cells (sourceWord index : Bits) : ℕ :=
  BinaryComparisonProgram.cells index sourceWord+BinaryComparisonProgram.cells sourceWord index+3+
    finishCells (lessEqual index sourceWord).1 (lessEqual sourceWord index).1 index

/-- Source identity is tested by the actual two comparisons before any row
read. Both branches return the exact outgoing rational record. -/
theorem outgoing_return {word sourceWord : Bits} {rows : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (input : BoolList heap a word) (context : Context heap b rows sourceWord)
    (hi : value word<rows.length) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 111) (stack : List (Frame ℕ 111)) (source : Bits) :
    ∃ ext root,ext.length=cells sourceWord word ∧
      NaturalRun program (instructions sourceWord word)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 90) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (result rows sourceWord word) := by
  obtain ⟨table,sw,hctx,tableRep,swRep⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  obtain ⟨ef,rf,lf,forward,hf⟩ := compare_return input swRep next table d hn ⟨a,sw,table,d⟩ 93 frames source
  let h1 := heap++ef
  let n1 := next+ef.length
  let pair : NaturalHeap := [.pair rf table]
  let h2 := h1++pair
  let n2 := n1+1
  have dense1 : n1=h1.length := by simp [n1,h1,hn]
  have dense2 : n2=h2.length := by simp [n2,h2,pair,dense1]
  obtain ⟨eg,rg,lg,backward,hg⟩ := reverse_return
    (boolList_extend (boolList_extend input ef) pair)
    (boolList_extend (boolList_extend swRep ef) pair)
    n2 n1 rf dense2 ⟨a,sw,n1,rf⟩ 95 frames source
  let h3 := h2++eg
  let n3 := n2+eg.length
  have dense3 : n3=h3.length := by simp [n3,h3,dense2]
  have pair3 : h3[n1]?=some (.pair rf table) := lookup_extend (by simp [h2,pair,dense1]) eg
  have flag3 : h3[rf]?=some (.flag (lessEqual word sourceWord).1) :=
    lookup_extend (lookup_extend hf pair) eg
  have input3 : BoolList h3 a word := boolList_extend (boolList_extend (boolList_extend input ef) pair) eg
  have table3 : WordPairTableRead.Table h3 table (IndexedRationalRead.fields rows) :=
    BinaryIndexedPairRead.table_extend (BinaryIndexedPairRead.table_extend
      (BinaryIndexedPairRead.table_extend tableRep ef) pair) eg
  obtain ⟨et,root,lt,tail,rep⟩ := finish_return input3 table3 rf rg
    (lessEqual word sourceWord).1 (lessEqual sourceWord word).1 pair3 flag3 hg hi n3 sw dense3 saved pc stack source
  have t90 : tickNatural program (state heap next a b c d frames source 90)=
      some ⟨state heap next a b table d frames source 91,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hctx]
  have t91 : tickNatural program (state heap next a b table d frames source 91)=
      some ⟨state heap next a sw table d frames source 92,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hctx]
  have t92 : tickNatural program (state heap next a sw table d frames source 92)=
      some ⟨state heap next a sw table d (⟨93,.r3,⟨a,sw,table,d⟩⟩::frames) source 30,[],0⟩ := by
    simp [tickNatural,program,state]
  have t93 : tickNatural program (state h1 n1 a sw table rf frames source 93)=
      some ⟨state h2 n2 a sw n1 rf frames source 94,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,n2,pair]
  have t94 : tickNatural program (state h2 n2 a sw n1 rf frames source 94)=
      some ⟨state h2 n2 a sw n1 rf (⟨95,.r3,⟨a,sw,n1,rf⟩⟩::frames) source 78,[],0⟩ := by
    simp [tickNatural,program,state]
  have pre : NaturalRun program 3 (state heap next a b c d frames source 90) []
      (state heap next a sw table d (⟨93,.r3,⟨a,sw,table,d⟩⟩::frames) source 30) :=
    .step t90 (.step t91 (.step t92 (.done _)))
  have middle : NaturalRun program 2 (state h1 n1 a sw table rf frames source 93) []
      (state h2 n2 a sw n1 rf (⟨95,.r3,⟨a,sw,n1,rf⟩⟩::frames) source 78) :=
    .step t93 (.step t94 (.done _))
  refine ⟨ef++pair++eg++et,root,?_,?_,?_⟩
  · simp [cells,pair,lf,lg,lt];omega
  · have all := run_append pre (run_append forward (run_append middle (run_append backward tail)))
    convert all using 1 <;> simp [instructions,h3,h2,h1,n3,n2,n1,pair,List.append_assoc,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]; omega
  · simpa [result,same,h3,h2,h1,List.append_assoc] using rep

/-- This is an output-sensitive bound; binary indices may be padded and the
literal table scan pays for their actual numeric value. -/
theorem instructions_bound (sourceWord index : Bits) :
    instructions sourceWord index ≤ 100*(sourceWord.length+index.length+value index+1) := by
  have hf := BinaryComparisonProgram.steps_bound index sourceWord
  have hg := BinaryComparisonProgram.steps_bound sourceWord index
  have hr := BinaryIndexedPairRead.steps_bound index
  have hd : (if (lessEqual sourceWord index).1 then 3 else 1) ≤ 3 := by split <;> omega
  have ht : (if (lessEqual index sourceWord).1 && (lessEqual sourceWord index).1 then 5
      else BinaryIndexedPairRead.steps index+7) ≤ BinaryIndexedPairRead.steps index+7 := by split <;> omega
  dsimp [instructions,finishSteps]
  omega
theorem outgoing_high {word sourceWord : Bits} {rows : List Fraction} (initial : NaturalState 111)
    (pc0 : initial.pc=109) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : BoolList initial.heap initial.registers.a word)
    (context : Context initial.heap initial.registers.b rows sourceWord) (hi : value word<rows.length) :
    ∃ ext root,ext.length=cells sourceWord word ∧
      NaturalRun program (instructions sourceWord word+1) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          initial.registers.b initial.registers.c root [] initial.source 110) ∧
      Stored (initial.heap++ext) root (result rows sourceWord word) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input context
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 109)=
          some ⟨state heap next a b c d [⟨110,.r3,⟨a,b,c,d⟩⟩] source 90,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := outgoing_return input context hi next c d hn ⟨a,b,c,d⟩ 110 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_assoc,state] using NaturalRun.step first run,rep⟩

/-- One lower-interpreter run performs source testing and the selected branch,
with one paid terminal halt and the original reader suffix unchanged. -/
theorem outgoing_bit {word sourceWord : Bits} {rows : List Fraction} {H B : ℕ} (initial : BitState 111)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=109)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : BoolList (eraseState initial).heap (eraseState initial).registers.a word)
    (context : Context (eraseState initial).heap (eraseState initial).registers.b rows sourceWord)
    (hi : value word<rows.length) :
    ∃ charge out,Run program (instructions sourceWord word+1) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (result rows sourceWord word) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=110 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells sourceWord word) ∧
      out.Bounded (H+instructions sourceWord word+1) (B+instructions sourceWord word+1) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 111 H B (instructions sourceWord word+1) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := outgoing_high (eraseState initial) pc0 hn' empty' input context hi
  obtain ⟨charge,out,run,erase,bound,_,src⟩ := polynomial_simulation bounded high
  have halt : tickNatural program
      (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
        (eraseState initial).registers.a (eraseState initial).registers.b
        (eraseState initial).registers.c root [] (eraseState initial).source 110)=none := by
    simp [tickNatural,program,state]
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some x => simp [ht] at obs
  refine ⟨charge,out,run,?_,by simpa [state,eraseState,State.map] using src,?_,?_,⟨ext,?_,len⟩,?_,stop,?_⟩
  · simpa [erase,state] using rep
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=110 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · simpa [Nat.add_assoc] using bound
  · exact (terminal_accounting run bounded stop).2

end DirectedFlowCutGap.OutgoingCostProgram
