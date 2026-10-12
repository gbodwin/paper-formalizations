import DirectedFlowCutGap.BinaryPointerListRead

/-! Both coordinates of a genuine stored Boolean adjacency matrix are read
by actual binary-index conversion and pointer traversal, retaining the same
input heap and source. No adjacency callback chooses the branch. -/
namespace DirectedFlowCutGap.GraphAdjacencyProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryPointerListRead

def Matrix (heap : NaturalHeap) (p : ℕ) (rows : List Bits) : Prop :=
  ∃ roots,∃ hl : roots.length=rows.length,PointerList heap p roots ∧
    ∀ i (hi : i<rows.length),BoolList heap roots[i] rows[i]

def Context (heap : NaturalHeap) (p : ℕ) (rows : List Bits) (column : Bits) : Prop :=
  ∃ matrix word,heap[p]?=some (.pair matrix word) ∧ Matrix heap matrix rows ∧
    BoolList heap word column

theorem matrix_extend {heap : NaturalHeap} {p : ℕ} {rows : List Bits}
    (h : Matrix heap p rows) (extra : NaturalHeap) : Matrix (heap++extra) p rows := by
  obtain ⟨roots,hl,hp,hr⟩ := h
  exact ⟨roots,hl,pointerList_extend hp extra,fun i hi => boolList_extend (hr i hi) extra⟩

theorem context_extend {heap : NaturalHeap} {p : ℕ} {rows : List Bits} {column : Bits}
    (h : Context heap p rows column) (extra : NaturalHeap) : Context (heap++extra) p rows column := by
  obtain ⟨m,w,hp,hm,hw⟩ := h
  exact ⟨m,w,lookup_extend hp extra,matrix_extend hm extra,boolList_extend hw extra⟩

theorem boolList_pointers {heap : NaturalHeap} {p : ℕ} {bs : Bits} (h : BoolList heap p bs) :
    ∃ roots,∃ hl : roots.length=bs.length,PointerList heap p roots ∧
      ∀ i (hi : i<bs.length),heap[roots[i]]?=some (.flag bs[i]) := by
  induction h with
  | nil h => exact ⟨[],rfl,.nil h,by simp⟩
  | @cons root head tail b bs hp hb ht ih =>
    obtain ⟨roots,hl,hr,hf⟩ := ih
    refine ⟨head::roots,by simpa using hl,.cons hp hr,?_⟩
    intro i hi
    cases i with
    | zero => exact hb
    | succ i => simpa using hf i (by simpa using hi)

def label (pc : Fin 27) : Fin 36 := ⟨pc.val,by omega⟩
def program : Program 36 := fun pc =>
  if pc.val=26 then .ret .r3
  else if h : pc.val<27 then
    ReferenceProgramLabels.instruction label (BinaryPointerListRead.program ⟨pc.val,h⟩)
  else match pc.val with
  | 27 => .move .r2 .r1 28
  | 28 => .field .r1 .r1 false 29
  | 29 => .call 25 30 .r3
  | 30 => .field .r0 .r2 true 31
  | 31 => .move .r1 .r3 32
  | 32 => .call 25 33 .r3
  | 33 => .ret .r3
  | 34 => .call 27 35 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 36)) (source : Bits) (pc : Fin 36) : NaturalState 36 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩
def steps (row column : Bits) : ℕ := BinaryPointerListRead.steps row+BinaryPointerListRead.steps column+11

theorem slots (pc : Fin 27) (h : BinaryPointerListRead.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (BinaryPointerListRead.program pc) := by
  by_cases hp : pc.val=26
  · have he : pc=26 := Fin.ext hp
    subst pc;simp [BinaryPointerListRead.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append {s u v : NaturalState 36} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem pointer_return {heap : NaturalHeap} {a b : ℕ} {word : Bits} {xs : List ℕ}
    (input : BoolList heap a word) (table : PointerList heap b xs) (hi : value word<xs.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 36) (stack : List (Frame ℕ 36)) (source : Bits) :
    ∃ ext,ext.length=value word+1 ∧
      NaturalRun program (BinaryPointerListRead.steps word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 25) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c xs[value word] stack source pc) := by
  obtain ⟨ext,len,core⟩ := BinaryPointerListRead.read_return input table hi next c d hn ⟨a,b,c,d⟩ 26 [] source
  have call : tickNatural BinaryPointerListRead.program
      (BinaryPointerListRead.state heap next a b c d [] source 25)=
      some ⟨BinaryPointerListRead.state heap next a b c d [⟨26,.r3,⟨a,b,c,d⟩⟩] source 24,[],0⟩ := by
    simp [tickNatural,BinaryPointerListRead.program,BinaryPointerListRead.state]
  have lift := ReferenceProgramLabels.run label BinaryPointerListRead.program program slots (.step call core)
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (BinaryPointerListRead.steps word+1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 25) []
      (state (heap++ext) (next+ext.length) a b c xs[value word] (⟨pc,.r3,saved⟩::stack) source 26) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryPointerListRead.state,label,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c xs[value word] (⟨pc,.r3,saved⟩::stack) source 26)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c xs[value word] stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,len,run_append body (.step ret (.done _))⟩

theorem read_return {heap : NaturalHeap} {a b : ℕ} {row column : Bits} {rows : List Bits}
    (input : BoolList heap a row) (context : Context heap b rows column)
    (hi : value row<rows.length) (hj : value column<(rows[value row]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 36) (stack : List (Frame ℕ 36)) (source : Bits) :
    ∃ ext root,ext.length=value row+value column+2 ∧
      NaturalRun program (steps row column)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 27) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (rows[value row])[value column]) := by
  obtain ⟨matrix,word,hctx,hm,hcw⟩ := context
  obtain ⟨roots,hl,table,words⟩ := hm
  have hri : value row<roots.length := by omega
  let frame : Frame ℕ 36 := ⟨pc,.r3,saved⟩
  obtain ⟨e1,len1,run1⟩ := pointer_return input table hri next b d hn ⟨a,matrix,b,d⟩ 30 (frame::stack) source
  have hr := boolList_extend (words (value row) hi) e1
  obtain ⟨flags,fl,flagTable,flagRep⟩ := boolList_pointers hr
  have hci : value column<flags.length := by omega
  obtain ⟨e2,len2,run2⟩ := pointer_return (boolList_extend hcw e1) flagTable hci
    (next+e1.length) b roots[value row] (by simp [hn]) ⟨word,roots[value row],b,roots[value row]⟩ 33
    (frame::stack) source
  have t27 : tickNatural program (state heap next a b c d (frame::stack) source 27)=
      some ⟨state heap next a b b d (frame::stack) source 28,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t28 : tickNatural program (state heap next a b b d (frame::stack) source 28)=
      some ⟨state heap next a matrix b d (frame::stack) source 29,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hctx]
  have t29 : tickNatural program (state heap next a matrix b d (frame::stack) source 29)=
      some ⟨state heap next a matrix b d (⟨30,.r3,⟨a,matrix,b,d⟩⟩::frame::stack) source 25,[],0⟩ := by
    simp [tickNatural,program,state]
  have t30 : tickNatural program
      (state (heap++e1) (next+e1.length) a matrix b roots[value row] (frame::stack) source 30)=
      some ⟨state (heap++e1) (next+e1.length) word matrix b roots[value row] (frame::stack) source 31,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hctx e1]
  have t31 : tickNatural program
      (state (heap++e1) (next+e1.length) word matrix b roots[value row] (frame::stack) source 31)=
      some ⟨state (heap++e1) (next+e1.length) word roots[value row] b roots[value row] (frame::stack) source 32,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t32 : tickNatural program
      (state (heap++e1) (next+e1.length) word roots[value row] b roots[value row] (frame::stack) source 32)=
      some ⟨state (heap++e1) (next+e1.length) word roots[value row] b roots[value row]
        (⟨33,.r3,⟨word,roots[value row],b,roots[value row]⟩⟩::frame::stack) source 25,[],0⟩ := by
    simp [tickNatural,program,state]
  have t33 : tickNatural program
      (state ((heap++e1)++e2) (next+e1.length+e2.length) word roots[value row] b flags[value column]
        (frame::stack) source 33)=
      some ⟨state ((heap++e1)++e2) (next+e1.length+e2.length) saved.a saved.b saved.c flags[value column]
        stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frame,Registers.get,Registers.set]
  refine ⟨e1++e2,flags[value column],by simp [len1,len2];omega,?_,?_⟩
  · have joined := run_append (.step t27 (.step t28 (.step t29 run1)))
      (.step t30 (.step t31 (.step t32 (run_append run2 (.step t33 (.done _))))))
    convert joined using 1 <;> simp [steps,List.append_assoc,Nat.add_assoc]
    omega
  · simpa [List.append_assoc] using lookup_extend (flagRep (value column) hj) e2

end DirectedFlowCutGap.GraphAdjacencyProgram
