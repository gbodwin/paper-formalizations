import DirectedFlowCutGap.InputAdditionProgram
import DirectedFlowCutGap.BinaryIndexedPairRead

/-! A literal source-driven constructor for the stored two-word row table.
Each true row marker precedes two self-delimited padded words; a false marker
ends the table. All word and table cells arise in the actual interpreter. -/
namespace DirectedFlowCutGap.SourceRowTableProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def encode : List (Bits × Bits) → Bits
  | [] => [false]
  | (a,b)::rows => true::(SelfDelimitedWordProgram.encode a++SelfDelimitedWordProgram.encode b++encode rows)
def bits : List (Bits × Bits) → ℕ
  | [] => 0
  | (a,b)::rows => a.length+b.length+bits rows
def steps (rows : List (Bits × Bits)) : ℕ := 6*bits rows+22*rows.length+4
def cells (rows : List (Bits × Bits)) : ℕ := 3*bits rows+7*rows.length+2

def wordLabel (pc : Fin 10) : Fin 32 := ⟨pc.val+16,by omega⟩
def program : Program 32 := fun pc =>
  if pc.val=24 then .ret .r3
  else if h : 16 ≤ pc.val ∧ pc.val < 26 then
    ReferenceProgramLabels.instruction wordLabel
      (SelfDelimitedWordProgram.program ⟨pc.val-16,by omega⟩)
  else match pc.val with
  | 0 => .request .r2 1
  | 1 => .branch .r2 31 2 4 31
  | 2 => .make .r3 .nil 3
  | 3 => .ret .r3
  | 4 => .call 25 5 .r3
  | 5 => .move .r0 .r3 6
  | 6 => .call 25 7 .r3
  | 7 => .move .r1 .r3 8
  | 8 => .call 0 9 .r3
  | 9 => .make .r2 (.pair .r0 .r1) 10
  | 10 => .make .r3 (.pair .r2 .r3) 11
  | 11 => .ret .r3
  | 30 => .call 0 31 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 32)) (source : Bits) (pc : Fin 32) : NaturalState 32 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def initial (source : Bits) : BitState 32 := ⟨[],[],⟨[],[],[],[]⟩,[],30,source⟩

theorem word_slots (pc : Fin 10) (h : SelfDelimitedWordProgram.program pc ≠ .halt) :
    program (wordLabel pc)=ReferenceProgramLabels.instruction wordLabel
      (SelfDelimitedWordProgram.program pc) := by
  fin_cases pc <;> simp_all [program,wordLabel,SelfDelimitedWordProgram.program]

theorem run_append {s u v : NaturalState 32} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The actual word reader is called with the table caller below its own
saved frames; the former word halt executes a real return. -/
theorem word_return (word suffix : Bits) (heap : NaturalHeap) (next a b c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 32)
    (stack : List (Frame ℕ 32)) :
    ∃ ext root, ext.length=3*word.length+2 ∧
      NaturalRun program (6*word.length+6)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack)
          (SelfDelimitedWordProgram.encode word++suffix) 25)
        ((SelfDelimitedWordProgram.encode word).map Event.request)
        (state (heap++ext) (next+3*word.length+2)
          saved.a saved.b saved.c root stack suffix pc) ∧ BoolList (heap++ext) root word := by
  obtain ⟨ext,root,len,run,rep⟩ := InputAdditionProgram.reader_high word suffix heap next a b c d hn
  have rel := ReferenceProgramLabels.run wordLabel SelfDelimitedWordProgram.program program word_slots run
  have extra := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) rel
  have body : NaturalRun program (6*word.length+5)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack)
        (SelfDelimitedWordProgram.encode word++suffix) 25)
      ((SelfDelimitedWordProgram.encode word).map Event.request)
      (state (heap++ext) (next+3*word.length+2) a b c root
        (⟨pc,.r3,saved⟩::stack) suffix 24) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      wordLabel,SelfDelimitedWordProgram.state,state] using extra
  have ret : tickNatural program
      (state (heap++ext) (next+3*word.length+2) a b c root
        (⟨pc,.r3,saved⟩::stack) suffix 24)=
      some ⟨state (heap++ext) (next+3*word.length+2)
        saved.a saved.b saved.c root stack suffix pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  simpa [Nat.add_assoc] using run_append body (NaturalRun.step ret (.done _))

/-- A record pair and a table-spine pair are actual allocations, followed by
restoring the table caller. The old field cells and tail table are retained. -/
theorem prepend_return {heap : NaturalHeap} {x y : Bits} {rows : List (Bits × Bits)}
    (next a b c d : ℕ) (hn : next=heap.length)
    (ra : BoolList heap a x) (rb : BoolList heap b y) (tail : WordPairTableRead.Table heap d rows)
    (saved : Registers ℕ) (pc : Fin 32) (stack : List (Frame ℕ 32)) (source : Bits) :
    let ext : NaturalHeap := [.pair a b,.pair next d]
    NaturalRun program 3
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 9) []
      (state (heap++ext) (next+2) saved.a saved.b saved.c (next+1) stack source pc) ∧
    WordPairTableRead.Table (heap++ext) (next+1) ((x,y)::rows) := by
  dsimp only
  constructor
  · have t0 : tickNatural program
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 9)=
        some ⟨state (heap++[.pair a b]) (next+1) a b next d
          (⟨pc,.r3,saved⟩::stack) source 10,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
    have t1 : tickNatural program
        (state (heap++[.pair a b]) (next+1) a b next d
          (⟨pc,.r3,saved⟩::stack) source 10)=
        some ⟨state (heap++[.pair a b,.pair next d]) (next+2) a b next (next+1)
          (⟨pc,.r3,saved⟩::stack) source 11,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,
        List.append_assoc,Nat.add_assoc]
    have t2 : tickNatural program
        (state (heap++[.pair a b,.pair next d]) (next+2) a b next (next+1)
          (⟨pc,.r3,saved⟩::stack) source 11)=
        some ⟨state (heap++[.pair a b,.pair next d]) (next+2)
          saved.a saved.b saved.c (next+1) stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    exact .step t0 (.step t1 (.step t2 (.done _)))
  · apply WordPairTableRead.Table.cons (item := next) (tail := d) (num := a) (den := b)
    · rw [List.getElem?_append_right (by omega)];simp [hn]
    · simp [hn]
    · exact boolList_extend ra _
    · exact boolList_extend rb _
    · exact BinaryIndexedPairRead.table_extend tail _

/-- Exact source requests and order are preserved by the actual recursive
constructor, on any dense incoming heap and beneath any supplied caller. -/
theorem read_return (rows : List (Bits × Bits)) (suffix : Bits) (heap : NaturalHeap)
    (next a b c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 32)
    (stack : List (Frame ℕ 32)) :
    ∃ ext root, ext.length=cells rows ∧
      NaturalRun program (steps rows)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) (encode rows++suffix) 0)
        ((encode rows).map Event.request)
        (state (heap++ext) (next+cells rows) saved.a saved.b saved.c root stack suffix pc) ∧
      WordPairTableRead.Table (heap++ext) root rows := by
  induction rows generalizing heap next a b c d saved pc stack with
  | nil =>
      let ext : NaturalHeap := [.flag false,.nil]
      have t0 : tickNatural program
          (state heap next a b c d (⟨pc,.r3,saved⟩::stack) (encode []++suffix) 0)=
          some ⟨state (heap++[.flag false]) (next+1) a b next d
            (⟨pc,.r3,saved⟩::stack) suffix 1,[.request false],0⟩ := by
        simp [tickNatural,program,state,encode,allocateNatural,Registers.set]
      have t1 : tickNatural program
          (state (heap++[.flag false]) (next+1) a b next d (⟨pc,.r3,saved⟩::stack) suffix 1)=
          some ⟨state (heap++[.flag false]) (next+1) a b next d (⟨pc,.r3,saved⟩::stack) suffix 2,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hn,tagBranch]
      have t2 : tickNatural program
          (state (heap++[.flag false]) (next+1) a b next d (⟨pc,.r3,saved⟩::stack) suffix 2)=
          some ⟨state (heap++ext) (next+2) a b next (next+1)
            (⟨pc,.r3,saved⟩::stack) suffix 3,[],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,
          ext,List.append_assoc,Nat.add_assoc]
      have t3 : tickNatural program
          (state (heap++ext) (next+2) a b next (next+1) (⟨pc,.r3,saved⟩::stack) suffix 3)=
          some ⟨state (heap++ext) (next+2) saved.a saved.b saved.c (next+1) stack suffix pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      refine ⟨ext,next+1,rfl,?_,?_⟩
      · simpa [encode,steps,bits,cells] using NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (.done _))))
      · apply WordPairTableRead.Table.nil
        rw [List.getElem?_append_right (by omega)];simp [ext,hn]
  | cons row rows ih =>
      rcases row with ⟨x,y⟩
      let frame : Frame ℕ 32 := ⟨pc,.r3,saved⟩
      let h1 := heap++[.flag true]
      have hn1 : next+1=h1.length := by simp [h1,hn]
      obtain ⟨ex,rx,lx,runX,repX⟩ := word_return x
        (SelfDelimitedWordProgram.encode y++encode rows++suffix) h1 (next+1) a b next d hn1
        ⟨a,b,next,d⟩ 5 (frame::stack)
      let h2 := h1++ex
      let n2 := next+1+3*x.length+2
      have hn2 : n2=h2.length := by simp [n2,h2,hn1,lx,Nat.add_assoc]
      obtain ⟨ey,ry,ly,runY,repY⟩ := word_return y (encode rows++suffix) h2 n2 rx b next rx hn2
        ⟨rx,b,next,rx⟩ 7 (frame::stack)
      let h3 := h2++ey
      let n3 := n2+3*y.length+2
      have hn3 : n3=h3.length := by simp [n3,h3,hn2,ly,Nat.add_assoc]
      obtain ⟨er,rr,lr,runR,repR⟩ := ih h3 n3 rx ry next ry hn3 ⟨rx,ry,next,ry⟩ 9 (frame::stack)
      let h4 := h3++er
      let n4 := n3+cells rows
      have hn4 : n4=h4.length := by simp [n4,h4,hn3,lr]
      have ra : BoolList h4 rx x := boolList_extend (boolList_extend repX ey) er
      have rb : BoolList h4 ry y := boolList_extend repY er
      obtain ⟨finish,rep⟩ := prepend_return n4 rx ry next rr hn4 ra rb repR saved pc stack suffix
      have t0 : tickNatural program (state heap next a b c d (frame::stack) (encode ((x,y)::rows)++suffix) 0)=
          some ⟨state h1 (next+1) a b next d (frame::stack)
            (SelfDelimitedWordProgram.encode x++SelfDelimitedWordProgram.encode y++encode rows++suffix)
            1,[.request true],0⟩ := by
        simp [tickNatural,program,state,encode,h1,allocateNatural,Registers.set,List.append_assoc]
      have t1 : tickNatural program (state h1 (next+1) a b next d (frame::stack)
          (SelfDelimitedWordProgram.encode x++SelfDelimitedWordProgram.encode y++encode rows++suffix) 1)=
          some ⟨state h1 (next+1) a b next d (frame::stack)
            (SelfDelimitedWordProgram.encode x++SelfDelimitedWordProgram.encode y++encode rows++suffix) 4,[],0⟩ := by
        simp [tickNatural,program,state,h1,Registers.get,hn,tagBranch]
      have t4 : tickNatural program (state h1 (next+1) a b next d (frame::stack)
          (SelfDelimitedWordProgram.encode x++SelfDelimitedWordProgram.encode y++encode rows++suffix) 4)=
          some ⟨state h1 (next+1) a b next d (⟨5,.r3,⟨a,b,next,d⟩⟩::frame::stack)
            (SelfDelimitedWordProgram.encode x++SelfDelimitedWordProgram.encode y++encode rows++suffix) 25,[],0⟩ := by
        simp [tickNatural,program,state]
      have t5 : tickNatural program (state h2 n2 a b next rx (frame::stack)
          (SelfDelimitedWordProgram.encode y++encode rows++suffix) 5)=
          some ⟨state h2 n2 rx b next rx (frame::stack)
            (SelfDelimitedWordProgram.encode y++encode rows++suffix) 6,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t6 : tickNatural program (state h2 n2 rx b next rx (frame::stack)
          (SelfDelimitedWordProgram.encode y++encode rows++suffix) 6)=
          some ⟨state h2 n2 rx b next rx (⟨7,.r3,⟨rx,b,next,rx⟩⟩::frame::stack)
            (SelfDelimitedWordProgram.encode y++encode rows++suffix) 25,[],0⟩ := by
        simp [tickNatural,program,state]
      have t7 : tickNatural program (state h3 n3 rx b next ry (frame::stack) (encode rows++suffix) 7)=
          some ⟨state h3 n3 rx ry next ry (frame::stack) (encode rows++suffix) 8,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t8 : tickNatural program (state h3 n3 rx ry next ry (frame::stack) (encode rows++suffix) 8)=
          some ⟨state h3 n3 rx ry next ry (⟨9,.r3,⟨rx,ry,next,ry⟩⟩::frame::stack)
            (encode rows++suffix) 0,[],0⟩ := by
        simp [tickNatural,program,state]
      let ext := [.flag true]++ex++ey++er++[.pair rx ry,.pair n4 rr]
      refine ⟨ext,n4+1,?_,?_,?_⟩
      · simp [ext,cells,bits,lx,ly,lr];omega
      · simp only [List.append_assoc] at t0 t1 t4 t5 t6 runX runY
        have all := NaturalRun.step t0 (.step t1 (.step t4
            (run_append runX (.step t5 (.step t6
              (run_append runY (.step t7 (.step t8 (run_append runR finish)))))))))
        convert all using 1 <;>
          simp [steps,cells,bits,encode,ext,h1,h2,h3,h4,n2,n3,n4,
            List.append_assoc,List.map_append,Nat.add_assoc]
        all_goals first | omega | (congr 1; omega)
      · simpa [ext,h1,h2,h3,h4,List.append_assoc] using rep

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

/-- The same low interpreter builds the ordered row table directly from its source
encoding. All row/word marker and data requests and allocations are included. -/
theorem read (rows : List (Bits × Bits)) (suffix : Bits) :
    ∃ charge out, Run program (steps rows+1) charge (initial (encode rows++suffix))
        ((encode rows).map Event.request) out ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState out).registers.d rows ∧
      out.source=suffix ∧ out.pc=31 ∧ out.stack=[] ∧
      out.heap.length=cells rows ∧ value out.next=out.heap.length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 32 1 0 (steps rows+1) := by
  obtain ⟨ext,root,len,body,rep⟩ := read_return rows suffix [] 0 0 0 0 0 rfl ⟨0,0,0,0⟩ 31 []
  let final := state ext (cells rows) 0 0 0 root [] suffix 31
  have start : tickNatural program (eraseState (initial (encode rows++suffix)))=
      some ⟨state [] 0 0 0 0 0 [⟨31,.r3,⟨0,0,0,0⟩⟩] (encode rows++suffix) 0,[],0⟩ := by
    simp [tickNatural,program,initial,eraseState,State.map,state,value,Registers.map]
  have high : NaturalRun program (steps rows+1)
      (eraseState (initial (encode rows++suffix))) ((encode rows).map Event.request) final := by
    simpa [final,state,Nat.add_assoc] using NaturalRun.step start body
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation (initial_bounded _) high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    have halt : tickNatural program final=none := rfl
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,source,?_,?_,?_,?_,stop,
    (terminal_accounting run (initial_bounded _) stop).2⟩
  · rw [erase]
    simpa [final,state] using rep
  · exact congrArg State.pc erase
  · have h : (eraseState out).stack=[] := congrArg State.stack erase
    simpa [eraseState,State.map] using h
  · have h := congrArg (fun s : NaturalState 32 => s.heap.length) erase
    simpa [eraseState,State.map,final,state,len] using h
  · have h := congrArg State.next erase
    have hl := congrArg (fun s : NaturalState 32 => s.heap.length) erase
    simp only [eraseState,State.map,List.length_map,final,state] at h hl
    omega

/-- The table is constructed directly from source in a stored-size polynomial,
including all row and word markers and the single final halt. -/
theorem total_bound (rows : List (Bits × Bits)) :
    completeBound 32 1 0 (steps rows+1) ≤ 10000000*(bits rows+rows.length+1)^3 := by
  let z := bits rows+rows.length+1
  have hz : 1 ≤ z := by dsimp [z];omega
  have ht : steps rows+1 ≤ 22*z := by dsimp [steps,z];omega
  have hs : 2*(steps rows+1)+2 ≤ 46*z := by omega
  have hr : steps rows+1+2 ≤ 24*z := by omega
  unfold completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 176*(22*z)*(46*z)^2+176*(24*z)*(24*z) := by gcongr <;> omega
    _ ≤ 10000000*z^3 := by
      have hz2 : z^2 ≤ z^3 := by nlinarith
      nlinarith

end DirectedFlowCutGap.SourceRowTableProgram
