import DirectedFlowCutGap.PackedBooleanConstructor

/-! A literal ten-slot program reads a self-delimiting Boolean word directly
from the source. A true marker precedes each stored data bit; false terminates.
No encoded length, incoming heap representation or host decoder is supplied. -/
namespace DirectedFlowCutGap.SelfDelimitedWordProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def encode : Bits → Bits
  | [] => [false]
  | b::bs => true::b::encode bs

def program : Program 10 := fun pc => match pc.val with
  | 0 => .request .r0 1
  | 1 => .branch .r0 8 2 3 8
  | 2 => .make .r3 .nil 7
  | 3 => .request .r2 4
  | 4 => .call 0 5 .r3
  | 5 => .make .r3 (.pair .r2 .r3) 7
  | 7 => .ret .r3
  | 9 => .call 0 8 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 10)) (source : Bits) (pc : Fin 10) : NaturalState 10 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem encode_length (word : Bits) : (encode word).length=2*word.length+1 := by
  induction word with
  | nil => rfl
  | cons b bs ih => simp only [encode,List.length_cons];omega

theorem run_append {s u v : NaturalState 10} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- Exact literal requests, real recursive callers, original data order and
actual unused source suffix are retained in one execution. -/
theorem read_return (word suffix : Bits) (heap : NaturalHeap) (next a b c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 10)
    (stack : List (Frame ℕ 10)) :
    ∃ ext root, ext.length=3*word.length+2 ∧
      NaturalRun program (6*word.length+4)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) (encode word++suffix) 0)
        ((encode word).map Event.request)
        (state (heap++ext) (next+3*word.length+2) saved.a saved.b saved.c root stack suffix pc) ∧
      BoolList (heap++ext) root word := by
  induction word generalizing heap next a b c d saved pc stack with
  | nil =>
      let ext : NaturalHeap := [.flag false,.nil]
      refine ⟨ext,next+1,rfl,?_,?_⟩
      · have t0 : tickNatural program
            (state heap next a b c d (⟨pc,.r3,saved⟩::stack) (encode []++suffix) 0)=
            some ⟨state (heap++[.flag false]) (next+1) next b c d
              (⟨pc,.r3,saved⟩::stack) suffix 1,[.request false],0⟩ := by
          simp [tickNatural,program,state,encode,allocateNatural,Registers.set]
        have t1 : tickNatural program
            (state (heap++[.flag false]) (next+1) next b c d (⟨pc,.r3,saved⟩::stack) suffix 1)=
            some ⟨state (heap++[.flag false]) (next+1) next b c d
              (⟨pc,.r3,saved⟩::stack) suffix 2,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hn,tagBranch]
        have t2 : tickNatural program
            (state (heap++[.flag false]) (next+1) next b c d (⟨pc,.r3,saved⟩::stack) suffix 2)=
            some ⟨state (heap++ext) (next+2) next b c (next+1)
              (⟨pc,.r3,saved⟩::stack) suffix 7,[],0⟩ := by
          simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,
            ext,List.append_assoc,Nat.add_assoc]
        have t7 : tickNatural program
            (state (heap++ext) (next+2) next b c (next+1) (⟨pc,.r3,saved⟩::stack) suffix 7)=
            some ⟨state (heap++ext) (next+2) saved.a saved.b saved.c (next+1) stack suffix pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        simpa [encode] using NaturalRun.step t0 (NaturalRun.step t1
          (NaturalRun.step t2 (NaturalRun.step t7 (NaturalRun.done _))))
      · apply BoolList.nil
        rw [List.getElem?_append_right (by omega)]
        simp [ext,hn]
  | cons bit word ih =>
      let frame : Frame ℕ 10 := ⟨pc,.r3,saved⟩
      let first : NaturalHeap := heap++[.flag true,.flag bit]
      have hn' : next+2=first.length := by simp [first,hn]
      obtain ⟨ext,root,len,body,rep⟩ := ih first (next+2) next b (next+1) d hn'
        ⟨next,b,next+1,d⟩ 5 (frame::stack)
      let fresh := next+2+3*word.length+2
      let total : NaturalHeap := [.flag true,.flag bit]++ext++[.pair (next+1) root]
      have t0 : tickNatural program
          (state heap next a b c d (frame::stack) (encode (bit::word)++suffix) 0)=
          some ⟨state (heap++[.flag true]) (next+1) next b c d
            (frame::stack) (bit::(encode word++suffix)) 1,[.request true],0⟩ := by
        simp [tickNatural,program,state,encode,allocateNatural,Registers.set]
      have t1 : tickNatural program
          (state (heap++[.flag true]) (next+1) next b c d
            (frame::stack) (bit::(encode word++suffix)) 1)=
          some ⟨state (heap++[.flag true]) (next+1) next b c d
            (frame::stack) (bit::(encode word++suffix)) 3,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hn,tagBranch]
      have t3 : tickNatural program
          (state (heap++[.flag true]) (next+1) next b c d
            (frame::stack) (bit::(encode word++suffix)) 3)=
          some ⟨state first (next+2) next b (next+1) d
            (frame::stack) (encode word++suffix) 4,[.request bit],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Registers.set,first,
          List.append_assoc,Nat.add_assoc]
      have t4 : tickNatural program
          (state first (next+2) next b (next+1) d (frame::stack) (encode word++suffix) 4)=
          some ⟨state first (next+2) next b (next+1) d
            (⟨5,.r3,⟨next,b,next+1,d⟩⟩::frame::stack) (encode word++suffix) 0,[],0⟩ := by
        simp [tickNatural,program,state]
      have t5 : tickNatural program
          (state (first++ext) fresh next b (next+1) root (frame::stack) suffix 5)=
          some ⟨state (heap++total) (fresh+1) next b (next+1) fresh
            (frame::stack) suffix 7,[],0⟩ := by
        simp [tickNatural,program,state,Recipe.cell,allocateNatural,Registers.get,
          Registers.set,first,total,List.append_assoc]
      have t7 : tickNatural program
          (state (heap++total) (fresh+1) next b (next+1) fresh (frame::stack) suffix 7)=
          some ⟨state (heap++total) (fresh+1) saved.a saved.b saved.c fresh stack suffix pc,[],0⟩ := by
        simp [tickNatural,program,state,frame,Registers.get,Registers.set]
      refine ⟨total,fresh,?_,?_,?_⟩
      · simp [total,len];omega
      · have finish := NaturalRun.step t5 (NaturalRun.step t7 (NaturalRun.done _))
        have full := run_append body finish
        convert NaturalRun.step t0 (NaturalRun.step t1 (NaturalRun.step t3 (NaturalRun.step t4 full))) using 1 <;>
          simp [encode,List.length_cons,fresh,state]
        all_goals omega
      · apply BoolList.cons (head := next+1) (tail := root)
        · have hbase : (heap++[Cell.flag true,Cell.flag bit]++ext).length=fresh := by simp [fresh,len,hn];omega
          have shape : heap++total=(heap++[Cell.flag true,Cell.flag bit]++ext)++[.pair (next+1) root] := by
            simp [total,List.append_assoc]
          rw [shape,←hbase]
          rw [List.getElem?_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self,List.getElem?_cons_zero]
        · have shape : heap++total=(heap++[Cell.flag true,Cell.flag bit])++(ext++[.pair (next+1) root]) := by
            simp [total,List.append_assoc]
          rw [shape]
          rw [List.getElem?_append_left (by simp [hn])]
          rw [List.getElem?_append_right (by omega)]
          simp [hn]
        · simpa [first,total,List.append_assoc] using boolList_extend rep [.pair (next+1) root]

/-- Empty-heap entry needs no preconstructed length or represented word. -/
def initial (source : Bits) : BitState 10 := ⟨[],[],⟨[],[],[],[]⟩,[],9,source⟩

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

/-- The same low interpreter builds the ordered word directly from its source
encoding. All marker/data requests and allocations are included. -/
theorem read (word suffix : Bits) :
    ∃ charge out, Run program (6*word.length+5) charge (initial (encode word++suffix))
        ((encode word).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d word ∧
      out.source=suffix ∧ out.pc=8 ∧ out.stack=[] ∧
      out.heap.length=3*word.length+2 ∧ value out.next=out.heap.length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 10 1 0 (6*word.length+5) := by
  obtain ⟨ext,root,len,body,rep⟩ := read_return word suffix [] 0 0 0 0 0 rfl ⟨0,0,0,0⟩ 8 []
  let final := state ext (3*word.length+2) 0 0 0 root [] suffix 8
  have start : tickNatural program (eraseState (initial (encode word++suffix)))=
      some ⟨state [] 0 0 0 0 0 [⟨8,.r3,⟨0,0,0,0⟩⟩] (encode word++suffix) 0,[],0⟩ := by
    simp [tickNatural,program,initial,eraseState,State.map,state,value,Registers.map]
  have high : NaturalRun program (6*word.length+5)
      (eraseState (initial (encode word++suffix))) ((encode word).map Event.request) final := by
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
  · have h := congrArg (fun s : NaturalState 10 => s.heap.length) erase
    simpa [eraseState,State.map,final,state,len] using h
  · have h := congrArg State.next erase
    have hl := congrArg (fun s : NaturalState 10 => s.heap.length) erase
    simp only [eraseState,State.map,List.length_map,final,state] at h hl
    omega

/-- Polynomial in the number of stored data bits, with no uncharged input-heap
constructor or encoded-size word premise. -/
theorem total_bound (word : Bits) :
    completeBound 10 1 0 (6*word.length+5) ≤ 200000*(word.length+1)^3 := by
  let z := word.length+1
  have hz : 1 ≤ z := by dsimp [z];omega
  have ht : 6*word.length+5 ≤ 6*z := by dsimp [z];omega
  have hs : 2*(6*word.length+5)+2 ≤ 14*z := by omega
  have hr : 6*word.length+5+2 ≤ 8*z := by omega
  unfold completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 154*(6*z)*(14*z)^2+154*(8*z)*(8*z) := by gcongr <;> omega
    _ ≤ 200000*z^3 := by
      have hz2 : z^2 ≤ z^3 := by nlinarith
      nlinarith

end DirectedFlowCutGap.SelfDelimitedWordProgram
