import DirectedFlowCutGap.BinaryAdditionProgram
import DirectedFlowCutGap.SelfDelimitedWordProgram

/-! Two actual self-delimited source readers followed by the actual addition
machine. The finite table creates both represented operands from an empty heap;
only the explicit well-formed source encoding is assumed. -/
namespace DirectedFlowCutGap.InputAdditionProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def addLabel (pc : Fin 64) : Fin 84 := ⟨pc.val,by omega⟩
def firstLabel (pc : Fin 10) : Fin 84 := ⟨pc.val+64,by omega⟩
def secondLabel (pc : Fin 10) : Fin 84 := ⟨pc.val+74,by omega⟩

/-- Reader halts become literal moves. Both completed operands are then passed
to the unchanged no-carry addition entry; its halt is the sole final halt. -/
def program : Program 84 := fun pc =>
  if h : pc.val < 64 then
    ReferenceProgramLabels.instruction addLabel (BinaryAdditionProgram.program ⟨pc.val,h⟩)
  else if pc.val = 72 then .move .r0 .r3 83
  else if pc.val = 82 then .move .r1 .r3 60
  else if h : pc.val < 74 then
    ReferenceProgramLabels.instruction firstLabel
      (SelfDelimitedWordProgram.program ⟨pc.val-64,by omega⟩)
  else
    ReferenceProgramLabels.instruction secondLabel
      (SelfDelimitedWordProgram.program ⟨pc.val-74,by omega⟩)

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (source : Bits) (pc : Fin 84) : NaturalState 84 :=
  ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩

def initial (source : Bits) : BitState 84 := ⟨[],[],⟨[],[],[],[]⟩,[],73,source⟩
def instructions (xs ys : Bits) : ℕ :=
  (6*xs.length+5)+1+(6*ys.length+5)+1+(BinaryAdditionProgram.steps false xs ys+1)

theorem add_slots (pc : Fin 64) :
    program (addLabel pc)=ReferenceProgramLabels.instruction addLabel
      (BinaryAdditionProgram.program pc) := by
  simp [program,addLabel,pc.isLt]

theorem first_slots (pc : Fin 10) (h : SelfDelimitedWordProgram.program pc ≠ .halt) :
    program (firstLabel pc)=ReferenceProgramLabels.instruction firstLabel
      (SelfDelimitedWordProgram.program pc) := by
  fin_cases pc <;> simp_all [program,firstLabel,SelfDelimitedWordProgram.program]

theorem second_slots (pc : Fin 10) (h : SelfDelimitedWordProgram.program pc ≠ .halt) :
    program (secondLabel pc)=ReferenceProgramLabels.instruction secondLabel
      (SelfDelimitedWordProgram.program pc) := by
  fin_cases pc <;> simp_all [program,secondLabel,SelfDelimitedWordProgram.program]

theorem run_append {s u v : NaturalState 84} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The already proved reader body is entered by a real top-level call on an
arbitrary existing dense heap. All caller registers except the result survive. -/
theorem reader_high (word suffix : Bits) (heap : NaturalHeap) (next a b c d : ℕ)
    (hn : next=heap.length) :
    ∃ ext root, ext.length=3*word.length+2 ∧
      NaturalRun SelfDelimitedWordProgram.program (6*word.length+5)
        (SelfDelimitedWordProgram.state heap next a b c d []
          (SelfDelimitedWordProgram.encode word++suffix) 9)
        ((SelfDelimitedWordProgram.encode word).map Event.request)
        (SelfDelimitedWordProgram.state (heap++ext) (next+3*word.length+2)
          a b c root [] suffix 8) ∧
      BoolList (heap++ext) root word := by
  obtain ⟨ext,root,len,body,rep⟩ := SelfDelimitedWordProgram.read_return word suffix
    heap next a b c d hn ⟨a,b,c,d⟩ 8 []
  have top : tickNatural SelfDelimitedWordProgram.program
      (SelfDelimitedWordProgram.state heap next a b c d []
        (SelfDelimitedWordProgram.encode word++suffix) 9)=
      some ⟨SelfDelimitedWordProgram.state heap next a b c d [⟨8,.r3,⟨a,b,c,d⟩⟩]
        (SelfDelimitedWordProgram.encode word++suffix) 0,[],0⟩ := by
    simp [tickNatural,SelfDelimitedWordProgram.program,SelfDelimitedWordProgram.state]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using NaturalRun.step top body,rep⟩

/-- One literal program requests both complete encodings, computes their sum,
and retains the same two operands, output and unused source suffix. -/
theorem run_high (xs ys suffix : Bits) :
    ∃ final, NaturalRun program (instructions xs ys)
        (eraseState (initial (SelfDelimitedWordProgram.encode xs++
          SelfDelimitedWordProgram.encode ys++suffix)))
        ((SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys).map Event.request) final ∧
      BoolList final.heap final.registers.d (add false xs ys).1 ∧
      BoolList final.heap final.registers.a xs ∧ BoolList final.heap final.registers.b ys ∧
      final.source=suffix ∧ final.pc=63 ∧ final.stack=[] ∧
      final.heap.length=3*(xs.length+ys.length)+4+BinaryAdditionProgram.cells false xs ys ∧
      final.next=final.heap.length ∧ tickNatural program final=none := by
  obtain ⟨ex,rx,lx,hx,repX⟩ := reader_high xs (SelfDelimitedWordProgram.encode ys++suffix)
    [] 0 0 0 0 0 rfl
  have nx : 3*xs.length+2=ex.length := lx.symm
  obtain ⟨ey,ry,ly,hy,repY⟩ := reader_high ys suffix ex (3*xs.length+2) rx 0 0 rx nx
  let ny := (3*xs.length+2)+3*ys.length+2
  have hny : ny=(ex++ey).length := by simp [ny,lx,ly];omega
  have left : BoolList (ex++ey) rx xs := by
    apply boolList_extend (by simpa using repX) ey
  obtain ⟨ez,rz,lz,hz,repZ⟩ := BinaryAdditionProgram.add_return left repY false
    ny 0 ry hny ⟨rx,ry,0,ry⟩ 63 [] suffix
  have startTick : tickNatural BinaryAdditionProgram.program
      (BinaryAdditionProgram.state (ex++ey) ny rx ry 0 ry [] suffix 60)=
      some ⟨BinaryAdditionProgram.state (ex++ey) ny rx ry 0 ry
        [⟨63,.r3,⟨rx,ry,0,ry⟩⟩] suffix 16,[],0⟩ := by
    simp [tickNatural,BinaryAdditionProgram.program,BinaryAdditionProgram.state]
  have ha := ReferenceProgramLabels.run addLabel BinaryAdditionProgram.program program
    (fun pc _ => add_slots pc) (NaturalRun.step startTick hz)
  have hxa := ReferenceProgramLabels.run firstLabel SelfDelimitedWordProgram.program program
    first_slots hx
  have hya := ReferenceProgramLabels.run secondLabel SelfDelimitedWordProgram.program program
    second_slots hy
  have first : NaturalRun program (6*xs.length+5)
      (eraseState (initial (SelfDelimitedWordProgram.encode xs++
        SelfDelimitedWordProgram.encode ys++suffix)))
      ((SelfDelimitedWordProgram.encode xs).map Event.request)
      (state ex (3*xs.length+2) 0 0 0 rx (SelfDelimitedWordProgram.encode ys++suffix) 72) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,firstLabel,
      SelfDelimitedWordProgram.state,state,initial,eraseState,State.map,Registers.map,value,
      List.append_assoc] using hxa
  have move1 : tickNatural program
      (state ex (3*xs.length+2) 0 0 0 rx (SelfDelimitedWordProgram.encode ys++suffix) 72)=
      some ⟨state ex (3*xs.length+2) rx 0 0 rx
        (SelfDelimitedWordProgram.encode ys++suffix) 83,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have second : NaturalRun program (6*ys.length+5)
      (state ex (3*xs.length+2) rx 0 0 rx (SelfDelimitedWordProgram.encode ys++suffix) 83)
      ((SelfDelimitedWordProgram.encode ys).map Event.request)
      (state (ex++ey) ny rx 0 0 ry suffix 82) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,secondLabel,
      SelfDelimitedWordProgram.state,state,ny] using hya
  have move2 : tickNatural program (state (ex++ey) ny rx 0 0 ry suffix 82)=
      some ⟨state (ex++ey) ny rx ry 0 ry suffix 60,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  let final := state ((ex++ey)++ez) (ny+BinaryAdditionProgram.cells false xs ys)
    rx ry 0 rz suffix 63
  have third : NaturalRun program (BinaryAdditionProgram.steps false xs ys+1)
      (state (ex++ey) ny rx ry 0 ry suffix 60) [] final := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,addLabel,
      BinaryAdditionProgram.state,BinaryAdditionProgram.entry,state,final] using ha
  refine ⟨final,?_,repZ,boolList_extend left ez,boolList_extend repY ez,
    rfl,rfl,rfl,?_,?_,?_⟩
  · have all := run_append first (NaturalRun.step move1
        (run_append second (NaturalRun.step move2 third)))
    convert all using 1 <;> simp [instructions,List.map_append]; omega
  · simp [final,state,lx,ly,lz];omega
  · simp [final,state,ny,lx,ly,lz];omega
  · simp [tickNatural,program,final,state,
      ReferenceProgramLabels.instruction,BinaryAdditionProgram.program]

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

theorem instructions_bound (xs ys : Bits) :
    instructions xs ys ≤ 24*(xs.length+ys.length+1) := by
  have h := BinaryAdditionProgram.steps_bound false xs ys
  unfold instructions
  omega

/-- No represented operands, cursor word or input heap is supplied. The same
lower run performs both readers, moves and addition, and pays its sole halt. -/
theorem add_from_source (xs ys suffix : Bits) :
    ∃ charge out, Run program (instructions xs ys) charge
        (initial (SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys++suffix))
        ((SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (add false xs ys).1 ∧
      value (add false xs ys).1=value xs+value ys ∧
      BoolList (eraseState out).heap (eraseState out).registers.a xs ∧
      BoolList (eraseState out).heap (eraseState out).registers.b ys ∧
      out.source=suffix ∧ out.pc=63 ∧ out.stack=[] ∧
      out.heap.length=3*(xs.length+ys.length)+4+BinaryAdditionProgram.cells false xs ys ∧
      value out.next=out.heap.length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 84 1 0 (instructions xs ys) := by
  obtain ⟨final,high,rep,lword,rword,src,pc,frames,len,dense,halt⟩ := run_high xs ys suffix
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation (initial_bounded _) high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,by simpa using (add_spec false xs ys).1,?_,?_,
    source.trans src,?_,?_,?_,?_,stop,(terminal_accounting run (initial_bounded _) stop).2⟩
  · rw [erase];exact rep
  · rw [erase];exact lword
  · rw [erase];exact rword
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).heap.length=3*(xs.length+ys.length)+4+
        BinaryAdditionProgram.cells false xs ys := by rw [erase];exact len
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];exact dense
    simpa [eraseState,State.map] using h

/-- All source reads, heap copies, call frames, address arithmetic, real sum
instructions and the final halt are paid in this one stored-length bound. -/
theorem total_bound (xs ys : Bits) :
    completeBound 84 1 0 (instructions xs ys) ≤
      15000000*(xs.length+ys.length+1)^3 := by
  let z := xs.length+ys.length+1
  have hz : 1 ≤ z := by dsimp [z];omega
  have ht : instructions xs ys ≤ 24*z := instructions_bound xs ys
  have hs : 2*instructions xs ys+2 ≤ 50*z := by omega
  have hr : instructions xs ys+2 ≤ 26*z := by omega
  have hb : instructions xs ys+1 ≤ 25*z := by omega
  unfold completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 228*(24*z)*(50*z)^2+228*(26*z)*(25*z) := by gcongr <;> omega
    _ ≤ 15000000*z^3 := by
      have hz2 : z^2 ≤ z^3 := by nlinarith
      nlinarith

end DirectedFlowCutGap.InputAdditionProgram
