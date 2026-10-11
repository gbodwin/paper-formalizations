import DirectedFlowCutGap.BinaryMultiplicationProgram
import DirectedFlowCutGap.InputAdditionProgram

/-! Two actual self-delimited source readers followed by the actual multiplication
machine. The finite table creates both represented operands from an empty heap;
only the explicit well-formed source encoding is assumed. -/
namespace DirectedFlowCutGap.InputMultiplicationProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def mulLabel (pc : Fin 96) : Fin 116 := ⟨pc.val,by omega⟩
def firstLabel (pc : Fin 10) : Fin 116 := ⟨pc.val+96,by omega⟩
def secondLabel (pc : Fin 10) : Fin 116 := ⟨pc.val+106,by omega⟩

/-- Reader halts become literal moves. Both completed operands are then passed
to the unchanged multiplication entry; its halt is the sole final halt. -/
def program : Program 116 := fun pc =>
  if h : pc.val < 96 then
    ReferenceProgramLabels.instruction mulLabel (BinaryMultiplicationProgram.program ⟨pc.val,h⟩)
  else if pc.val = 104 then .move .r0 .r3 115
  else if pc.val = 114 then .move .r1 .r3 94
  else if h : pc.val < 106 then
    ReferenceProgramLabels.instruction firstLabel
      (SelfDelimitedWordProgram.program ⟨pc.val-96,by omega⟩)
  else
    ReferenceProgramLabels.instruction secondLabel
      (SelfDelimitedWordProgram.program ⟨pc.val-106,by omega⟩)

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (source : Bits) (pc : Fin 116) : NaturalState 116 :=
  ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩

def initial (source : Bits) : BitState 116 := ⟨[],[],⟨[],[],[],[]⟩,[],105,source⟩
def instructions (xs ys : Bits) : ℕ :=
  (6*xs.length+5)+1+(6*ys.length+5)+1+(BinaryMultiplicationProgram.steps xs ys+1)

theorem mul_slots (pc : Fin 96) :
    program (mulLabel pc)=ReferenceProgramLabels.instruction mulLabel
      (BinaryMultiplicationProgram.program pc) := by
  simp [program,mulLabel,pc.isLt]

theorem first_slots (pc : Fin 10) (h : SelfDelimitedWordProgram.program pc ≠ .halt) :
    program (firstLabel pc)=ReferenceProgramLabels.instruction firstLabel
      (SelfDelimitedWordProgram.program pc) := by
  fin_cases pc <;> simp_all [program,firstLabel,SelfDelimitedWordProgram.program]

theorem second_slots (pc : Fin 10) (h : SelfDelimitedWordProgram.program pc ≠ .halt) :
    program (secondLabel pc)=ReferenceProgramLabels.instruction secondLabel
      (SelfDelimitedWordProgram.program pc) := by
  fin_cases pc <;> simp_all [program,secondLabel,SelfDelimitedWordProgram.program]

theorem run_append {s u v : NaturalState 116} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- One literal program requests both complete encodings, computes their product,
and retains the same two operands, output and unused source suffix. -/
theorem run_high (xs ys suffix : Bits) :
    ∃ final, NaturalRun program (instructions xs ys)
        (eraseState (initial (SelfDelimitedWordProgram.encode xs++
          SelfDelimitedWordProgram.encode ys++suffix)))
        ((SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys).map Event.request) final ∧
      BoolList final.heap final.registers.d (mul xs ys).1 ∧
      BoolList final.heap final.registers.a xs ∧ BoolList final.heap final.registers.b ys ∧
      final.source=suffix ∧ final.pc=95 ∧ final.stack=[] ∧
      final.heap.length=3*(xs.length+ys.length)+4+BinaryMultiplicationProgram.cells xs ys ∧
      final.next=final.heap.length ∧ tickNatural program final=none := by
  obtain ⟨ex,rx,lx,hx,repX⟩ := InputAdditionProgram.reader_high xs (SelfDelimitedWordProgram.encode ys++suffix)
    [] 0 0 0 0 0 rfl
  have nx : 3*xs.length+2=ex.length := lx.symm
  obtain ⟨ey,ry,ly,hy,repY⟩ := InputAdditionProgram.reader_high ys suffix ex (3*xs.length+2) rx 0 0 rx nx
  let ny := (3*xs.length+2)+3*ys.length+2
  have hny : ny=(ex++ey).length := by simp [ny,lx,ly];omega
  have left : BoolList (ex++ey) rx xs := by
    apply boolList_extend (by simpa using repX) ey
  obtain ⟨ez,rz,lz,hz,repZ⟩ := BinaryMultiplicationProgram.mul_return left repY
    ny 0 ry hny ⟨rx,ry,0,ry⟩ 95 [] suffix
  have startTick : tickNatural BinaryMultiplicationProgram.program
      (BinaryMultiplicationProgram.state (ex++ey) ny rx ry 0 ry [] suffix 94)=
      some ⟨BinaryMultiplicationProgram.state (ex++ey) ny rx ry 0 ry
        [⟨95,.r3,⟨rx,ry,0,ry⟩⟩] suffix 64,[],0⟩ := by
    simp [tickNatural,BinaryMultiplicationProgram.program,BinaryMultiplicationProgram.state]
  have ha := ReferenceProgramLabels.run mulLabel BinaryMultiplicationProgram.program program
    (fun pc _ => mul_slots pc) (NaturalRun.step startTick hz)
  have hxa := ReferenceProgramLabels.run firstLabel SelfDelimitedWordProgram.program program
    first_slots hx
  have hya := ReferenceProgramLabels.run secondLabel SelfDelimitedWordProgram.program program
    second_slots hy
  have first : NaturalRun program (6*xs.length+5)
      (eraseState (initial (SelfDelimitedWordProgram.encode xs++
        SelfDelimitedWordProgram.encode ys++suffix)))
      ((SelfDelimitedWordProgram.encode xs).map Event.request)
      (state ex (3*xs.length+2) 0 0 0 rx (SelfDelimitedWordProgram.encode ys++suffix) 104) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,firstLabel,
      SelfDelimitedWordProgram.state,state,initial,eraseState,State.map,Registers.map,value,
      List.append_assoc] using hxa
  have move1 : tickNatural program
      (state ex (3*xs.length+2) 0 0 0 rx (SelfDelimitedWordProgram.encode ys++suffix) 104)=
      some ⟨state ex (3*xs.length+2) rx 0 0 rx
        (SelfDelimitedWordProgram.encode ys++suffix) 115,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have second : NaturalRun program (6*ys.length+5)
      (state ex (3*xs.length+2) rx 0 0 rx (SelfDelimitedWordProgram.encode ys++suffix) 115)
      ((SelfDelimitedWordProgram.encode ys).map Event.request)
      (state (ex++ey) ny rx 0 0 ry suffix 114) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,secondLabel,
      SelfDelimitedWordProgram.state,state,ny] using hya
  have move2 : tickNatural program (state (ex++ey) ny rx 0 0 ry suffix 114)=
      some ⟨state (ex++ey) ny rx ry 0 ry suffix 94,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  let final := state ((ex++ey)++ez) (ny+BinaryMultiplicationProgram.cells xs ys)
    rx ry 0 rz suffix 95
  have third : NaturalRun program (BinaryMultiplicationProgram.steps xs ys+1)
      (state (ex++ey) ny rx ry 0 ry suffix 94) [] final := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,mulLabel,
      BinaryMultiplicationProgram.state,state,final] using ha
  refine ⟨final,?_,repZ,boolList_extend left ez,boolList_extend repY ez,
    rfl,rfl,rfl,?_,?_,?_⟩
  · have all := run_append first (NaturalRun.step move1
        (run_append second (NaturalRun.step move2 third)))
    convert all using 1 <;> simp [instructions,List.map_append]; omega
  · simp [final,state,lx,ly,lz];omega
  · simp [final,state,ny,lx,ly,lz];omega
  · simp [tickNatural,program,final,state,
      ReferenceProgramLabels.instruction,BinaryMultiplicationProgram.program]

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

theorem instructions_bound (xs ys : Bits) :
    instructions xs ys ≤ 160*(xs.length+ys.length+1)^2 := by
  have h := BinaryMultiplicationProgram.steps_bound xs ys
  unfold instructions
  nlinarith

/-- No represented operands, cursor word or input heap is supplied. The same
lower run performs both readers, moves and multiplication, and pays its sole halt. -/
theorem mul_from_source (xs ys suffix : Bits) :
    ∃ charge out, Run program (instructions xs ys) charge
        (initial (SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys++suffix))
        ((SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (mul xs ys).1 ∧
      value (mul xs ys).1=value xs*value ys ∧
      BoolList (eraseState out).heap (eraseState out).registers.a xs ∧
      BoolList (eraseState out).heap (eraseState out).registers.b ys ∧
      out.source=suffix ∧ out.pc=95 ∧ out.stack=[] ∧
      out.heap.length=3*(xs.length+ys.length)+4+BinaryMultiplicationProgram.cells xs ys ∧
      value out.next=out.heap.length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 116 1 0 (instructions xs ys) := by
  obtain ⟨final,high,rep,lword,rword,src,pc,frames,len,dense,halt⟩ := run_high xs ys suffix
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation (initial_bounded _) high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,by simpa using (mul_spec xs ys).1,?_,?_,
    source.trans src,?_,?_,?_,?_,stop,(terminal_accounting run (initial_bounded _) stop).2⟩
  · rw [erase];exact rep
  · rw [erase];exact lword
  · rw [erase];exact rword
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).heap.length=3*(xs.length+ys.length)+4+
        BinaryMultiplicationProgram.cells xs ys := by rw [erase];exact len
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];exact dense
    simpa [eraseState,State.map] using h

/-- All source reads, heap copies, call frames, address arithmetic, real product
instructions and the final halt are paid in this one stored-length bound. -/
theorem total_bound (xs ys : Bits) :
    completeBound 116 1 0 (instructions xs ys) ≤
      6000000000*(xs.length+ys.length+1)^6 := by
  let z := xs.length+ys.length+1
  have hz : 1 ≤ z := by dsimp [z];omega
  have hz2 : 1 ≤ z^2 := by nlinarith
  have ht : instructions xs ys ≤ 160*z^2 := instructions_bound xs ys
  have hs : 2*instructions xs ys+2 ≤ 322*z^2 := by omega
  have hr : instructions xs ys+2 ≤ 162*z^2 := by omega
  have hb : instructions xs ys+1 ≤ 161*z^2 := by omega
  unfold completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 260*(160*z^2)*(322*z^2)^2+260*(162*z^2)*(161*z^2) := by gcongr <;> omega
    _ ≤ 6000000000*z^6 := by
      have hz46 : z^4 ≤ z^6 := by exact Nat.pow_le_pow_right hz (by omega)
      nlinarith


end DirectedFlowCutGap.InputMultiplicationProgram
