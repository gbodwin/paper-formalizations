import DirectedFlowCutGap.CandidateCapacityFlags
import DirectedFlowCutGap.ReferenceProgramSteps

/-!
# Shared binary words for candidate capacities

The program constructs one word for each pair of capacity flags from a stored budget.
The selector reads the two capacity flags and returns the existing word
address without another arithmetic pass.
-/

namespace DirectedFlowCutGap.CandidateCapacityWords

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor

def barrier (budget : Bits) : Bits := (increment true budget).1
def combined (budget : Bits) : Bits := barrier (barrier budget)

def word (budget : Bits) : Bool → Bool → Bits
  | false,false => []
  | true,false => [true]
  | false,true => barrier budget
  | true,true => combined budget

theorem value_word (budget : Bits) (unit hard : Bool) :
    value (word budget unit hard) = CandidateCapacityFlags.amount (value budget) (unit,hard) := by
  have one (xs : Bits) : value (barrier xs) = value xs+1 := (increment_spec true xs).1
  cases unit <;> cases hard <;> simp [word,combined,value,CandidateCapacityFlags.amount,one,Nat.add_comm]

private theorem barrier_normal {budget : Bits} (h : Normal budget) : Normal (barrier budget) := by
  induction h with
  | nil => exact .digit .nil (fun _ => rfl)
  | @digit b xs normal last ih =>
    cases b
    · exact .digit normal (fun _ => rfl)
    · apply Normal.digit ih
      intro empty
      have numeric : value (barrier xs)=value xs+1 := (increment_spec true xs).1
      rw [empty] at numeric
      simp [value] at numeric

theorem canonical {budget : Bits} (h : Normal budget) (unit hard : Bool) :
    word budget unit hard = (CandidateCapacityFlags.amount (value budget) (unit,hard)).bits := by
  rw [← value_word]
  apply Eq.symm
  apply normal_bits
  cases unit <;> cases hard
  · exact .nil
  · exact barrier_normal h
  · exact .digit .nil (fun _ => rfl)
  · exact barrier_normal (barrier_normal h)

def Stored (heap : NaturalHeap) (root : ℕ) (budget : Bits) : Prop :=
  ∃ small large nilWord one hard both,
    heap[root]? = some (.pair small large) ∧
    heap[small]? = some (.pair nilWord one) ∧ heap[large]? = some (.pair hard both) ∧
    BoolList heap nilWord [] ∧ BoolList heap one [true] ∧
    BoolList heap hard (barrier budget) ∧ BoolList heap both (combined budget)

theorem stored_extend {heap : NaturalHeap} {root : ℕ} {budget : Bits}
    (h : Stored heap root budget) (ext : NaturalHeap) : Stored (heap++ext) root budget := by
  obtain ⟨small,large,nilWord,one,hard,both,outer,lo,hi,w0,w1,wh,wb⟩ := h
  exact ⟨small,large,nilWord,one,hard,both,lookup_extend outer ext,lookup_extend lo ext,
    lookup_extend hi ext,boolList_extend w0 ext,boolList_extend w1 ext,
    boolList_extend wh ext,boolList_extend wb ext⟩

def incrementLabel (pc : Fin 16) : Fin 32 := ⟨16+pc.val,by omega⟩

def program : Program 32 := fun pc =>
  if h : pc.val<16 then
    match pc.val with
    | 0 => .make .r1 .nil 1
    | 1 => .make .r2 (.flag true) 2
    | 2 => .make .r2 (.pair .r2 .r1) 3
    | 3 => .make .r1 (.pair .r1 .r2) 4
    | 4 => .call (incrementLabel 15) 5 .r3
    | 5 => .move .r0 .r3 6
    | 6 => .call (incrementLabel 15) 7 .r3
    | 7 => .make .r2 (.pair .r0 .r3) 8
    | 8 => .make .r3 (.pair .r1 .r2) 9
    | _ => .halt
  else if pc.val=30 then .ret .r3
  else ReferenceProgramLabels.instruction incrementLabel
    (BinaryIncrementProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 32))
    (tape : Bits) (pc : Fin 32) : NaturalState 32 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def steps (budget : Bits) : ℕ :=
  BinaryIncrementProgram.steps budget+BinaryIncrementProgram.steps (barrier budget)+13

theorem steps_le (budget : Bits) : steps budget ≤ 16*budget.length+31 := by
  have h := BinaryIncrementProgram.steps_bound budget
  have k := BinaryIncrementProgram.steps_bound (barrier budget)
  have len := (increment_spec true budget).2.1
  simp only [steps,barrier] at *
  omega

private theorem inc_slots (pc : Fin 16) (h : BinaryIncrementProgram.program pc ≠ .halt) :
    program (incrementLabel pc) =
      ReferenceProgramLabels.instruction incrementLabel (BinaryIncrementProgram.program pc) := by
  by_cases hp : pc.val=14
  · have eq : pc=14 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,incrementLabel,show ¬16+pc.val<16 by omega,show 16+pc.val≠30 by omega]

private theorem join {s u v : NaturalState 32} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem inc_call {heap : NaturalHeap} {r : Registers ℕ} {word : Bits}
    (input : BoolList heap r.a word) (tape : Bits) (pc next : Fin 32)
    (inst : program pc=.call (incrementLabel 15) next .r3) :
    ∃ ext root,BoolList (heap++ext) root (barrier word) ∧
      NaturalRun program (BinaryIncrementProgram.steps word+3) (state heap r [] tape pc) []
        (state (heap++ext) (r.set .r3 root) [] tape next) := by
  obtain ⟨ext,root,len,run,rep⟩ := BinaryIncrementProgram.increment_return input heap.length
    r.b r.c r.d rfl r 14 [] tape
  have oldCall : tickNatural BinaryIncrementProgram.program
      (BinaryIncrementProgram.state heap heap.length r.a r.b r.c r.d [] tape 15)=
      some ⟨BinaryIncrementProgram.state heap heap.length r.a r.b r.c r.d [⟨14,.r3,r⟩] tape 0,[],0⟩ := by
    cases r
    rfl
  have body := NaturalRun.step oldCall run
  let frame : Frame ℕ 32 := ⟨next,.r3,r⟩
  let stop := state (heap++ext) (r.set .r3 root) [frame] tape (incrementLabel 14)
  have start : tickNatural program (state heap r [] tape pc)=
      some ⟨state heap r [frame] tape (incrementLabel 15),[],0⟩ := by
    simp [state,frame,tickNatural,inst]
  have lift := ReferenceProgramLabels.run incrementLabel BinaryIncrementProgram.program program inc_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have trace : NaturalRun program (BinaryIncrementProgram.steps word+1)
      (state heap r [frame] tape (incrementLabel 15)) [] stop := by
    cases r
    simpa [stop,state,BinaryIncrementProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state,Registers.set,len] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape next,[],0⟩ := by
    simp [stop,state,frame,program,incrementLabel,tickNatural,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have whole := NaturalRun.step start (join trace (.step ret (.done _)))
  exact whole

theorem natural_make {heap : NaturalHeap} {r : Registers ℕ} {budget : Bits}
    (input : BoolList heap r.a budget) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Stored (heap++ext) root budget ∧
      NaturalRun program (steps budget) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 9) := by
  let i := heap.length
  let pre : NaturalHeap := [.nil,.flag true,.pair (i+1) i,.pair i (i+2)]
  let staged := heap++pre
  let args := (r.set .r1 (i+3)).set .r2 (i+2)
  have prep : NaturalRun program 4 (state heap r [] tape 0) [] (state staged args [] tape 4) := by
    have p0 : tickNatural program (state heap r [] tape 0) =
        some ⟨state (heap++[.nil]) (r.set .r1 i) [] tape 1,[],0⟩ := by
      simp [state,program,tickNatural,allocateNatural,Recipe.cell,i]
    have p1 : tickNatural program (state (heap++[.nil]) (r.set .r1 i) [] tape 1) =
        some ⟨state (heap++[.nil,.flag true]) ((r.set .r1 i).set .r2 (i+1)) [] tape 2,[],0⟩ := by
      simp [state,program,tickNatural,allocateNatural,Recipe.cell,List.append_assoc,i]
    have p2 : tickNatural program (state (heap++[.nil,.flag true]) ((r.set .r1 i).set .r2 (i+1)) [] tape 2) =
        some ⟨state (heap++[.nil,.flag true,.pair (i+1) i]) ((r.set .r1 i).set .r2 (i+2)) [] tape 3,[],0⟩ := by
      simp [state,program,tickNatural,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc,i]
    have p3 : tickNatural program
        (state (heap++[.nil,.flag true,.pair (i+1) i]) ((r.set .r1 i).set .r2 (i+2)) [] tape 3) =
        some ⟨state staged args [] tape 4,[],0⟩ := by
      simp [state,program,tickNatural,allocateNatural,Recipe.cell,Registers.get,Registers.set,
        staged,args,pre,List.append_assoc,i]
    exact .step p0 (.step p1 (.step p2 (.step p3 (.done _))))
  obtain ⟨e1,hard,hrep,htrace⟩ := inc_call (r:=args) (boolList_extend input pre) tape 4 5 rfl
  let withHard := args.set .r3 hard
  let right := withHard.set .r0 hard
  have move : tickNatural program (state (staged++e1) withHard [] tape 5)=
      some ⟨state (staged++e1) right [] tape 6,[],0⟩ := rfl
  obtain ⟨e2,both,brep,btrace⟩ := inc_call (r:=right) hrep tape 6 7 rfl
  let large := (staged++e1++e2).length
  let suf : NaturalHeap := [.pair hard both,.pair (i+3) large]
  let last := (right.set .r3 both).set .r2 large
  have lo : tickNatural program (state (staged++e1++e2) (right.set .r3 both) [] tape 7)=
      some ⟨state (staged++e1++e2++[.pair hard both]) last [] tape 8,[],0⟩ := by
    simp [state,program,tickNatural,allocateNatural,Recipe.cell,Registers.get,Registers.set,last,large,right]
    exact ⟨by omega,by omega⟩
  have hi : tickNatural program (state (staged++e1++e2++[.pair hard both]) last [] tape 8)=
      some ⟨state (staged++e1++e2++suf) (last.set .r3 (large+1)) [] tape 9,[],0⟩ := by
    simp [state,program,tickNatural,allocateNatural,Recipe.cell,Registers.get,Registers.set,last,large,
      right,withHard,args,suf,List.append_assoc,Nat.add_assoc]
  have base0 : staged[i]?=some (.nil : Cell ℕ) := by simp [staged,pre,i]
  have flag : staged[i+1]?=some (.flag true) := by
    rw [show staged=heap++pre from rfl,List.getElem?_append_right (by simp [i])]
    simp [pre,i]
  have base1 : staged[i+2]?=some (.pair (i+1) i) := by
    rw [show staged=heap++pre from rfl,List.getElem?_append_right (by simp [i])]
    simp [pre,i]
  have small : staged[i+3]?=some (.pair i (i+2)) := by
    rw [show staged=heap++pre from rfl,List.getElem?_append_right (by simp [i])]
    simp [pre,i]
  have hlarge : (staged++e1++e2++suf)[large]?=some (.pair hard both) := by
    rw [List.getElem?_append_right (show (staged++e1++e2).length ≤ large from le_rfl)]
    rw [show large-(staged++e1++e2).length=0 from Nat.sub_self _]
    rfl
  have outer : (staged++e1++e2++suf)[large+1]?=some (.pair (i+3) large) := by
    rw [List.getElem?_append_right (show (staged++e1++e2).length ≤ large+1 from Nat.le_succ _)]
    rw [show large+1-(staged++e1++e2).length=1 by change large+1-large=1; omega]
    rfl
  have w1 : BoolList staged (i+2) [true] := .cons base1 flag (.nil base0)
  have rep : Stored (staged++e1++e2++suf) (large+1) budget :=
    ⟨i+3,large,i,i+2,hard,both,outer,lookup_extend (lookup_extend (lookup_extend small e1) e2) suf,
      hlarge,boolList_extend (boolList_extend (boolList_extend (.nil base0) e1) e2) suf,
      boolList_extend (boolList_extend (boolList_extend w1 e1) e2) suf,
      boolList_extend (boolList_extend hrep e2) suf,boolList_extend brep suf⟩
  refine ⟨pre++e1++e2++suf,last,large+1,?_,?_⟩
  · simpa only [staged,List.append_assoc] using rep
  · have whole := join prep (join htrace (.step move (join btrace (.step lo (.step hi (.done _))))))
    unfold steps
    convert whole using 1 <;> first | rfl | omega | simp only [staged,List.append_assoc]

def select : Program 8 := fun pc => match pc.val with
  | 0 => .branch .r2 7 1 2 7
  | 1 => .field .r0 .r0 false 3
  | 2 => .field .r0 .r0 true 3
  | 3 => .branch .r1 7 4 5 7
  | 4 => .field .r3 .r0 false 6
  | 5 => .field .r3 .r0 true 6
  | _ => .halt

theorem natural_select {heap : NaturalHeap} {r : Registers ℕ} {budget : Bits} {unit hard : Bool}
    (table : Stored heap r.a budget) (u : heap[r.b]?=some (.flag unit)) (h : heap[r.c]?=some (.flag hard))
    (tape : Bits) :
    ∃ (args : Registers ℕ) (root : ℕ),BoolList heap root (word budget unit hard) ∧
      NaturalRun select 4 ⟨heap,heap.length,r,[],0,tape⟩ []
        ⟨heap,heap.length,args.set .r3 root,[],6,tape⟩ := by
  obtain ⟨small,large,nilWord,one,hi,both,outer,lo,high,w0,w1,wh,wb⟩ := table
  let branch := if hard then large else small
  let root := if hard then (if unit then both else hi) else (if unit then one else nilWord)
  refine ⟨r.set .r0 branch,root,?_,?_⟩
  · cases hard <;> cases unit <;> assumption
  · apply ReferenceProgramSteps.sound
    cases hard <;> cases unit <;>
      simp [ReferenceProgramSteps.run,branch,root,tickNatural,select,Registers.get,Registers.set,tagBranch, *]

end DirectedFlowCutGap.CandidateCapacityWords
