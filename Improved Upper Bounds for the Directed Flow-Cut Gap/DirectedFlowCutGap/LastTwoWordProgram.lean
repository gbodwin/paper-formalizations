import DirectedFlowCutGap.WordPairProductProgram

/-! Read the last two existing word addresses from a stored list of length at least two. -/

namespace DirectedFlowCutGap.LastTwoWordProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open PathCostMaterialization (WordList)
open GraphWalkExtension (Edge)
open ConcreteExpressionProgram (append_run)
open BinaryLabelRangeProgram (wordsFrom)

def program : Program 16 := fun pc => match pc.val with
  | 0 => .field .r1 .r0 false 1
  | 1 => .field .r0 .r0 true 2
  | 2 => .field .r2 .r0 false 3
  | 3 => .field .r0 .r0 true 4
  | 4 => .branch .r0 8 15 15 5
  | 5 => .move .r1 .r2 6
  | 6 => .field .r2 .r0 false 7
  | 7 => .field .r0 .r0 true 4
  | 8 => .make .r3 (.pair .r1 .r2) 9
  | _ => .halt

def state (heap : NaturalHeap) (r : Registers ℕ) (tape : Bits) (pc : Fin 16) : NaturalState 16 :=
  ⟨heap,heap.length,r,[],pc,tape⟩

def lastFrom (previous current : Bits) : List Bits → Bits×Bits
  | [] => (previous,current)
  | next::rest => lastFrom current next rest

theorem lastFrom_range (j count : ℕ) : lastFrom j.bits (j+1).bits (wordsFrom (j+2) count)=
    ((j+count).bits,(j+count+1).bits) := by
  induction count generalizing j with
  | zero => simp [wordsFrom,lastFrom]
  | succ k ih =>
    have following := ih (j+1)
    rw [show j+1+2=j+2+1 by omega,show j+1+k=j+(k+1) by omega] at following
    simpa only [wordsFrom,lastFrom] using following

def steps (tailLength : ℕ) : ℕ := 4*tailLength+6

private theorem scan {heap : NaturalHeap} {r : Registers ℕ} {previous current : Bits} {rest : List Bits}
    (tail : WordList heap r.a rest) (prev : BoolList heap r.b previous) (last : BoolList heap r.c current)
    (tape : Bits) :
    ∃ args : Registers ℕ,BoolList heap args.b (lastFrom previous current rest).1 ∧
      BoolList heap args.c (lastFrom previous current rest).2 ∧
      NaturalRun program (4*rest.length+1) (state heap r tape 4) [] (state heap args tape 8) := by
  induction rest generalizing r previous current with
  | nil =>
    cases tail with
    | nil hp =>
      have stop : tickNatural program (state heap r tape 4)=some ⟨state heap r tape 8,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      exact ⟨r,prev,last,.step stop (.done _)⟩
  | cons x xs ih =>
    cases tail with
    | @cons _ addr next _ _ hp hx hs =>
      let args := ((r.set .r1 r.c).set .r2 addr).set .r0 next
      have setup : NaturalRun program 4 (state heap r tape 4) [] (state heap args tape 4) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,args,hp]
      obtain ⟨out,hprev,hlast,body⟩ := ih (r:=args) hs last hx
      refine ⟨out,hprev,hlast,?_⟩
      have run := append_run setup body
      have count : 4+(4*xs.length+1)=4*(x::xs).length+1 := by simp [Nat.mul_add]; omega
      rw [← count]
      exact run

theorem natural_last {heap : NaturalHeap} {r : Registers ℕ} {p q : Bits} {tail : List Bits}
    (input : WordList heap r.a (p::q::tail)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Edge (heap++ext) root (lastFrom p q tail) ∧
      NaturalRun program (steps tail.length) (state heap r tape 0) [] (state (heap++ext) (args.set .r3 root) tape 9) := by
  cases input with
  | @cons _ first afterFirst _ _ hp pf htail =>
    cases htail with
    | @cons _ second remaining _ _ hq qf rest =>
      let args := ((r.set .r1 first).set .r2 second).set .r0 remaining
      have setup : NaturalRun program 4 (state heap r tape 0) [] (state heap args tape 4) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,hp,hq]
      obtain ⟨regs,prev,last,body⟩ := scan (r:=args) rest pf qf tape
      let node : Cell ℕ := .pair regs.b regs.c
      let root := heap.length
      have make : tickNatural program (state heap regs tape 8)=
          some ⟨state (heap++[node]) (regs.set .r3 root) tape 9,[],0⟩ := by
        simp [state,program,tickNatural,allocateNatural,Recipe.cell,node,root,Registers.get]
      refine ⟨[node],regs,root,⟨regs.b,regs.c,by simp [root,node],boolList_extend prev _,boolList_extend last _⟩,?_⟩
      have full := append_run setup (append_run body (.step make (.done _)))
      have count : 4+(4*tail.length+1+1)=steps tail.length := by unfold steps; omega
      rw [← count]
      exact full

theorem natural_last_range {heap : NaturalHeap} {r : Registers ℕ} {m : ℕ} (room : 2≤m)
    (input : WordList heap r.a (wordsFrom 0 m)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Edge (heap++ext) root ((m-2).bits,(m-1).bits) ∧
      NaturalRun program (steps (m-2)) (state heap r tape 0) [] (state (heap++ext) (args.set .r3 root) tape 9) := by
  have head : wordsFrom 0 m=(0 : ℕ).bits::(1 : ℕ).bits::wordsFrom 2 (m-2) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le room
    rw [show 2+k=(k+1)+1 by omega]
    simp [wordsFrom]
  rw [head] at input
  obtain ⟨ext,args,root,pair,run⟩ := natural_last input tape
  have numeric := lastFrom_range 0 (m-2)
  simp only [Nat.zero_add] at numeric
  have eq : m-2+1=m-1 := by omega
  rw [eq] at numeric
  refine ⟨ext,args,root,?_,?_⟩
  · simpa only [numeric] using pair
  · simpa only [BinaryLabelRangeProgram.words_length] using run

end DirectedFlowCutGap.LastTwoWordProgram
