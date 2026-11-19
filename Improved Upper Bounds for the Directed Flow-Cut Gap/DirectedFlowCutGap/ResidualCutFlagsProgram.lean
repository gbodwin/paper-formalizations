import DirectedFlowCutGap.ActualSupportSearch

/-!
# Reading the complement of a retained sink search

The program tests each vertex label against the stored search codes.
It writes a true flag exactly when lookup returns no entry for that
label, keeping the vertex order and the input tape.
-/

namespace DirectedFlowCutGap.ResidualCutFlagsProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor GraphWalkExtension
open GraphDiscoveryProgram (Vertices vertices_extend)
open SupportRecoveryProgram (Code Codes StoredOption lookup lookupSteps codes_extend)

def lookupLabel (pc : Fin 280) : Fin 304 := if pc.val=279 then 15 else ⟨24+pc.val,by omega⟩

def program : Program 304 := fun pc =>
  if pc.val<24 then
    match pc.val with
    | 0 => .branch .r0 1 23 23 4
    | 1 => .make .r3 .nil 2
    | 2 => .ret .r3
    | 4 => .field .r2 .r0 false 5
    | 5 => .field .r0 .r0 true 6
    | 6 => .call 0 7 .r0
    | 7 => .call 12 8 .r3
    | 8 => .make .r3 (.pair .r3 .r0) 2
    | 12 => .move .r0 .r1 13
    | 13 => .move .r1 .r2 14
    | 14 => .call (lookupLabel 150) 15 .r3
    | 15 => .branch .r3 16 23 23 17
    | 16 => .make .r3 (.flag true) 18
    | 17 => .make .r3 (.flag false) 18
    | 18 => .ret .r3
    | 22 => .call 0 23 .r3
    | _ => .halt
  else ReferenceProgramLabels.instruction lookupLabel
    (SupportRecoveryProgram.program ⟨pc.val-24,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 304))
    (tape : Bits) (pc : Fin 304) : NaturalState 304 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def mark (codes : List Code) (u : Bits) : Bool := (lookup u codes).isNone

def steps (codes : List Code) : List Bits → ℕ
  | [] => 3
  | u::us => steps codes us+lookupSteps u codes+13

private theorem lookup_slots (pc : Fin 280) (h : SupportRecoveryProgram.program pc≠.halt) :
    program (lookupLabel pc) =
      ReferenceProgramLabels.instruction lookupLabel (SupportRecoveryProgram.program pc) := by
  by_cases hp : pc.val=279
  · have eq : pc=279 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,lookupLabel,hp,show ¬24+pc.val<24 by omega]

private theorem join {s u v : NaturalState 304} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem mark_return {heap : NaturalHeap} {r : Registers ℕ} {cs : List Code} {u : Bits}
    (table : Codes heap r.b cs) (word : BoolList heap r.c u)
    (caller : Frame ℕ 304) (stack : List (Frame ℕ 304)) (tape : Bits) :
    ∃ ext root,(heap++ext)[root]?=some (.flag (mark cs u)) ∧
      NaturalRun program (lookupSteps u cs+6) (state heap r (caller::stack) tape 12) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let saved := caller::stack
  let first := r.set .r0 r.b
  let args := first.set .r1 r.c
  let frame : Frame ℕ 304 := ⟨15,.r3,args⟩
  have t0 : tickNatural program (state heap r saved tape 12)=some ⟨state heap first saved tape 13,[],0⟩ := rfl
  have t1 : tickNatural program (state heap first saved tape 13)=some ⟨state heap args saved tape 14,[],0⟩ := rfl
  have call : tickNatural program (state heap args saved tape 14)=
      some ⟨state heap args (frame::saved) tape (lookupLabel 150),[],0⟩ := rfl
  have tab : Codes heap args.a cs := table
  have key : BoolList heap args.b u := word
  obtain ⟨ext,root,_,body,rep⟩ := SupportRecoveryProgram.lookup_return tab key heap.length
    args.c args.d rfl args 279 [] tape
  let mid := heap++ext
  let ready := args.set .r3 root
  have lift := ReferenceProgramLabels.run lookupLabel SupportRecoveryProgram.program program lookup_slots body
  have lift := ReferenceProgramStack.run program saved lift
  have trace : NaturalRun program (lookupSteps u cs) (state heap args (frame::saved) tape (lookupLabel 150)) []
      (state mid ready saved tape 15) := by
    simpa [mid,ready,frame,state,SupportRecoveryProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,lookupLabel,Registers.set] using lift
  let branchTo : Fin 304 := if mark cs u then 16 else 17
  have branch : tickNatural program (state mid ready saved tape 15)=
      some ⟨state mid ready saved tape branchTo,[],0⟩ := by
    cases seen : lookup u cs with
    | none =>
      rw [seen] at rep
      change mid[ready.d]?=some .nil at rep
      simp [branchTo,mark,seen,state,program,tickNatural,Registers.get,tagBranch,rep]
    | some x =>
      rw [seen] at rep
      obtain ⟨v,path,hp,_,_⟩ := rep
      have pair : mid[ready.d]?=some (.pair v path) := hp
      simp [branchTo,mark,seen,state,program,tickNatural,Registers.get,tagBranch,pair]
  let cell : Cell ℕ := .flag (mark cs u)
  let finish := mid++[cell]
  let fresh := mid.length
  let before := state finish (ready.set .r3 fresh) saved tape 18
  have alloc : tickNatural program (state mid ready saved tape branchTo)=some ⟨before,[],0⟩ := by
    cases bit : mark cs u <;>
      simp [bit,branchTo,cell,finish,fresh,before,state,program,tickNatural,allocateNatural,Recipe.cell]
  have ret : tickNatural program before=some ⟨state finish (caller.saved.set caller.destination fresh)
      stack tape caller.continuation,[],0⟩ := by
    simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
  have hflag : finish[fresh]?=some (.flag (mark cs u)) := by simp [finish,fresh,cell]
  refine ⟨ext++[cell],fresh,?_,?_⟩
  · simpa only [finish,mid,List.append_assoc] using hflag
  · have run := NaturalRun.step t0 (.step t1 (.step call (join trace
      (.step branch (.step alloc (.step ret (.done _)))))))
    convert run using 1 <;> first | rfl | omega | simp only [finish,mid,List.append_assoc]

theorem flags_return {heap : NaturalHeap} {r : Registers ℕ} {cs : List Code} {vs : List Bits}
    (input : Vertices heap r.a vs) (table : Codes heap r.b cs)
    (caller : Frame ℕ 304) (stack : List (Frame ℕ 304)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (vs.map (mark cs)) ∧
      NaturalRun program (steps cs vs) (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction vs generalizing heap r caller stack with
  | nil =>
    cases input with
    | nil hp =>
      let saved := caller::stack
      let ext : NaturalHeap := [.nil]
      let fresh := heap.length
      let before := state (heap++ext) (r.set .r3 fresh) saved tape 2
      have branch : tickNatural program (state heap r saved tape 0)=some ⟨state heap r saved tape 1,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      have alloc : tickNatural program (state heap r saved tape 1)=some ⟨before,[],0⟩ := by
        simp [ext,fresh,before,state,program,tickNatural,allocateNatural,Recipe.cell]
      have ret : tickNatural program before=some ⟨state (heap++ext)
          (caller.saved.set caller.destination fresh) stack tape caller.continuation,[],0⟩ := by
        simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
      exact ⟨ext,fresh,.nil (by simp [ext,fresh]),.step branch (.step alloc (.step ret (.done _)))⟩
  | cons u vs ih =>
    cases input with
    | @cons _ word tail _ _ hp hw ht =>
      let saved := caller::stack
      let first := r.set .r2 word
      let args := first.set .r0 tail
      let tailFrame : Frame ℕ 304 := ⟨7,.r0,args⟩
      have branch : tickNatural program (state heap r saved tape 0)=
          some ⟨state heap r saved tape 4,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      have readHead : tickNatural program (state heap r saved tape 4)=
          some ⟨state heap first saved tape 5,[],0⟩ := by
        simp [first,state,program,tickNatural,Registers.get,hp]
      have readTail : tickNatural program (state heap first saved tape 5)=
          some ⟨state heap args saved tape 6,[],0⟩ := by
        simp [args,first,state,program,tickNatural,Registers.get,Registers.set,hp]
      have callTail : tickNatural program (state heap args saved tape 6)=
          some ⟨state heap args (tailFrame::saved) tape 0,[],0⟩ := rfl
      obtain ⟨et,rest,hrest,tailRun⟩ := ih (r:=args) ht table tailFrame saved
      let mid := heap++et
      let returned := args.set .r0 rest
      let headFrame : Frame ℕ 304 := ⟨8,.r3,returned⟩
      have callHead : tickNatural program (state mid returned saved tape 7)=
          some ⟨state mid returned (headFrame::saved) tape 12,[],0⟩ := rfl
      obtain ⟨eh,head,hhead,headRun⟩ := mark_return (r:=returned)
        (codes_extend table et) (boolList_extend hw et) headFrame saved tape
      let grown := mid++eh
      let fresh := grown.length
      let pair : Cell ℕ := .pair head rest
      let out := grown++[pair]
      let afterHead := returned.set .r3 head
      let before := state out (afterHead.set .r3 fresh) saved tape 2
      have alloc : tickNatural program (state grown afterHead saved tape 8)=some ⟨before,[],0⟩ := by
        simp [before,out,fresh,pair,afterHead,returned,state,program,tickNatural,Registers.get,
          Registers.set,allocateNatural,Recipe.cell]
      have ret : tickNatural program before=some ⟨state out (caller.saved.set caller.destination fresh)
          stack tape caller.continuation,[],0⟩ := by
        simp [before,afterHead,saved,state,program,tickNatural,Registers.get,Registers.set]
      have result : BoolList out fresh ((u::vs).map (mark cs)) :=
        .cons (by simp [out,fresh,pair]) (lookup_extend hhead [pair])
          (boolList_extend (boolList_extend hrest eh) [pair])
      refine ⟨et++eh++[pair],fresh,?_,?_⟩
      · simpa only [out,grown,mid,List.append_assoc] using result
      · have finish := NaturalRun.step callHead (join headRun (.step alloc (.step ret (.done _))))
        have trace := NaturalRun.step branch (.step readHead (.step readTail (.step callTail (join tailRun finish))))
        simp only [steps]
        convert trace using 1 <;> first | rfl | omega | simp only [out,grown,mid,List.append_assoc]

theorem natural_flags {heap : NaturalHeap} {r : Registers ℕ} {cs : List Code} {vs : List Bits}
    (input : Vertices heap r.a vs) (table : Codes heap r.b cs) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (vs.map (mark cs)) ∧
      NaturalRun program (steps cs vs+1) (state heap r [] tape 22) []
        (state (heap++ext) (r.set .r3 root) [] tape 23) := by
  let frame : Frame ℕ 304 := ⟨23,.r3,r⟩
  obtain ⟨ext,root,hrep,hrun⟩ := flags_return input table frame [] tape
  have call : tickNatural program (state heap r [] tape 22)=some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,hrep,.step call hrun⟩

def instructionBound (m q W : ℕ) : ℕ := m*(q*(32*W+27)+16)+4

theorem steps_le (cs : List Code) (vs : List Bits) (W : ℕ) (width : ∀ u ∈ vs,u.length≤W)
    (codes : ∀ x ∈ cs,x.1.length≤W) :
    steps cs vs+1 ≤ instructionBound vs.length cs.length W := by
  induction vs with
  | nil => simp [steps,instructionBound]
  | cons u vs ih =>
    have first := SupportRecoveryProgram.lookup_steps_le W u cs (width u List.mem_cons_self) codes
    have later := ih (fun v hv => width v (List.mem_cons_of_mem _ hv))
    simp only [steps,instructionBound,List.length_cons,Nat.add_mul,Nat.one_mul] at later ⊢
    omega

end DirectedFlowCutGap.ResidualCutFlagsProgram
