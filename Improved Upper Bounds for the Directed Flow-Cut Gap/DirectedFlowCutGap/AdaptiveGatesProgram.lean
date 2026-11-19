import DirectedFlowCutGap.BinaryProductOrderProgram
import DirectedFlowCutGap.IntegerAdaptiveExecution

/-! Compute the retained controller's ready and active flags from stored mass words. -/

namespace DirectedFlowCutGap.AdaptiveGatesProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)

def zeroLabel (pc : Fin 9) : Fin 237 := ⟨48+pc.val,by omega⟩
def productLabel (pc : Fin 180) : Fin 237 := ⟨57+pc.val,by omega⟩

def program : Program 237 := fun pc =>
  if pc.val<48 then
    match pc.val with
    | 0 => .call 16 1 .r3
    | 1 => .branch .r3 47 3 20 47
    | 3 => .call 24 4 .r3
    | 4 => .branch .r3 47 12 5 47
    | 5 => .call 32 6 .r1
    | 6 => .make .r3 (.pair .r3 .r1) 7
    | 12 => .make .r3 (.pair .r3 .r3) 7
    | 16 => .move .r0 .r1 17
    | 17 => .call (zeroLabel 7) 18 .r3
    | 18 => .ret .r3
    | 20 => .make .r0 (.flag false) 21
    | 21 => .make .r3 (.pair .r3 .r0) 7
    | 24 => .field .r2 .r2 false 25
    | 25 => .call (productLabel 0) 26 .r3
    | 26 => .ret .r3
    | 32 => .move .r1 .r0 33
    | 33 => .field .r0 .r2 true 34
    | 34 => .field .r2 .r2 false 35
    | 35 => .call (productLabel 0) 36 .r3
    | 36 => .ret .r3
    | _ => .halt
  else if h : pc.val<57 then
    if pc.val=56 then .ret .r3
    else ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program ⟨pc.val-48,by omega⟩)
  else if pc.val=59 then .ret .r3
  else ReferenceProgramLabels.instruction productLabel
    (BinaryProductOrderProgram.program ⟨pc.val-57,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 237

def Parameters (heap : NaturalHeap) (root : ℕ) (ratio threshold : Bits) : Prop :=
  ∃ R M,heap[root]?=some (.pair R M) ∧ BoolList heap R ratio ∧ BoolList heap M threshold

theorem parameters_extend {heap : NaturalHeap} {root : ℕ} {ratio threshold : Bits}
    (h : Parameters heap root ratio threshold) (ext : NaturalHeap) : Parameters (heap++ext) root ratio threshold := by
  obtain ⟨R,M,ptr,r,m⟩ := h
  exact ⟨R,M,lookup_extend ptr ext,boolList_extend r ext,boolList_extend m ext⟩

def ready (current optimal R : Bits) : Bool := FlexibleGridProvider.readyCode (value R) (value current) (value optimal)

def active (current optimal R M : Bits) : Bool := ready current optimal R && !(value optimal == 0) &&
  Nat.ble (value M) (value R*value current)

def Output (heap : NaturalHeap) (root : ℕ) (current optimal R M : Bits) : Prop :=
  ∃ r a,heap[root]?=some (.pair r a) ∧ heap[r]?=some (.flag (ready current optimal R)) ∧
    heap[a]?=some (.flag (active current optimal R M))

def instructionBound (current optimal R M : ℕ) : ℕ :=
  4*optimal+BinaryProductOrderProgram.instructionBound current optimal R+
    BinaryProductOrderProgram.instructionBound M current R+24

private theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  by_cases stop : pc.val=8
  · have eq : pc=8 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,zeroLabel,show ¬48+pc.val<48 by omega,show 48+pc.val<57 by omega,show 48+pc.val≠56 by omega]

private theorem product_slots (pc : Fin 180) (h : BinaryProductOrderProgram.program pc≠.halt) :
    program (productLabel pc)=ReferenceProgramLabels.instruction productLabel (BinaryProductOrderProgram.program pc) := by
  by_cases stop : pc.val=2
  · have eq : pc=2 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,productLabel,show ¬57+pc.val<48 by omega,show ¬57+pc.val<57 by omega,show 57+pc.val≠59 by omega]

private theorem zero_call {heap : NaturalHeap} {r : Registers ℕ} {optimal : Bits}
    (opt : BoolList heap r.b optimal) (tape : Bits) :
    let ext : NaturalHeap := [.flag (isZero optimal).1]
    NaturalRun program (BinaryZeroProgram.steps optimal+6) (state heap r [] tape 0) []
      (state (heap++ext) (r.set .r3 heap.length) [] tape 1) := by
  let frame : Frame ℕ 237 := ⟨1,.r3,r⟩
  let args := r.set .r0 r.b
  have enter : NaturalRun program 2 (state heap r [] tape 0) [] (state heap args [frame] tape 17) := by
    apply ReferenceProgramSteps.sound
    cases r
    rfl
  let i : NaturalState 9 := ReferenceProgramInvocation.state heap args [] tape 7
  obtain ⟨out,run,heapEq,next,aa,bb,cc,dd,quiet,suffix,pc,_,_⟩ := BinaryZeroProgram.zero_high i rfl rfl opt rfl
  let ext : NaturalHeap := [.flag (isZero optimal).1]
  have eq : out=ReferenceProgramInvocation.state (heap++ext) (args.set .r3 heap.length) [] tape 8 := by
    cases out with
    | mk h n regs stack p t =>
      cases regs
      cases r
      simp_all [i,ReferenceProgramInvocation.state,args,Registers.set,ext]
  rw [eq] at run
  have invoke := ReferenceProgramInvocation.call zeroLabel zero_slots (caller:=17) (continuation:=18)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [frame] run
  let done := state (heap++ext) (args.set .r3 heap.length) [frame] tape 18
  have work : NaturalRun program (1+BinaryZeroProgram.steps optimal+2) (state heap args [frame] tape 17) [] done := by
    simpa only [done,i,Registers.get,Registers.set] using invoke
  have ret : tickNatural program done=some ⟨state (heap++ext) (r.set .r3 heap.length) [] tape 1,[],0⟩ := by
    simp [done,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  dsimp only
  have count : 2+(1+BinaryZeroProgram.steps optimal+2+1)=BinaryZeroProgram.steps optimal+6 := by omega
  rw [← count]
  exact append_run enter (append_run work (.step ret (.done _)))

private theorem comparison_call {heap : NaturalHeap} {r : Registers ℕ} {current optimal R M : Bits}
    (threshold : Bool) (currentRep : BoolList heap r.a current) (optimalRep : BoolList heap r.b optimal)
    (params : Parameters heap r.c R M) (tape : Bits) :
    let x := if threshold then M else current
    let y := if threshold then current else optimal
    let start : Fin 237 := if threshold then 5 else 3
    let exit : Fin 237 := if threshold then 6 else 4
    let destination : Reg := if threshold then .r1 else .r3
    ∃ ext root,(heap++ext)[root]?=some (.flag (Nat.ble (value x) (value R*value y))) ∧
      NaturalRun program (BinaryProductOrderProgram.steps x y R+(if threshold then 7 else 5))
        (state heap r [] tape start) [] (state (heap++ext) (r.set destination root) [] tape exit) := by
  obtain ⟨ratio,cutoff,atParams,ratioRep,cutoffRep⟩ := params
  let x := if threshold then M else current
  let y := if threshold then current else optimal
  let start : Fin 237 := if threshold then 5 else 3
  let exit : Fin 237 := if threshold then 6 else 4
  let destination : Reg := if threshold then .r1 else .r3
  let frame : Frame ℕ 237 := ⟨exit,destination,r⟩
  let callSite : Fin 237 := if threshold then 35 else 25
  let retSite : Fin 237 := if threshold then 36 else 26
  let args : Registers ℕ := if threshold then ⟨cutoff,r.a,ratio,r.d⟩ else r.set .r2 ratio
  have prep : NaturalRun program (if threshold then 4 else 2) (state heap r [] tape start) []
      (state heap args [frame] tape callSite) := by
    cases threshold <;> apply ReferenceProgramSteps.sound <;>
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        atParams,start,exit,destination,frame,args,callSite]
  have left : BoolList heap args.a x := by cases threshold <;> assumption
  have right : BoolList heap args.b y := by cases threshold <;> assumption
  have factor : BoolList heap args.c R := by cases threshold <;> exact ratioRep
  obtain ⟨ext,out,root,rep,body⟩ := BinaryProductOrderProgram.natural_order left right factor tape
  have link : program callSite=.call (productLabel 0) retSite .r3 := by cases threshold <;> rfl
  have invoke := ReferenceProgramInvocation.call productLabel product_slots (dst:=.r3) (result:=.r3) link (by rfl) [frame] body
  let done := state (heap++ext) (args.set .r3 root) [frame] tape retSite
  have work : NaturalRun program (BinaryProductOrderProgram.steps x y R+2) (state heap args [frame] tape callSite) [] done := by
    simpa only [Registers.get,Registers.set,done] using invoke
  have ret : tickNatural program done=some ⟨state (heap++ext) (r.set destination root) [] tape exit,[],0⟩ := by
    cases threshold <;> simp [done,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      retSite,frame,exit,destination,args]
  refine ⟨ext,root,rep,?_⟩
  let k := BinaryProductOrderProgram.steps x y R
  have count : (if threshold then 4 else 2)+(k+2+1)=k+(if threshold then 7 else 5) := by cases threshold <;> simp <;> omega
  change NaturalRun program (k+(if threshold then 7 else 5)) _ [] _
  rw [← count]
  exact append_run prep (append_run work (.step ret (.done _)))

set_option maxHeartbeats 2100000 in
theorem natural_gates {heap : NaturalHeap} {r : Registers ℕ} {c o R M : Bits}
    (current : BoolList heap r.a c) (optimal : BoolList heap r.b o) (params : Parameters heap r.c R M) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),Output (heap++ext) root c o R M ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 7) ∧
      k ≤ instructionBound c.length o.length R.length M.length := by
  let ez : NaturalHeap := [.flag (isZero o).1]
  let mid := heap++ez
  let args := r.set .r3 heap.length
  have start := zero_call optimal tape
  have zeroFlag : mid[heap.length]?=some (.flag (isZero o).1) := by simp [mid,ez]
  have zeroBound := BinaryZeroProgram.steps_bound o
  have readyBound := BinaryProductOrderProgram.steps_le c o R
  have activeBound := BinaryProductOrderProgram.steps_le M c R
  cases zero : (isZero o).1 with
  | true =>
    rw [zero] at zeroFlag
    have iszero : value o=0 := (isZero_spec o).1.mp zero
    let root := mid.length+1
    let inactive := mid.length
    let extra : NaturalHeap := [.flag false,.pair heap.length inactive]
    let outArgs := args.set .r0 inactive
    have tail : NaturalRun program 3 (state mid args [] tape 1) []
        (state (mid++extra) (outArgs.set .r3 root) [] tape 7) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        tagBranch,allocateNatural,Recipe.cell,zeroFlag,args,outArgs,extra,inactive,root]
    have terminated : Output (mid++extra) root c o R M :=
      ⟨heap.length,inactive,by simp [root,extra,inactive],
        by simpa [ready,FlexibleGridProvider.readyCode,iszero] using lookup_extend zeroFlag extra,
        by simp [active,iszero,extra,inactive]⟩
    refine ⟨ez++extra,outArgs,root,BinaryZeroProgram.steps o+6+3,?_,?_,?_⟩
    · simpa only [mid,List.append_assoc] using terminated
    · simpa only [mid,ez,args,List.append_assoc,List.nil_append] using append_run start tail
    · unfold instructionBound; omega
  | false =>
    rw [zero] at zeroFlag
    have nonzero : value o≠0 := by
      intro h
      have z := (isZero_spec o).1.mpr h
      rw [zero] at z
      contradiction
    have branch : tickNatural program (state mid args [] tape 1)=some ⟨state mid args [] tape 3,[],0⟩ := by
      simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,tagBranch,args,zeroFlag]
    obtain ⟨er,rr,test,check⟩ := comparison_call (r:=args) false (boolList_extend current ez)
      (boolList_extend optimal ez) (parameters_extend params ez) tape
    let grown := mid++er
    let checked := args.set .r3 rr
    have compared : NaturalRun program (BinaryProductOrderProgram.steps c o R+5)
        (state mid args [] tape 3) [] (state grown checked [] tape 4) := check
    let ok := Nat.ble (value c) (value R*value o)
    have testFlag : grown[rr]?=some (.flag ok) := test
    have exactReady : ready c o R=ok := by simp [ready,FlexibleGridProvider.readyCode,nonzero,ok]
    have beq : (value o == 0)=false := by simp [nonzero]
    cases result : ok with
    | false =>
      have flag : grown[rr]?=some (.flag false) := result ▸ testFlag
      let root := grown.length
      let extra : NaturalHeap := [.pair rr rr]
      have read : NaturalRun program 2 (state grown checked [] tape 4) []
          (state (grown++extra) (checked.set .r3 root) [] tape 7) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
          tagBranch,allocateNatural,Recipe.cell,flag,checked,extra,root]
      have finished : Output (grown++extra) root c o R M :=
        ⟨rr,rr,by simp [root,extra],by simpa [exactReady,result] using lookup_extend flag extra,
          by simpa [active,exactReady,result] using lookup_extend flag extra⟩
      refine ⟨ez++er++extra,checked,root,
        BinaryZeroProgram.steps o+6+(BinaryProductOrderProgram.steps c o R+5+2+1),?_,?_,?_⟩
      · simpa only [grown,mid,List.append_assoc] using finished
      · simpa only [grown,mid,ez,args,List.append_assoc,List.nil_append] using
          append_run start (.step branch (append_run compared read))
      · unfold instructionBound; omega
    | true =>
      have flag : grown[rr]?=some (.flag true) := result ▸ testFlag
      have next : tickNatural program (state grown checked [] tape 4)=some ⟨state grown checked [] tape 5,[],0⟩ := by
        simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,tagBranch,checked,flag]
      obtain ⟨ea,ra,threshold,checkThreshold⟩ := comparison_call (r:=checked) true
        (boolList_extend (boolList_extend current ez) er) (boolList_extend (boolList_extend optimal ez) er)
        (parameters_extend (parameters_extend params ez) er) tape
      let final := grown++ea
      let outArgs := checked.set .r1 ra
      let root := final.length
      let extra : NaturalHeap := [.pair rr ra]
      have compute : NaturalRun program (BinaryProductOrderProgram.steps M c R+7)
          (state grown checked [] tape 5) [] (state final outArgs [] tape 6) := checkThreshold
      have finish : NaturalRun program 1 (state final outArgs [] tape 6) []
          (state (final++extra) (outArgs.set .r3 root) [] tape 7) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
          allocateNatural,Recipe.cell,extra,root,outArgs,checked]
      have finished : Output (final++extra) root c o R M :=
        ⟨rr,ra,by simp [root,extra],by simpa [exactReady,result,final] using lookup_extend (lookup_extend flag ea) extra,
          by simpa [active,exactReady,result,beq,final,grown,mid] using lookup_extend threshold extra⟩
      refine ⟨ez++er++ea++extra,outArgs,root,
        BinaryZeroProgram.steps o+6+(BinaryProductOrderProgram.steps c o R+5+
          (BinaryProductOrderProgram.steps M c R+7+1+1)+1),?_,?_,?_⟩
      · simpa only [final,grown,mid,List.append_assoc] using finished
      · simpa only [final,grown,mid,ez,args,List.append_assoc,List.nil_append] using
          append_run start (.step branch (append_run compared (.step next (append_run compute finish))))
      · unfold instructionBound; omega

end DirectedFlowCutGap.AdaptiveGatesProgram
