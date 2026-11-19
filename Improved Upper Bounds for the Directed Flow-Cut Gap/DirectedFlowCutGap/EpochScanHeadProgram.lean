import DirectedFlowCutGap.CacheGatesProgram
import DirectedFlowCutGap.CurrentDemandProgram

/-! Test one actual epoch head against the live cache and remaining-demand mask. -/

namespace DirectedFlowCutGap.EpochScanHeadProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open ConcreteExpressionProgram (append_run)
open AdaptiveControllerStorage (Parameters CacheAt cache_extend)
open GraphWalkExtension (Edge edge_extend)
open EpochActiveFromMaskProgram (labelPair)

def gateLabel (pc : Fin 298) : Fin 382 := ⟨32+pc.val,by omega⟩
def memberLabel (pc : Fin 52) : Fin 382 := ⟨330+pc.val,by omega⟩

def program : Program 382 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call (gateLabel 0) 1 .r1
    | 1 => .field .r1 .r1 true 2
    | 2 => .branch .r1 31 8 3 31
    | 3 => .call 12 4 .r1
    | 4 => .branch .r1 31 8 6 31
    | 6 => .move .r3 .r0 7
    | 8 => .make .r3 .nil 7
    | 12 => .field .r0 .r0 false 13
    | 13 => .call (memberLabel 0) 14 .r3
    | 14 => .ret .r3
    | _ => .halt
  else if h : pc.val<330 then
    if pc.val=36 then .ret .r3
    else ReferenceProgramLabels.instruction gateLabel (CacheGatesProgram.program ⟨pc.val-32,by omega⟩)
  else if pc.val=338 then .ret .r3
  else ReferenceProgramLabels.instruction memberLabel (CurrentDemandProgram.program ⟨pc.val-330,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 382

def active (c o : ℕ) (R M : Bits) : Bool := FlexibleGridProvider.readyCode (value R) c o &&
  !(o == 0) && Nat.ble (value M) (value R*c)

def keep {n : ℕ} (d : Data n) (optimum : ℕ) (R M : Bits) (p : Pair n) : Bool :=
  active d.current optimum R M && flag d.remaining p

def instructionBound (n H cur opt ratio threshold : ℕ) : ℕ :=
  CacheGatesProgram.instructionBound H cur opt ratio threshold+CurrentDemandProgram.instructionBound n+11

def allocationBound (n cur opt ratio threshold : ℕ) : ℕ :=
  CacheGatesProgram.allocationBound cur opt ratio threshold+CurrentDemandProgram.instructionBound n+1

private theorem gate_slots (pc : Fin 298) (h : CacheGatesProgram.program pc≠.halt) :
    program (gateLabel pc)=ReferenceProgramLabels.instruction gateLabel (CacheGatesProgram.program pc) := by
  by_cases stop : pc.val=4
  · have eq : pc=4 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,gateLabel,show ¬32+pc.val<32 by omega,show 32+pc.val<330 by omega,show 32+pc.val≠36 by omega]

private theorem member_slots (pc : Fin 52) (h : CurrentDemandProgram.program pc≠.halt) :
    program (memberLabel pc)=ReferenceProgramLabels.instruction memberLabel (CurrentDemandProgram.program pc) := by
  by_cases stop : pc.val=8
  · have eq : pc=8 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,memberLabel,show ¬330+pc.val<32 by omega,show ¬330+pc.val<330 by omega,show 330+pc.val≠338 by omega]

private theorem member_call {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {p : Pair n} {key tail : ℕ}
    {d : Data n} {optimum : ℕ} {candidate : Family n} {words candidateWords : List (List Bits)} {scale : Bits}
    (head : heap[r.a]?=some (.pair key tail)) (edge : Edge heap key (labelPair p))
    (cache : CacheAt heap r.d d optimum candidate words candidateWords scale) (tape : Bits) :
    ∃ ext root,(heap++ext)[root]?=some (.flag (flag d.remaining p)) ∧
      NaturalRun program (CurrentDemandProgram.steps p+5) (state heap r [] tape 3) []
        (state (heap++ext) (r.set .r1 root) [] tape 4) ∧ ext.length≤CurrentDemandProgram.steps p := by
  let frame : Frame ℕ 382 := ⟨4,.r1,r⟩
  let args := r.set .r0 key
  have enter : NaturalRun program 2 (state heap r [] tape 3) [] (state heap args [frame] tape 13) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      head,frame,args]
  obtain ⟨ext,out,root,rep,body⟩ := CurrentDemandProgram.natural_flag (r:=args) edge cache tape
  have invoke := ReferenceProgramInvocation.call memberLabel member_slots (caller:=13) (continuation:=14)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape 14
  have run : NaturalRun program (CurrentDemandProgram.steps p+2) (state heap args [frame] tape 13) [] stop := by
    simpa only [stop,Registers.get,Registers.set] using invoke
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) [] tape 4,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  let k := CurrentDemandProgram.steps p
  refine ⟨ext,root,rep,?_,ControllerWordWidth.extension_bound body rfl⟩
  have count : 2+(k+2+1)=k+5 := by omega
  change NaturalRun program (k+5) _ [] _
  rw [← count]
  exact append_run enter (append_run run (.step ret (.done _)))

set_option maxHeartbeats 2300000 in
theorem natural_head {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {p : Pair n} {key tail : ℕ}
    {adj : PairFlags n} {R M scale : Bits} {d : Data n} {optimum : ℕ} {candidate : Family n}
    {words candidateWords : List (List Bits)} (head : heap[r.a]?=some (.pair key tail)) (edge : Edge heap key (labelPair p))
    (params : Parameters (L:=L) heap r.c adj R M) (cache : CacheAt heap r.d d optimum candidate words candidateWords scale)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      (if keep d optimum R M p then root=r.a else (heap++ext)[root]?=some .nil) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 7) ∧
      k ≤ instructionBound n heap.length d.current.size optimum.size R.length M.length ∧
      ext.length ≤ allocationBound n d.current.size optimum.size R.length M.length := by
  obtain ⟨eg,out,root,k,⟨ready,activeRoot,pair,_,activeFlag⟩,body,within,allocated⟩ :=
    CacheGatesProgram.natural_cache_gates params cache tape
  have invoke := ReferenceProgramInvocation.call gateLabel gate_slots (caller:=0) (continuation:=1)
    (dst:=.r1) (result:=.r3) (by rfl) (by rfl) [] body
  let mid := heap++eg
  let fields := r.set .r1 root
  let afterGate := r.set .r1 activeRoot
  have gateRun : NaturalRun program (k+2) (state heap r [] tape 0) [] (state mid fields [] tape 1) := by
    simpa only [mid,fields,Registers.get,Registers.set] using invoke
  have first : tickNatural program (state mid fields [] tape 1)=some ⟨state mid afterGate [] tape 2,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,fields,afterGate,mid,pair]
  have gate : mid[activeRoot]?=some (.flag (active d.current optimum R M)) := activeFlag
  have demandBound := CurrentDemandProgram.steps_le p
  cases hact : active d.current optimum R M with
  | false =>
    have tested : mid[activeRoot]?=some (.flag false) := hact ▸ gate
    have stop : NaturalRun program 2 (state mid afterGate [] tape 2) []
        (state (mid++[.nil]) (afterGate.set .r3 mid.length) [] tape 7) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        tagBranch,allocateNatural,Recipe.cell,afterGate,tested]
    refine ⟨eg++[.nil],afterGate,mid.length,k+2+(2+1),?_,?_,?_,?_⟩
    · simp [keep,hact,← List.append_assoc,mid]
    · simpa only [mid,List.append_assoc,List.nil_append] using append_run gateRun (.step first stop)
    · unfold instructionBound; omega
    · simp only [List.length_append,List.length_singleton,allocationBound]; omega
  | true =>
    have tested : mid[activeRoot]?=some (.flag true) := hact ▸ gate
    have advance : tickNatural program (state mid afterGate [] tape 2)=some ⟨state mid afterGate [] tape 3,[],0⟩ := by
      simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,tagBranch,afterGate,tested]
    obtain ⟨em,member,flagAt,check,used⟩ := member_call (r:=afterGate) (lookup_extend head eg) (edge_extend edge eg)
      (cache_extend cache eg) tape
    let grown := mid++em
    let checked := afterGate.set .r1 member
    let j := CurrentDemandProgram.steps p
    cases hmember : flag d.remaining p with
    | false =>
      have flagRead : grown[member]?=some (.flag false) := hmember ▸ flagAt
      have stop : NaturalRun program 2 (state grown checked [] tape 4) []
          (state (grown++[.nil]) (checked.set .r3 grown.length) [] tape 7) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
          tagBranch,allocateNatural,Recipe.cell,flagRead,checked]
      refine ⟨eg++em++[.nil],checked,grown.length,k+2+(j+5+2+1+1),?_,?_,?_,?_⟩
      · have nil : (grown++[.nil])[grown.length]?=some .nil := by simp
        simpa only [keep,hact,hmember,Bool.and_self,Bool.true_and,Bool.false_eq_true,ite_false,grown,mid,List.append_assoc] using nil
      · simpa only [grown,mid,j,List.append_assoc,List.nil_append,Nat.add_assoc] using
          append_run gateRun (.step first (.step advance (append_run check stop)))
      · unfold instructionBound; omega
      · simp only [List.length_append,List.length_singleton,allocationBound]; omega
    | true =>
      have flagRead : grown[member]?=some (.flag true) := hmember ▸ flagAt
      have finish : NaturalRun program 2 (state grown checked [] tape 4) []
          (state grown (checked.set .r3 r.a) [] tape 7) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
          tagBranch,flagRead,checked,afterGate]
      refine ⟨eg++em,checked,r.a,k+2+(j+5+2+1+1),by simp [keep,hact,hmember],?_,?_,?_⟩
      · simpa only [grown,mid,j,List.append_assoc,List.nil_append,Nat.add_assoc] using
          append_run gateRun (.step first (.step advance (append_run check finish)))
      · unfold instructionBound; omega
      · simp only [List.length_append,allocationBound]; omega

end DirectedFlowCutGap.EpochScanHeadProgram
