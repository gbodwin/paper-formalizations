import DirectedFlowCutGap.InitialUniformTables
import DirectedFlowCutGap.AdaptiveControllerStorage
import DirectedFlowCutGap.RetainedDemandMask

/-! Compute and store the actual initial mass and retained state. -/

namespace DirectedFlowCutGap.InitialRetainedStateProgram

open BooleanTableRead (BoolList)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open RetainedGridState IntegralNetworkFlow
open RetainedMassTableProgram (TableAt DataRows pairOrder)
open InitialUniformTables (uniform words unitWord)

def flatLabel (pc : Fin 18) : Fin 340 := ⟨48+pc.val,by omega⟩
def massLabel (pc : Fin 274) : Fin 340 := ⟨66+pc.val,by omega⟩

def program : Program 340 := fun pc =>
  if pc.val < 48 then
    match pc.val with
    | 0 => .call 16 1 .r0
    | 1 => .field .r2 .r3 true 2
    | 2 => .field .r3 .r3 false 3
    | 3 => .make .r1 (.pair .r1 .r2) 4
    | 4 => .make .r1 (.pair .r1 .r3) 5
    | 5 => .make .r3 (.pair .r0 .r1) 6
    | 16 => .call (flatLabel 0) 17 .r3
    | 17 => .call 24 18 .r3
    | 18 => .make .r0 (.pair .r0 .r2) 19
    | 19 => .make .r3 (.pair .r0 .r3) 20
    | 20 => .ret .r3
    | 24 => .move .r0 .r3 25
    | 25 => .call (massLabel 0) 26 .r3
    | 26 => .ret .r3
    | _ => .halt
  else if h : pc.val < 66 then
    if pc.val=56 then .ret .r3
    else ReferenceProgramLabels.instruction flatLabel (FlattenDemandMaskProgram.program ⟨pc.val-48,by omega⟩)
  else if pc.val=89 then .ret .r3
  else ReferenceProgramLabels.instruction massLabel (RetainedMassTableProgram.program ⟨pc.val-66,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 340

def instructionBound (n : ℕ) : ℕ := (6*n+8)*n+RetainedMassTableProgram.instructionBudget (n*n) n 1+22

private theorem flat_slots (pc : Fin 18) (h : FlattenDemandMaskProgram.program pc≠.halt) :
    program (flatLabel pc)=ReferenceProgramLabels.instruction flatLabel (FlattenDemandMaskProgram.program pc) := by
  by_cases stop : pc.val=8
  · have eq : pc=8 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,flatLabel,show ¬48+pc.val<48 by omega,show 48+pc.val<66 by omega,show 48+pc.val≠56 by omega]

private theorem mass_slots (pc : Fin 274) (h : RetainedMassTableProgram.program pc≠.halt) :
    program (massLabel pc)=ReferenceProgramLabels.instruction massLabel (RetainedMassTableProgram.program pc) := by
  by_cases stop : pc.val=23
  · have eq : pc=23 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,massLabel,show ¬66+pc.val<48 by omega,show ¬66+pc.val<66 by omega,show 66+pc.val≠89 by omega]

def Constants (heap : NaturalHeap) (root : ℕ) : Prop :=
  ∃ scale free,heap[root]?=some (.pair scale free) ∧ BoolList heap scale unitWord ∧ heap[free]?=some (.flag false)

theorem words_width (n : ℕ) : ∀ ws ∈ words n,∀ w ∈ ws,w.length≤1 := by
  intro ws hws w hw
  obtain rfl := List.eq_of_mem_replicate hws
  obtain rfl := List.eq_of_mem_replicate hw
  simp

private theorem rows_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {mask : PairFlags n}
    (h : RetainedDemandEraseProgram.RowsAt heap root mask) (ext : NaturalHeap) :
    RetainedDemandEraseProgram.RowsAt (heap++ext) root mask := by
  obtain ⟨refs,spine,rows⟩ := h
  exact ⟨refs,BinaryPointerListRead.pointerList_extend spine ext,rows.imp (fun _ _ r => boolList_extend r ext)⟩

set_option maxHeartbeats 2200000 in
private theorem sum_call {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {active : Bits}
    (flat : BoolList heap r.d active) (cut : BoolList heap r.c (List.replicate n false))
    (table : TableAt heap r.b (words n)) (count : active.length=n*n)
    (stack : List (Frame ℕ 340)) (tape : Bits) :
    let word := RetainedMassTableProgram.sum (List.replicate n false) active (words n)
    ∃ (ext : NaturalHeap) (root k : ℕ),BoolList (heap++ext) root word ∧
      NaturalRun program k (state heap r stack tape 17) [] (state (heap++ext) (r.set .r3 root) stack tape 18) ∧
      k≤ RetainedMassTableProgram.instructionBudget (n*n) n 1+5 := by
  let frame : Frame ℕ 340 := ⟨18,.r3,r⟩
  let args := r.set .r0 r.d
  have load : NaturalRun program 2 (state heap r stack tape 17) [] (state heap args (frame::stack) tape 25) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,args,frame]
  have length : active.length=(words n).length := by simpa only [words,List.length_replicate] using count
  have aligned : ∀ ws∈words n,ws.length=(List.replicate n false).length := by
    simpa only [List.length_replicate] using RetainedMassTableProgram.data_aligned (InitialUniformTables.data_rows n)
  obtain ⟨ext,root,rep,body⟩ := RetainedMassTableProgram.natural_trace (r:=args) flat table cut length aligned tape
  let k := RetainedMassTableProgram.steps (List.replicate n false) active (words n)+1
  have invoke := ReferenceProgramInvocation.call massLabel mass_slots (caller:=25) (continuation:=26)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) (frame::stack) body
  let stop := state (heap++ext) (args.set .r3 root) (frame::stack) tape 26
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) stack tape 18,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  have cap : k≤ RetainedMassTableProgram.instructionBudget (n*n) n 1 := by
    simpa only [k,words,List.length_replicate] using RetainedMassTableProgram.steps_le (words n) active
      (List.replicate n false) 1 aligned (words_width n)
  refine ⟨ext,root,k+5,rep,?_,by omega⟩
  have cnt : 2+(k+2+1)=k+5 := by omega
  rw [← cnt]
  simpa only [k,stop,Registers.get,Registers.set,List.nil_append] using append_run load (append_run invoke (.step ret (.done _)))

set_option maxHeartbeats 2500000 in
private theorem compute_mass {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {mask : PairFlags n}
    (active : RetainedDemandEraseProgram.RowsAt heap r.a mask) (weights : TableAt heap r.b (words n))
    (cut : BoolList heap r.c (List.replicate n false)) (tape : Bits) :
    let word := RetainedMassTableProgram.sum (List.replicate n false) ((pairOrder n).map (flag mask)) (words n)
    ∃ (ext : NaturalHeap) (root k : ℕ),
      (∃ masks mass,(heap++ext)[root]?=some (.pair masks mass) ∧ (heap++ext)[masks]?=some (.pair r.a r.c) ∧
        BoolList (heap++ext) mass word) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (r.set .r0 root) [] tape 1) ∧
      k≤ (6*n+8)*n+RetainedMassTableProgram.instructionBudget (n*n) n 1+14 := by
  let frame : Frame ℕ 340 := ⟨1,.r0,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape 16,[],0⟩ := rfl
  obtain ⟨ef,flags,_,rep,flatRun⟩ := FlattenDemandMaskProgram.natural_trace active tape
  let mid := heap++ef
  let args := r.set .r3 flags
  have invoke := ReferenceProgramInvocation.call flatLabel flat_slots (caller:=16) (continuation:=17)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] flatRun
  have got : NaturalRun program ((6*n+8)*n+5) (state heap r [frame] tape 16) []
      (state mid args [frame] tape 17) := by
    simpa only [mid,args,Registers.get,Registers.set] using invoke
  obtain ⟨em,mass,k,word,body,time⟩ := sum_call (r:=args) rep (boolList_extend cut ef)
    (RoundInputPackProgram.weights_extend weights ef)
    (by simp only [List.length_map,RetainedMassTableProgram.pairOrder_length]) [frame] tape
  let grown := mid++em
  let first : Cell ℕ := .pair r.a r.c
  let second : Cell ℕ := .pair grown.length mass
  let endCells : NaturalHeap := [first,second]
  let front := args.set .r3 mass
  have finish : NaturalRun program 3 (state grown front [frame] tape 18) []
      (state (grown++endCells) (r.set .r0 (grown.length+1)) [] tape 1) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      front,args,first,second,endCells,frame,allocateNatural,Recipe.cell]
  refine ⟨ef++em++endCells,grown.length+1,(6*n+8)*n+5+(k+3)+1,?_,?_,by omega⟩
  · have atPacked : (grown++endCells)[grown.length+1]?=some second := by simp [endCells]
    have atMasks : (grown++endCells)[grown.length]?=some first := by simp [endCells]
    have packed : ∃ masks mass', (grown++endCells)[grown.length+1]?=some (.pair masks mass') ∧
        (grown++endCells)[masks]?=some (.pair r.a r.c) ∧ BoolList (grown++endCells) mass'
          (RetainedMassTableProgram.sum (List.replicate n false) ((pairOrder n).map (flag mask)) (words n)) :=
      ⟨grown.length,mass,atPacked,atMasks,boolList_extend word endCells⟩
    simpa only [grown,mid,List.append_assoc,first,second] using packed
  · simpa only [grown,mid,List.append_assoc,List.nil_append] using
      NaturalRun.step enter (append_run got (append_run body finish))

set_option maxHeartbeats 2600000 in
theorem natural_state {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (E : ResidualSearch.Enumeration (Fin n)) (positive : 0<L)
    (active : RetainedDemandEraseProgram.RowsAt heap r.a (RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E L))
    (weights : TableAt heap r.b (words n)) (cut : BoolList heap r.c (List.replicate n false))
    (constants : Constants heap r.d) (tape : Bits) :
    let s := RetainedDemandMask.initial (EncodedIntegerShortestPaths.graph adj) E L positive
    ∃ (ext : NaturalHeap) (root packed runtime free k : ℕ),
      AdaptiveControllerStorage.StateAt (heap++ext) root s.data (words n) unitWord ∧
      NaturalRun program k (state heap r [] tape 0) []
        (state (heap++ext) ⟨packed,runtime,free,root⟩ [] tape 6) ∧ k≤ instructionBound n := by
  let mask := RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E L
  let s := RetainedDemandMask.initial (EncodedIntegerShortestPaths.graph adj) E L positive
  obtain ⟨em,packed,k,⟨masks,mass,atPacked,atMasks,bits⟩,body,time⟩ := compute_mass active weights cut tape
  let mid := heap++em
  obtain ⟨scale,free,atConsts,scaleRep,freeAt⟩ := constants
  let args : Registers ℕ := ⟨packed,r.b,free,scale⟩
  have atConfig : mid[r.d]?=some (.pair scale free) := lookup_extend atConsts em
  have fields : NaturalRun program 2 (state mid (r.set .r0 packed) [] tape 1) []
      (state mid args [] tape 3) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,atConfig,args]
  let base := mid.length
  let context := base
  let runtime := base+1
  let result := base+2
  let first : Cell ℕ := .pair r.b free
  let second : Cell ℕ := .pair context scale
  let third : Cell ℕ := .pair packed runtime
  let ext : NaturalHeap := [first,second,third]
  have pack : NaturalRun program 3 (state mid args [] tape 3) []
      (state (mid++ext) ⟨packed,runtime,free,result⟩ [] tape 6) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,base,context,runtime,result,ext,first,second,third,allocateNatural,Recipe.cell]
  let d := InitialUniformTables.data_rows n
  have massValue := RetainedMassTableProgram.mass_value (uniform n) mask (Vector.replicate n false) d
  rw [EncodedRoundingState.mass_value] at massValue
  have current : value (RetainedMassTableProgram.sum (List.replicate n false) ((pairOrder n).map (flag mask)) (words n))=s.data.current := by
    change value _=massNumerator mask (Vector.replicate n false) (uniform n)
    simpa only [Vector.toList_replicate] using massValue
  have updated : RoundStateUpdateProgram.UpdatedAt (mid++ext) packed s.data :=
    ⟨masks,mass,_,lookup_extend atPacked ext,
      ⟨r.a,r.c,lookup_extend atMasks ext,rows_extend (rows_extend active em) ext,
        by
          change BoolList (mid++ext) r.c (Vector.replicate n false).toList
          rw [Vector.toList_replicate]
          exact boolList_extend (boolList_extend cut em) ext⟩,
      boolList_extend bits ext,current⟩
  have finalRep : AdaptiveControllerStorage.StateAt (mid++ext) result s.data (words n) unitWord :=
    ⟨packed,runtime,context,scale,r.b,free,by simp [base,result,ext,third],updated,
      by simp [base,runtime,ext,second],by simp [base,context,ext,first],
      RoundInputPackProgram.weights_extend (RoundInputPackProgram.weights_extend weights em) ext,
      lookup_extend (lookup_extend freeAt em) ext,boolList_extend (boolList_extend scaleRep em) ext,rfl,d⟩
  refine ⟨em++ext,result,packed,runtime,free,k+5,?_,?_,?_⟩
  · simpa only [mid,List.append_assoc] using finalRep
  · simpa only [mid,List.append_assoc,List.nil_append] using append_run body (append_run fields pack)
  · unfold instructionBound
    omega

end DirectedFlowCutGap.InitialRetainedStateProgram
