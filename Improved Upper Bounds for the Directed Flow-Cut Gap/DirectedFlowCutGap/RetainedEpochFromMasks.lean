import DirectedFlowCutGap.RetainedEpochScheduleProgram

/-!
# Guarded epoch draws from the retained demand mask

The physical program flattens the actual retained flag rows, builds the
draw schedule for their active count, then executes the guarded batch.
The same tape passes through all three stages. A represented grid bound
and trial spine are shared across the calls.
-/

namespace DirectedFlowCutGap.RetainedEpochFromMasks

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState

def flattenLabel (pc : Fin 18) : Fin 174 := ⟨6+pc.val,by omega⟩
def scheduleLabel (pc : Fin 56) : Fin 174 := ⟨24+pc.val,by omega⟩
def drawLabel (pc : Fin 94) : Fin 174 := ⟨80+pc.val,by omega⟩

def program : Program 174 := fun pc =>
  if pc.val < 6 then
    match pc.val with
    | 0 => .call (flattenLabel 0) 1 .r0
    | 1 => .call (scheduleLabel 36) 2 .r0
    | 2 => .move .r1 .r2 (drawLabel 14)
    | _ => .halt
  else if pc.val=14 ∨ pc.val=55 then .ret .r3
  else if h : pc.val < 24 then
    ReferenceProgramLabels.instruction flattenLabel (FlattenDemandMaskProgram.program ⟨pc.val-6,by omega⟩)
  else if h : pc.val < 80 then
    ReferenceProgramLabels.instruction scheduleLabel (RetainedEpochScheduleProgram.program ⟨pc.val-24,by omega⟩)
  else ReferenceProgramLabels.instruction drawLabel
    (PhysicalDrawSequenceProgram.program ⟨pc.val-80,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 174)) (tape : Bits)
    (pc : Fin 174) : NaturalState 174 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def flags {n : ℕ} (a : PairFlags n) : Bits :=
  (RetainedMassTableProgram.pairOrder n).map (flag a)

def bounds {n L : ℕ} (a : PairFlags n) (positive : 0<L) : List Bits :=
  PhysicalEpochDraws.epochBounds L positive (Fintype.card ↥(remainingSet a))

def steps {n L : ℕ} (a : PairFlags n) (positive : 0<L) (fuel : ℕ) (tape : Bits) : ℕ :=
  (6*n+8)*n+3+RetainedEpochScheduleProgram.steps (flags a)+
    PhysicalDrawSequenceProgram.steps fuel (bounds a positive) tape+6

private theorem flatten_slots (pc : Fin 18) (h : FlattenDemandMaskProgram.program pc≠.halt) :
    program (flattenLabel pc) = ReferenceProgramLabels.instruction flattenLabel (FlattenDemandMaskProgram.program pc) := by
  by_cases hp : pc.val=8
  · have eq : pc=8 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,flattenLabel,show ¬6+pc.val<6 by omega,show 6+pc.val≠14 by omega,
      show 6+pc.val≠55 by omega,show 6+pc.val<24 by omega]

private theorem schedule_slots (pc : Fin 56) (h : RetainedEpochScheduleProgram.program pc≠.halt) :
    program (scheduleLabel pc) =
      ReferenceProgramLabels.instruction scheduleLabel (RetainedEpochScheduleProgram.program pc) := by
  by_cases hp : pc.val=31
  · have eq : pc=31 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,scheduleLabel,show ¬24+pc.val<6 by omega,show 24+pc.val≠14 by omega,
      show 24+pc.val≠55 by omega,show ¬24+pc.val<24 by omega,show 24+pc.val<80 by omega]

private theorem draw_slots (pc : Fin 94) :
    program (drawLabel pc) = ReferenceProgramLabels.instruction drawLabel (PhysicalDrawSequenceProgram.program pc) := by
  simp [program,drawLabel,show ¬80+pc.val<6 by omega,show 80+pc.val≠14 by omega,
    show 80+pc.val≠55 by omega,show ¬80+pc.val<24 by omega,show ¬80+pc.val<80 by omega]

private theorem join {s u v : NaturalState 174} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

theorem natural_epoch {n L fuel : ℕ} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ} (positive : 0<L)
    (rows : RetainedDemandEraseProgram.RowsAt heap r.a a)
    (level : BoolList heap r.b L.bits) (trials : IndexSpine heap r.c fuel) (tape : Bits) :
    let observed := PhysicalDrawSequenceProgram.batch fuel (bounds a positive) tape
    ∃ extra out, PhysicalDrawSequenceProgram.StoredBatch (heap++extra) out.d observed.draws ∧
      NaturalRun program (steps a positive fuel tape) (state heap r [] tape 0) (observed.requests.map Event.request)
        (state (heap++extra) out [] observed.suffix (drawLabel 15)) := by
  let ff : Frame ℕ 174 := ⟨1,.r0,r⟩
  obtain ⟨ef,flat,_,hflat,htrace⟩ := FlattenDemandMaskProgram.natural_trace rows tape
  let mid := heap++ef
  let rflat := r.set .r0 flat
  have callFlat : tickNatural program (state heap r [] tape 0)=
      some ⟨state heap r [ff] tape (flattenLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run flattenLabel FlattenDemandMaskProgram.program program flatten_slots htrace
  have lift := ReferenceProgramStack.run program [ff] lift
  let beforeFlat := state mid (r.set .r3 flat) [ff] tape (flattenLabel 8)
  have flatRun : NaturalRun program ((6*n+8)*n+3) (state heap r [ff] tape (flattenLabel 0)) [] beforeFlat := by
    simpa [state,mid,beforeFlat,FlattenDemandMaskProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have retFlat : tickNatural program beforeFlat=some ⟨state mid rflat [] tape 1,[],0⟩ := by
    cases r
    simp [beforeFlat,rflat,ff,state,tickNatural,program,flattenLabel,Registers.get,Registers.set]
  have flatInput : BoolList mid rflat.a (flags a) := by cases r; exact hflat
  have keptLevel : BoolList mid rflat.b L.bits := by cases r; exact boolList_extend level ef
  obtain ⟨es,schedule,rs,hrs,hwords,htrace⟩ :=
    RetainedEpochScheduleProgram.natural_schedule positive flatInput keptLevel tape
  have count := RetainedEpochScheduleProgram.active_eq a
  change RetainedEpochScheduleProgram.activeCount (flags a) = _ at count
  rw [count] at hwords
  let grown := mid++es
  let rready := rflat.set .r0 schedule
  let fs : Frame ℕ 174 := ⟨2,.r0,rflat⟩
  have callSchedule : tickNatural program (state mid rflat [] tape 1)=
      some ⟨state mid rflat [fs] tape (scheduleLabel 36),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run scheduleLabel RetainedEpochScheduleProgram.program program schedule_slots htrace
  have lift := ReferenceProgramStack.run program [fs] lift
  let beforeSchedule := state grown rs [fs] tape (scheduleLabel 31)
  have scheduleRun : NaturalRun program (RetainedEpochScheduleProgram.steps (flags a))
      (state mid rflat [fs] tape (scheduleLabel 36)) [] beforeSchedule := by
    simpa [state,grown,beforeSchedule,RetainedEpochScheduleProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state] using lift
  have retSchedule : tickNatural program beforeSchedule=some ⟨state grown rready [] tape 2,[],0⟩ := by
    simp [beforeSchedule,rready,fs,state,tickNatural,program,scheduleLabel,Registers.get,hrs]
  let args := rready.set .r1 r.c
  have move : tickNatural program (state grown rready [] tape 2)=
      some ⟨state grown args [] tape (drawLabel 14),[],0⟩ := by
    cases r
    rfl
  have words : PathCostMaterialization.WordList grown args.a (bounds a positive) := by cases r; exact hwords
  have htrials : IndexSpine grown args.b fuel := indexSpine_extend (indexSpine_extend trials ef) es
  obtain ⟨ed,result,hrep,drawRun⟩ := PhysicalDrawSequenceProgram.natural_batch words htrials tape
  let observed := PhysicalDrawSequenceProgram.batch fuel (bounds a positive) tape
  let out := args.set .r3 result
  have lift := ReferenceProgramLabels.run drawLabel PhysicalDrawSequenceProgram.program program (fun pc _ => draw_slots pc) drawRun
  have body : NaturalRun program (PhysicalDrawSequenceProgram.steps fuel (bounds a positive) tape+1)
      (state grown args [] tape (drawLabel 14)) (observed.requests.map Event.request)
      (state (grown++ed) out [] observed.suffix (drawLabel 15)) := by
    simpa [out,state,PhysicalDrawSequenceProgram.state,ReferenceProgramLabels.state] using lift
  refine ⟨ef++es++ed,out,?_,?_⟩
  · simpa only [out,Registers.set,grown,mid,List.append_assoc] using hrep
  · have trace := NaturalRun.step callFlat (join flatRun (NaturalRun.step retFlat
      (NaturalRun.step callSchedule (join scheduleRun (NaturalRun.step retSchedule (NaturalRun.step move body))))))
    unfold steps
    convert trace using 1 <;> first | rfl | omega | simp only [grown,mid,observed,List.append_assoc]

private theorem permutation_length (m : ℕ) : (PhysicalEpochDraws.permutationBounds m).length=m := by
  simpa only [RetainedEpochScheduleProgram.permutationWords,List.length_map] using
    RetainedEpochScheduleProgram.permutationWords_length m

private theorem permutation_le (m : ℕ) (x : PhysicalEpochDraws.Positive)
    (hx : x ∈ PhysicalEpochDraws.permutationBounds m) : x.val ≤ m := by
  induction m with
  | zero => simp [PhysicalEpochDraws.permutationBounds] at hx
  | succ m ih =>
    simp only [PhysicalEpochDraws.permutationBounds,List.mem_cons] at hx
    rcases hx with rfl|hx
    · rfl
    · exact (ih hx).trans (Nat.le_succ _)

def width (n L : ℕ) : ℕ := (max (n*n) L).size

theorem widths {n L : ℕ} (a : PairFlags n) (positive : 0<L) :
    ∀ x ∈ bounds a positive,x.length ≤ width n L := by
  intro x hx
  unfold bounds PhysicalEpochDraws.epochBounds at hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
  have hnum : v.val ≤ max (n*n) L := by
    rcases List.mem_append.mp hv with hp|hc
    · exact (permutation_le _ v hp).trans ((RetainedDrawTrees.active_card_le a).trans (le_max_left _ _))
    · have hv := (List.mem_replicate.mp hc).2
      rw [hv]
      exact le_max_right _ _
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le_size hnum

def instructionBound (n L fuel : ℕ) : ℕ :=
  (6*n+8)*n+3+RetainedEpochScheduleProgram.instructionBound (n*n)+
    PhysicalDrawSequenceProgram.instructionBound (width n L) fuel (2*(n*n))+5

theorem steps_le {n L : ℕ} (a : PairFlags n) (positive : 0<L) (fuel : ℕ) (tape : Bits) :
    steps a positive fuel tape ≤ instructionBound n L fuel := by
  have hflags : (flags a).length=n*n := by simp [flags,RetainedMassTableProgram.pairOrder_length]
  have hlen : (bounds a positive).length ≤ 2*(n*n) := by
    simp only [bounds,PhysicalEpochDraws.epochBounds,List.length_map,List.length_append,permutation_length,
      PhysicalEpochDraws.cellBounds,List.length_replicate]
    have h := RetainedDrawTrees.active_card_le a
    omega
  have hs := RetainedEpochScheduleProgram.steps_le (flags a)
  rw [hflags] at hs
  have hd := PhysicalDrawSequenceProgram.steps_le fuel (width n L) (bounds a positive) tape (widths a positive)
  have mono : PhysicalDrawSequenceProgram.instructionBound (width n L) fuel (bounds a positive).length ≤
      PhysicalDrawSequenceProgram.instructionBound (width n L) fuel (2*(n*n)) := by
    unfold PhysicalDrawSequenceProgram.instructionBound
    gcongr
  have hdraw := hd.trans mono
  unfold steps instructionBound
  omega

private theorem at_entry (s : NaturalState 174) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_epoch {n L H A fuel : ℕ} (a : PairFlags n) (positive : 0<L)
    (initial : BitState 174) (bounded : initial.Bounded H A) (hp : initial.pc=0)
    (hc : initial.stack=[]) (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (rows : RetainedDemandEraseProgram.RowsAt (eraseState initial).heap (eraseState initial).registers.a a)
    (level : BoolList (eraseState initial).heap (eraseState initial).registers.b L.bits)
    (trials : IndexSpine (eraseState initial).heap (eraseState initial).registers.c fuel) :
    let observed := PhysicalDrawSequenceProgram.batch fuel (bounds a positive) initial.source
    let budget := instructionBound n L fuel
    let run := GuardedReferenceExecution.execute program (budget+1) initial 0
    match (EncodedSolverBits.run (LazyFairBitTrees.lower fuel (RetainedDrawTrees.sampleTape positive a))
      initial.source).map (fun p => (PhysicalEpochDraws.values L (Fintype.card ↥(remainingSet a)) p.1,p.2)) with
    | none => run=none
    | some (indices,(rest,reads)) =>
      ∃ out charge, run=some (out,charge) ∧
        PhysicalDrawSequenceProgram.StoredBatch (eraseState out).heap (eraseState out).registers.d observed.draws ∧
        indices=observed.draws.map (fun r => value r.index) ∧ reads=observed.requests.length ∧
        out.source=rest ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=drawLabel 15 ∧
        (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
        charge ≤ completeBound 174 H A budget+(budget+1)*GuardedReferenceExecution.guardCost 174 := by
  let old := eraseState initial
  let observed := PhysicalDrawSequenceProgram.batch fuel (bounds a positive) initial.source
  let budget := instructionBound n L fuel
  obtain ⟨ext,regs,hrep,hbody⟩ := natural_epoch positive rows level trials old.source
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) regs [] observed.suffix (drawLabel 15)
  have trace : NaturalRun program (steps a positive fuel initial.source) old
      (observed.requests.map Event.request) final := by
    rw [at_entry old hp empty hn]
    exact hbody
  have halt : tickNatural program final=none := by
    simp [final,state,tickNatural,program,drawLabel,PhysicalDrawSequenceProgram.program,ReferenceProgramLabels.instruction]
  obtain ⟨q,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace halt
  have hsteps : steps a positive fuel initial.source ≤ budget := steps_le a positive fuel initial.source
  have hrun := GuardedReferenceExecution.execute_eq hr hstop (budget+1) 0 (by omega)
  rw [GuardedReferenceExecution.count_reads] at hrun
  dsimp only
  rw [RetainedDrawTrees.sampleTape,PhysicalEpochDraws.epoch_run]
  unfold PhysicalEpochDraws.checkedValues
  dsimp only
  have base : q+(attempt program out).operations ≤ completeBound 174 H A budget :=
    hcharge.trans (by unfold completeBound runBound stepBound; gcongr)
  have guard := Nat.mul_le_mul_right (GuardedReferenceExecution.guardCost 174) (Nat.add_le_add_right hsteps 1)
  by_cases enough : observed.requests.length ≤ initial.source.length
  · have enough' : (PhysicalDrawSequenceProgram.batch fuel
        (PhysicalEpochDraws.epochBounds L positive (Fintype.card ↥(remainingSet a))) initial.source).requests.length ≤
        initial.source.length := enough
    rw [ite_eq_left enough] at hrun
    rw [ite_eq_left enough']
    refine ⟨out,_,hrun,?_,rfl,Nat.zero_add _,htape,?_,?_,⟨ext,?_⟩,?_⟩
    · rw [hout]; exact hrep
    · rw [hout]; rfl
    · rw [hout]; rfl
    · rw [hout]; rfl
    · simpa only [Nat.zero_add] using Nat.add_le_add base guard
  · have enough' : ¬ (PhysicalDrawSequenceProgram.batch fuel
        (PhysicalEpochDraws.epochBounds L positive (Fintype.card ↥(remainingSet a))) initial.source).requests.length ≤
        initial.source.length := enough
    rw [ite_eq_right enough] at hrun
    rw [ite_eq_right enough']
    exact hrun

end DirectedFlowCutGap.RetainedEpochFromMasks
