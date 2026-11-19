import DirectedFlowCutGap.CandidateFamilyData

/-! Refresh the stored candidate family and sum its retained mass on the same heap. -/

namespace DirectedFlowCutGap.CandidateRefreshProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open EncodedCandidateCapacity (Input)
open CandidateEnumeration (Node Network)
open CandidateFamilyProgram (Shared StateAt)
open CandidateFamilyData (familyWords active_feasible family_data family_width)
open EpochActiveFromMaskProgram (labelPair flatSteps)
open GraphWalkExtension (EdgeList)
open RetainedDemandEraseProgram (RowsAt)
open RetainedMassTableProgram (TableAt DataRows pairOrder)

def familyLabel (pc : Fin 3975) : Fin 4331 := ⟨64+pc.val,by omega⟩
def flatLabel (pc : Fin 18) : Fin 4331 := ⟨4039+pc.val,by omega⟩
def massLabel (pc : Fin 274) : Fin 4331 := ⟨4057+pc.val,by omega⟩

def program : Program 4331 := fun pc =>
  if pc.val<64 then
    match pc.val with
    | 0 => .call (familyLabel 0) 1 .r2
    | 1 => .call 16 2 .r1
    | 2 => .move .r0 .r1 5
    | 5 => .move .r1 .r2 6
    | 6 => .field .r2 .r3 false 7
    | 7 => .call (massLabel 0) 8 .r3
    | 8 => .make .r3 (.pair .r1 .r3) 9
    | 16 => .move .r0 .r1 17
    | 17 => .call (flatLabel 0) 18 .r3
    | 18 => .ret .r3
    | _ => .halt
  else if h : pc.val<4039 then
    if pc.val=67 then .ret .r3
    else ReferenceProgramLabels.instruction familyLabel (CandidateFamilyProgram.program ⟨pc.val-64,by omega⟩)
  else if h : pc.val<4057 then
    if pc.val=4047 then .ret .r3
    else ReferenceProgramLabels.instruction flatLabel (FlattenDemandMaskProgram.program ⟨pc.val-4039,by omega⟩)
  else if pc.val=4080 then .ret .r3
  else ReferenceProgramLabels.instruction massLabel (RetainedMassTableProgram.program ⟨pc.val-4057,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 4331

def Output {n : ℕ} (heap : NaturalHeap) (root : ℕ) (c : Family n) (optimal : ℕ) (words : List (List Bits)) : Prop :=
  ∃ table mass bits,heap[root]?=some (.pair table mass) ∧ TableAt heap table words ∧
    DataRows c words ∧ BoolList heap mass bits ∧ value bits=optimal

def instructionBound (n L vertices grid scale : ℕ) : ℕ :=
  CandidateFamilyProgram.instructionBound n L vertices grid scale+flatSteps n+
    RetainedMassTableProgram.instructionBudget (n*n) n (max grid (L+1).size)+13

private theorem family_slots (pc : Fin 3975) (h : CandidateFamilyProgram.program pc≠.halt) :
    program (familyLabel pc)=ReferenceProgramLabels.instruction familyLabel (CandidateFamilyProgram.program pc) := by
  by_cases stop : pc.val=3
  · have eq : pc=3 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,familyLabel,show ¬64+pc.val<64 by omega,show 64+pc.val<4039 by omega,show 64+pc.val≠67 by omega]

private theorem flat_slots (pc : Fin 18) (h : FlattenDemandMaskProgram.program pc≠.halt) :
    program (flatLabel pc)=ReferenceProgramLabels.instruction flatLabel (FlattenDemandMaskProgram.program pc) := by
  by_cases stop : pc.val=8
  · have eq : pc=8 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,flatLabel,show ¬4039+pc.val<64 by omega,show ¬4039+pc.val<4039 by omega,
      show 4039+pc.val<4057 by omega,show 4039+pc.val≠4047 by omega]

private theorem mass_slots (pc : Fin 274) (h : RetainedMassTableProgram.program pc≠.halt) :
    program (massLabel pc)=ReferenceProgramLabels.instruction massLabel (RetainedMassTableProgram.program pc) := by
  by_cases stop : pc.val=23
  · have eq : pc=23 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,massLabel,show ¬4057+pc.val<64 by omega,show ¬4057+pc.val<4039 by omega,
      show ¬4057+pc.val<4057 by omega,show 4057+pc.val≠4080 by omega]

private theorem flatten_call {n : ℕ} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ}
    (active : RowsAt heap r.b a) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (RetainedEpochFromMasks.flags a) ∧
      NaturalRun program (flatSteps n+5) (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r1 root) [] tape 2) := by
  let args := r.set .r0 r.b
  let frame : Frame ℕ 4331 := ⟨2,.r1,r⟩
  have enter : NaturalRun program 2 (state heap r [] tape 1) [] (state heap args [frame] tape 17) := by
    apply ReferenceProgramSteps.sound
    cases r
    rfl
  obtain ⟨ext,root,_,rep,body⟩ := FlattenDemandMaskProgram.natural_trace (r:=args) active tape
  have invoke := ReferenceProgramInvocation.call flatLabel flat_slots (caller:=17) (continuation:=18)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [frame] body
  let done := state (heap++ext) (args.set .r3 root) [frame] tape 18
  have work : NaturalRun program (flatSteps n+2) (state heap args [frame] tape 17) [] done := by
    simpa [done,Registers.get,Registers.set,flatSteps] using invoke
  have ret : tickNatural program done=some ⟨state (heap++ext) (r.set .r1 root) [] tape 2,[],0⟩ := by
    simp [done,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,rep,?_⟩
  have count : 2+(flatSteps n+2+1)=flatSteps n+5 := by omega
  rw [← count]
  exact append_run enter (append_run work (.step ret (.done _)))

private theorem rows_extend {n : ℕ} {heap : NaturalHeap} {addr : ℕ} {a : PairFlags n}
    (h : RowsAt heap addr a) (ext : NaturalHeap) : RowsAt (heap++ext) addr a := by
  obtain ⟨refs,spine,rows⟩ := h
  exact ⟨refs,BinaryPointerListRead.pointerList_extend spine ext,rows.imp (fun _ _ w => boolList_extend w ext)⟩

set_option maxHeartbeats 2600000 in
theorem natural_refresh {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {D : Input n}
    {demands : Finset (Pair n)} (s : Code D.graph demands L) (removed : D.removed=s.data.cut)
    {vertices grid scale : Bits} (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (keys : EdgeList heap r.a ((pairOrder n).map labelPair)) (active : RowsAt heap r.b s.data.remaining)
    (shared : Shared heap r.c D vertices grid) (current : StateAt heap r.d D scale)
    (size : value vertices=n) (gridValue : value grid=L) (scaleValue : value scale=s.data.scale) (tape : Bits) :
    let cache := refresh (tabulatedOptimizer positive (ResidualSearch.Enumeration.fin n) E) s
    let words := familyWords D s.data.remaining (4*s.data.scale) grid EN E
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),Output (heap++ext) root cache.candidate cache.optimal words ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 9) ∧
      k ≤ instructionBound n L vertices.length grid.length scale.length := by
  let cache := refresh (tabulatedOptimizer positive (ResidualSearch.Enumeration.fin n) E) s
  let words := familyWords D s.data.remaining (4*s.data.scale) grid EN E
  have cutEq : D.cut=cutSet s.data.cut := by
    unfold EncodedCandidateCapacity.Input.cut cutSet
    rw [removed]
  have feasible := active_feasible D s cutEq
  obtain ⟨ef,args0,table,k,candidate,body,familyBound⟩ := CandidateFamilyProgram.natural_family positive feasible EN E
    keys active shared current size gridValue scaleValue tape
  let mid := heap++ef
  let familyArgs := r.set .r2 table
  have familyRun : NaturalRun program (k+2) (state heap r [] tape 0) [] (state mid familyArgs [] tape 1) := by
    have invoke := ReferenceProgramInvocation.call familyLabel family_slots (caller:=0) (continuation:=1)
      (dst:=.r2) (result:=.r3) (by rfl) (by rfl) [] body
    simpa only [mid,familyArgs,Registers.get,Registers.set] using invoke
  obtain ⟨et,flags,flagRep,flatRun⟩ := flatten_call (r:=familyArgs) (rows_extend active ef) tape
  let grown := mid++et
  let flagArgs := familyArgs.set .r1 flags
  obtain ⟨cut,scaleRoot,atState,cutRep,_⟩ := current
  let massArgs : Registers ℕ := ⟨flags,table,cut,r.d⟩
  have atCurrent : grown[r.d]?=some (.pair cut scaleRoot) := lookup_extend (lookup_extend atState ef) et
  have setup : NaturalRun program 3 (state grown flagArgs [] tape 2) [] (state grown massArgs [] tape 7) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atCurrent,flagArgs,familyArgs,massArgs]
  have exactData : DataRows cache.candidate words := family_data D s cutEq grid gridValue positive EN E
  have storedCut : BoolList grown massArgs.c s.data.cut.toList := by
    have stored := boolList_extend (boolList_extend cutRep ef) et
    simpa only [removed] using stored
  have tableRep : TableAt grown massArgs.b words := RoundInputPackProgram.weights_extend candidate et
  have length : (RetainedEpochFromMasks.flags s.data.remaining).length=words.length := by
    rw [RetainedMassTableProgram.data_length exactData]
    simp only [RetainedEpochFromMasks.flags,List.length_map,RetainedMassTableProgram.pairOrder_length]
  have aligned : ∀ x∈words,x.length=s.data.cut.toList.length := by
    simpa only [Vector.length_toList] using RetainedMassTableProgram.data_aligned exactData
  obtain ⟨em,mass,massRep,massBody⟩ := RetainedMassTableProgram.natural_trace (r:=massArgs)
    flagRep tableRep storedCut length aligned tape
  let m := RetainedMassTableProgram.steps s.data.cut.toList (RetainedEpochFromMasks.flags s.data.remaining) words+1
  have massRun : NaturalRun program (m+2) (state grown massArgs [] tape 7) []
      (state (grown++em) (massArgs.set .r3 mass) [] tape 8) := by
    have invoke := ReferenceProgramInvocation.call massLabel mass_slots (caller:=7) (continuation:=8)
      (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [] massBody
    simpa only [m,Registers.get,Registers.set] using invoke
  let finalHeap := grown++em
  let root := finalHeap.length
  let cell : Cell ℕ := .pair table mass
  have pack : NaturalRun program 1 (state finalHeap (massArgs.set .r3 mass) [] tape 8) []
      (state (finalHeap++[cell]) (massArgs.set .r3 root) [] tape 9) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,cell,massArgs,root]
  have valueMass : value (RetainedMassTableProgram.sum s.data.cut.toList
      (RetainedEpochFromMasks.flags s.data.remaining) words)=cache.optimal :=
    (RetainedMassTableProgram.mass_value cache.candidate s.data.remaining s.data.cut exactData).trans
      (EncodedRoundingState.mass_value s.data.remaining s.data.cut cache.candidate)
  have represented : Output (finalHeap++[cell]) root cache.candidate cache.optimal words :=
    ⟨table,mass,_,by simp [root,cell],RoundInputPackProgram.weights_extend (RoundInputPackProgram.weights_extend tableRep em) [cell],
      exactData,boolList_extend massRep [cell],valueMass⟩
  have massBound : m≤RetainedMassTableProgram.instructionBudget (n*n) n (max grid.length (L+1).size) := by
    have h := RetainedMassTableProgram.steps_le words (RetainedEpochFromMasks.flags s.data.remaining) s.data.cut.toList
      (max grid.length (L+1).size) aligned (family_width D s.data.remaining (4*s.data.scale) grid EN E)
    simpa only [m,RetainedMassTableProgram.data_length exactData,Vector.length_toList] using h
  refine ⟨ef++et++em++[cell],massArgs,root,k+2+(flatSteps n+5+(3+(m+2+1))),?_,?_,?_⟩
  · simpa only [cache,words,finalHeap,grown,mid,List.append_assoc] using represented
  · simpa only [finalHeap,grown,mid,List.append_assoc,List.nil_append] using
      append_run familyRun (append_run flatRun (append_run setup (append_run massRun pack)))
  · unfold instructionBound
    omega

private theorem at_entry (s : NaturalState 4331) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [ReferenceProgramInvocation.state]

theorem physical_refresh {n L H A : ℕ} {D : Input n} {demands : Finset (Pair n)} (s : Code D.graph demands L)
    (removed : D.removed=s.data.cut) {vertices grid scale : Bits} (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (initial : BitState 4331) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (keys : EdgeList (eraseState initial).heap (eraseState initial).registers.a ((pairOrder n).map labelPair))
    (active : RowsAt (eraseState initial).heap (eraseState initial).registers.b s.data.remaining)
    (shared : Shared (eraseState initial).heap (eraseState initial).registers.c D vertices grid)
    (current : StateAt (eraseState initial).heap (eraseState initial).registers.d D scale)
    (size : value vertices=n) (gridValue : value grid=L) (scaleValue : value scale=s.data.scale) :
    let cache := refresh (tabulatedOptimizer positive (ResidualSearch.Enumeration.fin n) E) s
    let words := familyWords D s.data.remaining (4*s.data.scale) grid EN E
    ∃ (paid k : ℕ) (out : BitState 4331),Run program k paid initial [] out ∧
      Output (eraseState out).heap (eraseState out).registers.d cache.candidate cache.optimal words ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ out.pc=9 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧ (attempt program out).result=none ∧
      paid+(attempt program out).operations ≤ completeBound 4331 H A (instructionBound n L vertices.length grid.length scale.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,k,rep,body,within⟩ := natural_refresh s removed positive EN E keys active shared current
    size gridValue scaleValue old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 9
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have run : NaturalRun program k old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have halt : tickNatural program final=none := rfl
  obtain ⟨paid,out,actual,finalState,stopped,cost,tape⟩ := terminating_simulation bounded run halt
  refine ⟨paid,k,out,actual,?_,tape,?_,?_,⟨ext,?_⟩,stopped,cost.trans ?_⟩
  · rw [finalState]; exact rep
  · rw [finalState]; rfl
  · exact congrArg (fun s : NaturalState 4331 => s.pc) finalState
  · rw [finalState]; rfl
  · exact SupportSearchEncoding.complete_mono _ _ _ _ _ within

end DirectedFlowCutGap.CandidateRefreshProgram
