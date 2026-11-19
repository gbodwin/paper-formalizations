import DirectedFlowCutGap.RoundInputPackProgram
import DirectedFlowCutGap.RoundWeightRowProgram

/-! Use the original pair selected by the epoch to run its physical cut and update. -/

namespace DirectedFlowCutGap.EpochSelectedRoundProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open ConcreteExpressionProgram (append_run)
open EpochActiveFromMaskProgram (labelPair)
open GraphWalkExtension (Edge edge_extend)
open RetainedMassTableProgram (DataRows)
open RoundInputPackProgram (Environment environment_extend)

def gridLabel (pc : Fin 104) : Fin 2451 := ⟨64+pc.val,by omega⟩
def rowLabel (pc : Fin 175) : Fin 2451 := ⟨168+pc.val,by omega⟩
def wordLabel (pc : Fin 45) : Fin 2451 := ⟨343+pc.val,by omega⟩
def packLabel (pc : Fin 81) : Fin 2451 := ⟨388+pc.val,by omega⟩
def roundLabel (pc : Fin 1982) : Fin 2451 := ⟨469+pc.val,by omega⟩

def roundHalt : Fin 1982 := PhysicalSampledRoundProgram.updateLabel 5

def program : Program 2451 := fun pc =>
  if pc.val<64 then
    match pc.val with
    | 0 => .call (gridLabel 0) 1 .r1
    | 1 => .call 24 2 .r2
    | 2 => .call (packLabel 0) 3 .r3
    | 3 => .field .r0 .r3 false 4
    | 4 => .field .r2 .r3 true 5
    | 5 => .field .r1 .r0 true 6
    | 6 => .field .r0 .r0 false 7
    | 7 => .field .r3 .r2 true 8
    | 8 => .field .r2 .r2 false 9
    | 9 => .call (roundLabel 0) 10 .r3
    | 24 => .call 32 25 .r1
    | 25 => .field .r2 .r2 true 26
    | 26 => .field .r0 .r3 false 27
    | 27 => .field .r0 .r0 false 28
    | 28 => .call (wordLabel 0) 29 .r3
    | 29 => .ret .r3
    | 32 => .field .r1 .r2 false 33
    | 33 => .field .r2 .r3 true 34
    | 34 => .field .r2 .r2 true 35
    | 35 => .field .r2 .r2 false 36
    | 36 => .call (rowLabel 0) 37 .r3
    | 37 => .ret .r3
    | _ => .halt
  else if h : pc.val<168 then
    if pc.val=65 then .ret .r3
    else ReferenceProgramLabels.instruction gridLabel (EpochGridLookupProgram.program ⟨pc.val-64,by omega⟩)
  else if h : pc.val<343 then
    if pc.val=169 then .ret .r3
    else ReferenceProgramLabels.instruction rowLabel (RoundWeightRowProgram.program ⟨pc.val-168,by omega⟩)
  else if h : pc.val<388 then
    if pc.val=344 then .ret .r3
    else ReferenceProgramLabels.instruction wordLabel (RoundWordTablesProgram.program ⟨pc.val-343,by omega⟩)
  else if h : pc.val<469 then
    if pc.val=451 then .ret .r3
    else ReferenceProgramLabels.instruction packLabel (RoundInputPackProgram.program ⟨pc.val-388,by omega⟩)
  else if pc.val=2054 then .ret .r3
  else ReferenceProgramLabels.instruction roundLabel
    (PhysicalSampledRoundProgram.program ⟨pc.val-469,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 2451
abbrev enumeration := IntegralNetworkFlow.ResidualSearch.Enumeration.fin

def config (heap : NaturalHeap) (root n : ℕ) : Prop :=
  ∃ vertices one,heap[root]?=some (.pair vertices one) ∧ BoolList heap vertices n.bits ∧ BoolList heap one [true]

private theorem config_extend {heap : NaturalHeap} {root n : ℕ} (h : config heap root n) (ext : NaturalHeap) :
    config (heap++ext) root n := by
  obtain ⟨v,one,read,vRep,oneRep⟩ := h
  exact ⟨v,one,lookup_extend read ext,boolList_extend vRep ext,boolList_extend oneRep ext⟩

def steps {n : ℕ} (adj : PairFlags n) (d : Data n) (p : Pair n)
    (cells : List (Pair n×Bits)) (words : List (List Bits)) : ℕ :=
  EpochGridLookupProgram.steps p cells+RoundWeightRowProgram.steps p+
    RoundWordTablesProgram.steps (RoundWeightRowProgram.selected p words)+RoundInputPackProgram.steps p+
    PhysicalSampledRoundProgram.steps (enumeration n) adj d p p.1.val.bits (fun i => i.val.bits)
      (EpochGridLookupProgram.word p cells) words+27

private theorem grid_slots (pc : Fin 104) (h : EpochGridLookupProgram.program pc≠.halt) :
    program (gridLabel pc)=ReferenceProgramLabels.instruction gridLabel (EpochGridLookupProgram.program pc) := by
  by_cases stop : pc.val=1
  · have eq : pc=1 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,gridLabel,show ¬64+pc.val<64 by omega,show 64+pc.val<168 by omega,show 64+pc.val≠65 by omega]

private theorem row_slots (pc : Fin 175) (h : RoundWeightRowProgram.program pc≠.halt) :
    program (rowLabel pc)=ReferenceProgramLabels.instruction rowLabel (RoundWeightRowProgram.program pc) := by
  by_cases stop : pc.val=1
  · have eq : pc=1 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,rowLabel,show ¬168+pc.val<64 by omega,show ¬168+pc.val<168 by omega,
      show 168+pc.val<343 by omega,show 168+pc.val≠169 by omega]

private theorem word_slots (pc : Fin 45) (h : RoundWordTablesProgram.program pc≠.halt) :
    program (wordLabel pc)=ReferenceProgramLabels.instruction wordLabel (RoundWordTablesProgram.program pc) := by
  by_cases stop : pc.val=1
  · have eq : pc=1 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,wordLabel,show ¬343+pc.val<64 by omega,show ¬343+pc.val<168 by omega,
      show ¬343+pc.val<343 by omega,show 343+pc.val<388 by omega,show 343+pc.val≠344 by omega]

private theorem pack_slots (pc : Fin 81) (h : RoundInputPackProgram.program pc≠.halt) :
    program (packLabel pc)=ReferenceProgramLabels.instruction packLabel (RoundInputPackProgram.program pc) := by
  by_cases stop : pc.val=63
  · have eq : pc=63 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,packLabel,show ¬388+pc.val<64 by omega,show ¬388+pc.val<168 by omega,
      show ¬388+pc.val<343 by omega,show ¬388+pc.val<388 by omega,
      show 388+pc.val<469 by omega,show 388+pc.val≠451 by omega]

private theorem round_slots (pc : Fin 1982) (h : PhysicalSampledRoundProgram.program pc≠.halt) :
    program (roundLabel pc)=ReferenceProgramLabels.instruction roundLabel (PhysicalSampledRoundProgram.program pc) := by
  by_cases stop : pc.val=1585
  · have eq : pc=roundHalt := Fin.ext stop
    subst pc
    have stopped : PhysicalSampledRoundProgram.program roundHalt=.halt := by
      simp [roundHalt,PhysicalSampledRoundProgram.updateLabel,PhysicalSampledRoundProgram.program,
        RoundStateUpdateProgram.program,ReferenceProgramLabels.instruction]
    exact (h stopped).elim
  · simp [program,roundLabel,show ¬469+pc.val<64 by omega,show ¬469+pc.val<168 by omega,
      show ¬469+pc.val<343 by omega,show ¬469+pc.val<388 by omega,show ¬469+pc.val<469 by omega,
      show 469+pc.val≠2054 by omega]

set_option maxHeartbeats 2200000 in
private theorem tables_call {n : ℕ} {p : Pair n} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {d : Data n} {words : List (List Bits)} (key : Edge heap r.a (labelPair p))
    (parameters : config heap r.c n) (env : Environment heap r.d (enumeration n) adj d words)
    (data : DataRows d.weights words) (tape : Bits) :
    ∃ ext root,RoundWordTablesProgram.Output (heap++ext) root (List.finRange n |>.map fun i => i.val.bits)
        (RoundWeightRowProgram.selected p words) ∧
      NaturalRun program (RoundWeightRowProgram.steps p+RoundWordTablesProgram.steps (RoundWeightRowProgram.selected p words)+15)
        (state heap r [] tape 1) [] (state (heap++ext) (r.set .r2 root) [] tape 2) := by
  obtain ⟨count,one,atConfig,countRep,oneRep⟩ := parameters
  obtain ⟨g,s,atEnv,⟨e,m,atGraph,enum,matrix⟩,
    ⟨masks,weightContext,weights,free,atState,atContext,maskRep,tableRep,freeRep⟩⟩ := env
  let outer : Frame ℕ 2451 := ⟨2,.r2,r⟩
  let caller : Frame ℕ 2451 := ⟨25,.r1,r⟩
  let atCount := r.set .r1 count
  let rowArgs := atCount.set .r2 weights
  have setup : NaturalRun program 3 (state heap r [] tape 1) [] (state heap atCount [caller,outer] tape 33) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atConfig,atCount,caller,outer]
  have load : NaturalRun program 3 (state heap atCount [caller,outer] tape 33) []
      (state heap rowArgs [caller,outer] tape 36) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atEnv,atState,atContext,rowArgs,atCount]
  obtain ⟨er,rowRoot,rowRep,rowBody⟩ := RoundWeightRowProgram.natural_row (r:=rowArgs) key countRep tableRep data tape
  have rowRun := ReferenceProgramInvocation.call rowLabel row_slots (caller:=36) (continuation:=37)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [caller,outer] rowBody
  let mid := heap++er
  let selected := r.set .r1 rowRoot
  let rowStop := state mid (rowArgs.set .r3 rowRoot) [caller,outer] tape 37
  have rowRet : tickNatural program rowStop=some ⟨state mid selected [outer] tape 25,[],0⟩ := by
    simp [rowStop,program,ReferenceProgramInvocation.state,tickNatural,Registers.get,Registers.set,caller,selected]
  let zipArgs : Registers ℕ := ⟨e,rowRoot,one,r.d⟩
  have configAt : mid[r.c]?=some (.pair count one) := lookup_extend atConfig er
  have envAt : mid[r.d]?=some (.pair g s) := lookup_extend atEnv er
  have graphAt : mid[g]?=some (.pair e m) := lookup_extend atGraph er
  have prep : NaturalRun program 3 (state mid selected [outer] tape 25) [] (state mid zipArgs [outer] tape 28) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      configAt,envAt,graphAt,selected,zipArgs]
  let labels := (List.finRange n).map fun i => i.val.bits
  let chosen := RoundWeightRowProgram.selected p words
  have len : chosen.length=labels.length := by
    have lengths := congrArg List.length (RoundWeightRowProgram.selected_values data p)
    simpa [labels,chosen] using lengths
  have vertices : GraphDiscoveryProgram.Vertices mid zipArgs.a labels := GraphDiscoveryProgram.vertices_extend enum er
  obtain ⟨ez,result,rep,zipBody⟩ := RoundWordTablesProgram.natural_tables (r:=zipArgs) vertices rowRep
    (boolList_extend oneRep er) len tape
  have zipRun := ReferenceProgramInvocation.call wordLabel word_slots (caller:=28) (continuation:=29)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [outer] zipBody
  let final := state (mid++ez) (zipArgs.set .r3 result) [outer] tape 29
  have ret : tickNatural program final=some ⟨state (mid++ez) (r.set .r2 result) [] tape 2,[],0⟩ := by
    simp [final,program,ReferenceProgramInvocation.state,tickNatural,Registers.get,Registers.set,outer]
  have rowTrace : NaturalRun program (RoundWeightRowProgram.steps p+2) (state heap rowArgs [caller,outer] tape 36) [] rowStop := by
    simpa [rowStop,mid,Registers.get,Registers.set] using rowRun
  have zipTrace : NaturalRun program (RoundWordTablesProgram.steps chosen+2)
      (state mid zipArgs [outer] tape 28) [] final := by
    simpa [final,Registers.get,Registers.set] using zipRun
  refine ⟨er++ez,result,?_,?_⟩
  · simpa only [mid,labels,chosen,List.append_assoc] using rep
  · let a := RoundWeightRowProgram.steps p
    let b := RoundWordTablesProgram.steps chosen
    have count : 3+(3+(a+2+(3+(b+2+1)+1)))=a+b+15 := by omega
    change NaturalRun program (a+b+15) _ [] _
    rw [← count]
    simpa only [rowStop,mid,final,a,b,List.append_assoc,List.nil_append,Nat.zero_add,Nat.add_assoc] using
      append_run setup (append_run load (append_run rowTrace (.step rowRet (append_run prep
        (append_run zipTrace (.step ret (.done _)))))))

set_option maxHeartbeats 2400000 in
theorem natural_round {n : ℕ} {p : Pair n} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {d : Data n} {words : List (List Bits)} {cells : List (Pair n×Bits)} (key : Edge heap r.a (labelPair p))
    (grid : EpochGridLookupProgram.Table heap r.b cells) (parameters : config heap r.c n)
    (env : Environment heap r.d (enumeration n) adj d words) (data : DataRows d.weights words) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (result : ℕ),
      RoundStateUpdateProgram.UpdatedAt (heap++ext) result (EncodedRoundingState.roundData d p
        (PhysicalSampledRoundProgram.cut (enumeration n) adj d p (EpochGridLookupProgram.word p cells))).1 ∧
      NaturalRun program (steps adj d p cells words) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 result) [] tape 10) := by
  let level := EpochGridLookupProgram.word p cells
  let chosen := RoundWeightRowProgram.selected p words
  obtain ⟨eg,j,levelRep,gridBody⟩ := EpochGridLookupProgram.natural_lookup key grid tape
  let mid := heap++eg
  let ready := r.set .r1 j
  have gridRun : NaturalRun program (EpochGridLookupProgram.steps p cells+2) (state heap r [] tape 0) []
      (state mid ready [] tape 1) := by
    have trace := ReferenceProgramInvocation.call gridLabel grid_slots (caller:=0) (continuation:=1)
      (dst:=.r1) (result:=.r3) (by rfl) (by rfl) [] gridBody
    simpa [ready,mid,Registers.get,Registers.set] using trace
  obtain ⟨et,table,tables,tableRun⟩ := tables_call (r:=ready) (edge_extend key eg) (config_extend parameters eg)
    (environment_extend env eg) data tape
  let tablesHeap := mid++et
  let args := ready.set .r2 table
  obtain ⟨ep,packedRegs,bundle,packed,packBody⟩ := RoundInputPackProgram.natural_pack (r:=args)
    (edge_extend (edge_extend key eg) et) (boolList_extend levelRep et) tables
    (RoundWeightRowProgram.selected_values data p) (environment_extend (environment_extend env eg) et) tape
  let grown := tablesHeap++ep
  let prepared := args.set .r3 bundle
  have packRun : NaturalRun program (RoundInputPackProgram.steps p+2) (state tablesHeap args [] tape 2) []
      (state grown prepared [] tape 3) := by
    have trace := ReferenceProgramInvocation.call packLabel pack_slots (caller:=2) (continuation:=3)
      (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [] packBody
    simpa [grown,tablesHeap,mid,prepared,Registers.get,Registers.set] using trace
  obtain ⟨inputs,contexts,enum,target,cut,update,atBundle,atInput,atContext,enumRep,targetRep,cutRep,updateRep⟩ := packed
  have bundleAt : grown[bundle]?=some (.pair inputs contexts) := atBundle
  have inputAt : grown[inputs]?=some (.pair enum target) := atInput
  have contextAt : grown[contexts]?=some (.pair cut update) := atContext
  let frontRegs : Registers ℕ := ⟨inputs,target,contexts,bundle⟩
  let roundArgs : Registers ℕ := ⟨enum,target,cut,update⟩
  have first : NaturalRun program 3 (state grown prepared [] tape 3) [] (state grown frontRegs [] tape 6) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      bundleAt,inputAt,prepared,frontRegs]
  have second : NaturalRun program 3 (state grown frontRegs [] tape 6) [] (state grown roundArgs [] tape 9) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      inputAt,contextAt,frontRegs,roundArgs]
  obtain ⟨er,out,outRep,roundBody⟩ := PhysicalSampledRoundProgram.natural_round (r:=roundArgs)
    (enumeration n) adj d p p.1.val.bits (value_bits _) (fun i => i.val.bits) (fun i => value_bits i.val)
    level tape words enumRep targetRep cutRep updateRep data
  have roundRun := ReferenceProgramInvocation.call roundLabel round_slots (caller:=9) (continuation:=10)
    (dst:=.r3) (result:=.r3) (by rfl) (by simp [program,roundLabel,PhysicalSampledRoundProgram.updateLabel]) [] roundBody
  let G := EpochGridLookupProgram.steps p cells
  let R := RoundWeightRowProgram.steps p
  let W := RoundWordTablesProgram.steps chosen
  let P := RoundInputPackProgram.steps p
  let C := PhysicalSampledRoundProgram.steps (enumeration n) adj d p p.1.val.bits (fun i => i.val.bits) level words
  refine ⟨eg++et++ep++er,roundArgs,out.d,?_,?_⟩
  · simpa only [grown,tablesHeap,mid,List.append_assoc] using outRep
  · have trace : NaturalRun program (C+2) (state grown roundArgs [] tape 9) []
        (state (grown++er) (roundArgs.set .r3 out.d) [] tape 10) := by
      simpa only [Registers.get,C] using roundRun
    have count : (G+2)+(R+W+15+((P+2)+(3+(3+(C+2)))))=steps adj d p cells words := by
      simp only [steps,G,R,W,P,C,chosen,level]
      omega
    rw [← count]
    simpa only [mid,tablesHeap,grown,G,R,W,P,C,chosen,level,List.append_assoc,List.nil_append,Nat.add_assoc] using
      append_run gridRun (append_run tableRun (append_run packRun (append_run first (append_run second trace))))

def instructionBound (n rows W S B : ℕ) : ℕ :=
  EpochGridLookupProgram.instructionBound n rows+RoundWeightRowProgram.instructionBound n+
    (n*(8*B+21)+5)+RoundInputPackProgram.instructionBound n+
    PhysicalSampledRoundProgram.instructionBound n W S B+27

theorem steps_le {n W B : ℕ} (adj : PairFlags n) (d : Data n) (p : Pair n) (cells : List (Pair n×Bits))
    (words : List (List Bits)) (data : DataRows d.weights words) (hW : 1≤W) (labels : n.size≤W)
    (hrow : ∀ i : Fin n,(row d.weights p)[i.val].bits.length≤W) (hj : (EpochGridLookupProgram.word p cells).length≤W)
    (stored : ∀ ws∈words,∀ w∈ws,w.length≤B) :
    steps adj d p cells words ≤ instructionBound n cells.length W p.1.val.bits.length B := by
  let level := EpochGridLookupProgram.word p cells
  have labelWidth (i : Fin n) : i.val.bits.length≤W := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le_size i.isLt.le).trans labels
  have scan := IntegerLevelCutProgram.steps_le (enumeration n) adj (row d.weights p) p.1 p.1.val.bits
    (value_bits _) (fun i => i.val.bits) (fun i => value_bits i.val) level hW (labelWidth _) labelWidth hrow hj
  have update := RoundStateUpdateProgram.steps_le d p (PhysicalSampledRoundProgram.cut (enumeration n) adj d p level)
    words data stored
  have round : PhysicalSampledRoundProgram.steps (enumeration n) adj d p p.1.val.bits (fun i => i.val.bits) level words ≤
      PhysicalSampledRoundProgram.instructionBound n W p.1.val.bits.length B := by
    unfold PhysicalSampledRoundProgram.steps PhysicalSampledRoundProgram.instructionBound
    omega
  have rowRead := RoundWeightRowProgram.steps_le p
  have gridRead := EpochGridLookupProgram.steps_le p cells
  have pack := RoundInputPackProgram.steps_le p
  let chosen := RoundWeightRowProgram.selected p words
  have length : chosen.length=n := by
    simpa [chosen] using congrArg List.length (RoundWeightRowProgram.selected_values data p)
  have tables := RoundWordTablesProgram.steps_le chosen B (stored chosen (RoundWeightRowProgram.selected_mem data p))
  rw [length] at tables
  unfold steps instructionBound
  change EpochGridLookupProgram.steps p cells+RoundWeightRowProgram.steps p+RoundWordTablesProgram.steps chosen+
    RoundInputPackProgram.steps p+PhysicalSampledRoundProgram.steps (enumeration n) adj d p p.1.val.bits
      (fun i => i.val.bits) level words+27 ≤ _
  omega

private theorem at_entry (s : NaturalState 2451) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [ReferenceProgramInvocation.state]

theorem physical_round {n H A W B : ℕ} (adj : PairFlags n) (d : Data n) (p : Pair n) (cells : List (Pair n×Bits))
    (words : List (List Bits)) (data : DataRows d.weights words) (hW : 1≤W) (labels : n.size≤W)
    (hrow : ∀ i : Fin n,(row d.weights p)[i.val].bits.length≤W) (hj : (EpochGridLookupProgram.word p cells).length≤W)
    (widths : ∀ ws∈words,∀ w∈ws,w.length≤B) (initial : BitState 2451)
    (bound : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (key : Edge (eraseState initial).heap (eraseState initial).registers.a (labelPair p))
    (grid : EpochGridLookupProgram.Table (eraseState initial).heap (eraseState initial).registers.b cells)
    (parameters : config (eraseState initial).heap (eraseState initial).registers.c n)
    (env : Environment (eraseState initial).heap (eraseState initial).registers.d (enumeration n) adj d words) :
    ∃ paid out,Run program (steps adj d p cells words) paid initial [] out ∧
      RoundStateUpdateProgram.UpdatedAt (eraseState out).heap (eraseState out).registers.d
        (EncodedRoundingState.roundData d p (PhysicalSampledRoundProgram.cut (enumeration n) adj d p
          (EpochGridLookupProgram.word p cells))).1 ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ out.pc=10 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧ (attempt program out).result=none ∧
      paid+(attempt program out).operations ≤ completeBound 2451 H A
        (instructionBound n cells.length W p.1.val.bits.length B) := by
  let old := eraseState initial
  obtain ⟨ext,args,result,rep,run⟩ := natural_round key grid parameters env data old.source
  let final := state (old.heap++ext) (args.set .r3 result) [] old.source 10
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have body : NaturalRun program (steps adj d p cells words) old [] final := by
    rw [at_entry old hp empty hn]
    exact run
  have stop : tickNatural program final=none := rfl
  obtain ⟨paid,out,actual,resultState,halted,cost,tape⟩ := terminating_simulation bound body stop
  refine ⟨paid,out,actual,?_,tape,?_,?_,⟨ext,?_⟩,halted,cost.trans ?_⟩
  · rw [resultState]; exact rep
  · rw [resultState]; rfl
  · exact congrArg (fun s : NaturalState 2451 => s.pc) resultState
  · rw [resultState]; rfl
  · exact SupportSearchEncoding.complete_mono _ _ _ _ _ (steps_le adj d p cells words data hW labels hrow hj widths)

/-- These are the exact Boolean flags of the retained integer controller at its sampled cell. -/
theorem cut_of_epoch {n L : ℕ} (adj : PairFlags n) (d : Data n) (p : Pair n) (a : PairFlags n)
    (positive : 0<L) (tape : RetainedTapeInput.Tape L a) (words : List Bits)
    (samples : words.map value=PhysicalEpochDraws.cellValues L (Fintype.card ↥(remainingSet a)) tape.2) :
    PhysicalSampledRoundProgram.cut (enumeration n) adj d p
      (EpochGridLookupProgram.word p ((RetainedTapeInput.activeList a).zip words))=
    (EncodedRoundingInput.cutOracle (enumeration n) adj positive).cut (row d.weights p) p.1
      ((RetainedTapeInput.materialize positive a tape).cell p) := by
  unfold PhysicalSampledRoundProgram.cut EncodedRoundingInput.cutOracle
  rw [EpochGridLookupProgram.word_value a positive tape words samples]

end DirectedFlowCutGap.EpochSelectedRoundProgram
