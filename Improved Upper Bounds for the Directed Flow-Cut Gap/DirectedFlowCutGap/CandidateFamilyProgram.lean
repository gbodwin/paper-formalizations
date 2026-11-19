import DirectedFlowCutGap.CandidateFamilyScanProgram
import DirectedFlowCutGap.ZeroWeightRowProgram

/-! Build the active flags and shared words from stored state, then solve the whole family. -/

namespace DirectedFlowCutGap.CandidateFamilyProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow CandidateClosureProvider
open ConcreteExpressionProgram (append_run)
open EncodedCandidateCapacity (Input)
open CandidateEnumeration (Node Network)
open CandidateDemandRowProgram (GraphSizeAt graph_extend)
open EpochActiveFromMaskProgram (labelPair flatSteps)
open GraphWalkExtension (EdgeList edgeList_extend)
open RetainedDemandEraseProgram (RowsAt)
open RetainedMassTableProgram (TableAt pairOrder)
open PathCostMaterialization (list_extend)

def Shared {n : ℕ} (heap : NaturalHeap) (root : ℕ) (D : Input n) (vertices grid : Bits) : Prop :=
  ∃ graph rest labels gridRoot us,heap[root]?=some (.pair graph rest) ∧ heap[rest]?=some (.pair labels gridRoot) ∧
    GraphSizeAt heap graph D vertices ∧ GraphDiscoveryProgram.Vertices heap labels us ∧ us.length=n ∧ BoolList heap gridRoot grid

def StateAt {n : ℕ} (heap : NaturalHeap) (root : ℕ) (D : Input n) (scale : Bits) : Prop :=
  ∃ mask stored,heap[root]?=some (.pair mask stored) ∧ BoolList heap mask D.removed.toList ∧ BoolList heap stored scale

def capWord (scale : Bits) : Bits := false::false::scale

theorem cap_value (scale : Bits) : value (capWord scale)=4*value scale := by
  simp [capWord,value]
  omega

private theorem shared_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {D : Input n} {vertices grid : Bits}
    (h : Shared heap root D vertices grid) (ext : NaturalHeap) : Shared (heap++ext) root D vertices grid := by
  obtain ⟨g,r,l,j,us,outer,rest,graph,labels,len,word⟩ := h
  exact ⟨g,r,l,j,us,lookup_extend outer ext,lookup_extend rest ext,graph_extend graph ext,
    GraphDiscoveryProgram.vertices_extend labels ext,len,boolList_extend word ext⟩

private theorem state_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {D : Input n} {scale : Bits}
    (h : StateAt heap root D scale) (ext : NaturalHeap) : StateAt (heap++ext) root D scale := by
  obtain ⟨m,s,read,mask,word⟩ := h
  exact ⟨m,s,lookup_extend read ext,boolList_extend mask ext,boolList_extend word ext⟩

def flatLabel (pc : Fin 18) : Fin 3975 := ⟨64+pc.val,by omega⟩
def zeroLabel (pc : Fin 16) : Fin 3975 := ⟨82+pc.val,by omega⟩
def scanLabel (pc : Fin 3877) : Fin 3975 := ⟨98+pc.val,by omega⟩

def program : Program 3975 := fun pc =>
  if pc.val<64 then
    match pc.val with
    | 0 => .call 16 1 .r1
    | 1 => .call 20 2 .r2
    | 2 => .call (scanLabel 0) 3 .r3
    | 16 => .move .r0 .r1 17
    | 17 => .call (flatLabel 0) 18 .r3
    | 18 => .ret .r3
    | 20 => .call 40 21 .r0
    | 21 => .call 48 22 .r1
    | 22 => .field .r2 .r2 false 23
    | 23 => .make .r2 (.pair .r2 .r1) 24
    | 24 => .make .r3 (.pair .r2 .r0) 25
    | 25 => .ret .r3
    | 40 => .field .r0 .r2 true 41
    | 41 => .field .r0 .r0 false 42
    | 42 => .call (zeroLabel 0) 43 .r3
    | 43 => .ret .r3
    | 48 => .field .r0 .r3 true 49
    | 49 => .make .r1 (.flag false) 50
    | 50 => .make .r0 (.pair .r1 .r0) 51
    | 51 => .make .r0 (.pair .r1 .r0) 52
    | 52 => .field .r3 .r3 false 53
    | 53 => .field .r2 .r2 true 54
    | 54 => .field .r2 .r2 true 55
    | 55 => .make .r3 (.pair .r3 .r2) 56
    | 56 => .make .r3 (.pair .r3 .r0) 57
    | 57 => .ret .r3
    | _ => .halt
  else if h : pc.val<82 then
    if pc.val=72 then .ret .r3
    else ReferenceProgramLabels.instruction flatLabel (FlattenDemandMaskProgram.program ⟨pc.val-64,by omega⟩)
  else if h : pc.val<98 then
    if pc.val=84 then .ret .r3
    else ReferenceProgramLabels.instruction zeroLabel (ZeroWeightRowProgram.program ⟨pc.val-82,by omega⟩)
  else if pc.val=99 then .ret .r3
  else ReferenceProgramLabels.instruction scanLabel (CandidateFamilyScanProgram.program ⟨pc.val-98,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 3975

def instructionBound (n L vertices grid scale : ℕ) : ℕ :=
  flatSteps n+ZeroWeightRowProgram.steps n+CandidateFamilyScanProgram.instructionBound n L vertices grid (scale+2)+29

private theorem flat_slots (pc : Fin 18) (h : FlattenDemandMaskProgram.program pc≠.halt) :
    program (flatLabel pc)=ReferenceProgramLabels.instruction flatLabel (FlattenDemandMaskProgram.program pc) := by
  by_cases stop : pc.val=8
  · have eq : pc=8 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,flatLabel,show ¬64+pc.val<64 by omega,show 64+pc.val<82 by omega,show 64+pc.val≠72 by omega]

private theorem zero_slots (pc : Fin 16) (h : ZeroWeightRowProgram.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (ZeroWeightRowProgram.program pc) := by
  by_cases stop : pc.val=2
  · have eq : pc=2 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,zeroLabel,show ¬82+pc.val<64 by omega,show ¬82+pc.val<82 by omega,show 82+pc.val<98 by omega,
      show 82+pc.val≠84 by omega]

private theorem scan_slots (pc : Fin 3877) (h : CandidateFamilyScanProgram.program pc≠.halt) :
    program (scanLabel pc)=ReferenceProgramLabels.instruction scanLabel (CandidateFamilyScanProgram.program pc) := by
  by_cases stop : pc.val=1
  · have eq : pc=1 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,scanLabel,show ¬98+pc.val<64 by omega,show ¬98+pc.val<82 by omega,show ¬98+pc.val<98 by omega,
      show 98+pc.val≠99 by omega]

private theorem flatten_call {n : ℕ} {a : PairFlags n} {heap : NaturalHeap} {r : Registers ℕ}
    (active : RowsAt heap r.b a) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (RetainedEpochFromMasks.flags a) ∧
      NaturalRun program (flatSteps n+5) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r1 root) [] tape 1) := by
  let args := r.set .r0 r.b
  let frame : Frame ℕ 3975 := ⟨1,.r1,r⟩
  have enter : NaturalRun program 2 (state heap r [] tape 0) [] (state heap args [frame] tape 17) := by
    apply ReferenceProgramSteps.sound
    cases r
    rfl
  obtain ⟨ext,root,_,rep,body⟩ := FlattenDemandMaskProgram.natural_trace (r:=args) active tape
  have invoke := ReferenceProgramInvocation.call flatLabel flat_slots (caller:=17) (continuation:=18)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [frame] body
  let done := state (heap++ext) (args.set .r3 root) [frame] tape 18
  have work : NaturalRun program (flatSteps n+2) (state heap args [frame] tape 17) [] done := by
    simpa [done,Registers.get,Registers.set,flatSteps] using invoke
  have ret : tickNatural program done=some ⟨state (heap++ext) (r.set .r1 root) [] tape 1,[],0⟩ := by
    simp [done,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,rep,?_⟩
  have count : 2+(flatSteps n+2+1)=flatSteps n+5 := by omega
  rw [← count]
  exact append_run enter (append_run work (.step ret (.done _)))

private theorem allocated (heap ext : NaturalHeap) (i : ℕ) : (heap++ext)[heap.length+i]?=ext[i]? := by
  rw [List.getElem?_append_right (by omega)]
  have atIndex : heap.length+i-heap.length=i := by omega
  rw [atIndex]

set_option maxHeartbeats 1900000 in
private theorem rest_call {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {D : Input n}
    {vertices grid scale : Bits} (shared : Shared heap r.c D vertices grid) (d : StateAt heap r.d D scale)
    (stack : List (Frame ℕ 3975)) (tape : Bits) :
    ∃ ext root, (∃ g b,(heap++ext)[root]?=some (.pair g b) ∧ CandidateDemandRowProgram.GridAt (heap++ext) g D grid ∧
        BoolList (heap++ext) b (capWord scale)) ∧
      NaturalRun program 11 (state heap r stack tape 21) [] (state (heap++ext) (r.set .r1 root) stack tape 22) := by
  obtain ⟨graph,rest,labels,gridRoot,us,atShared,atRest,graphRep,labelsRep,len,gridRep⟩ := shared
  obtain ⟨mask,weight,atState,maskRep,scaleRep⟩ := d
  let i := heap.length
  let bit : Cell ℕ := .flag false
  let half : Cell ℕ := .pair i weight
  let cap : Cell ℕ := .pair i (i+1)
  let removedGrid : Cell ℕ := .pair mask gridRoot
  let bundle : Cell ℕ := .pair (i+3) (i+2)
  let ext : NaturalHeap := [bit,half,cap,removedGrid,bundle]
  let withBit := heap++[bit]
  let withCap := heap++[bit,half,cap]
  let withGrid := heap++[bit,half,cap,removedGrid]
  let first : Registers ℕ := ⟨weight,i,r.c,r.d⟩
  let second : Registers ℕ := ⟨i+2,i,r.c,mask⟩
  let third : Registers ℕ := ⟨i+2,i,gridRoot,i+3⟩
  let frame : Frame ℕ 3975 := ⟨22,.r1,r⟩
  let saved := frame::stack
  have prep : NaturalRun program 3 (state heap r stack tape 21) [] (state withBit first saved tape 50) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,frame,saved,atState,withBit,first,bit,i]
  have stateAt : withCap[r.d]?=some (.pair mask weight) := lookup_extend atState _
  have shift : NaturalRun program 3 (state withBit first saved tape 50) [] (state withCap second saved tape 53) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,stateAt,withBit,withCap,first,second,half,cap,i,Nat.add_assoc]
  have sharedAt : withCap[r.c]?=some (.pair graph rest) := lookup_extend atShared _
  have restAt : withCap[rest]?=some (.pair labels gridRoot) := lookup_extend atRest _
  have load : NaturalRun program 3 (state withCap second saved tape 53) [] (state withGrid third saved tape 56) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,withCap,withGrid,second,third,sharedAt,restAt,removedGrid,i]
  have finish : NaturalRun program 2 (state withGrid third saved tape 56) []
      (state (heap++ext) (r.set .r1 (i+4)) stack tape 22) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,frame,saved,withGrid,third,ext,bundle,i]
  have read (j : ℕ) : (heap++ext)[i+j]?=ext[j]? := allocated heap ext j
  have falseAt : (heap++ext)[i]?=some (.flag false) := by simpa [ext,bit] using read 0
  refine ⟨ext,i+4,⟨i+3,i+2,?_,?_,?_⟩,append_run prep (append_run shift (append_run load finish))⟩
  · simpa [ext,bundle] using read 4
  · exact ⟨mask,gridRoot,by simpa [ext,removedGrid] using read 3,boolList_extend maskRep _,boolList_extend gridRep _⟩
  · exact .cons (by simpa [ext,cap] using read 2) falseAt
      (.cons (by simpa [ext,half] using read 1) falseAt (boolList_extend scaleRep _))

set_option maxHeartbeats 2000000 in
private theorem context_call {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {D : Input n}
    {vertices grid scale : Bits} (shared : Shared heap r.c D vertices grid) (d : StateAt heap r.d D scale) (tape : Bits) :
    ∃ ext root,CandidateFamilyScanProgram.Context (heap++ext) root D vertices grid (capWord scale) ∧
      NaturalRun program (ZeroWeightRowProgram.steps n+22) (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r2 root) [] tape 2) := by
  obtain ⟨graph,rest,labels,gridRoot,us,atShared,atRest,graphRep,labelsRep,len,gridRep⟩ := shared
  let shared : Shared heap r.c D vertices grid := ⟨graph,rest,labels,gridRoot,us,atShared,atRest,graphRep,labelsRep,len,gridRep⟩
  let outer : Frame ℕ 3975 := ⟨2,.r2,r⟩
  let caller : Frame ℕ 3975 := ⟨21,.r0,r⟩
  let zeroArgs := r.set .r0 labels
  have enter : NaturalRun program 4 (state heap r [] tape 1) [] (state heap zeroArgs [caller,outer] tape 42) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      outer,caller,zeroArgs,atShared,atRest]
  obtain ⟨ez,zr,out,zeros,body⟩ := ZeroWeightRowProgram.natural_zero_row (r:=zeroArgs) labelsRep tape
  have zeroInvoke := ReferenceProgramInvocation.call zeroLabel zero_slots (caller:=42) (continuation:=43)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [caller,outer] body
  let mid := heap++ez
  let zeroStop := state mid (zeroArgs.set .r3 out) [caller,outer] tape 43
  have zeroRun : NaturalRun program (ZeroWeightRowProgram.steps n+2) (state heap zeroArgs [caller,outer] tape 42) [] zeroStop := by
    simpa [zeroStop,mid,Registers.get,Registers.set,len] using zeroInvoke
  let ready := r.set .r0 out
  have zeroRet : tickNatural program zeroStop=some ⟨state mid ready [outer] tape 21,[],0⟩ := by
    simp [zeroStop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,caller,ready]
  obtain ⟨er,gq,⟨g,b,restRead,gridAt,boundAt⟩,restRun⟩ := rest_call (r:=ready) (shared_extend shared ez)
    (state_extend d ez) [outer] tape
  let grown := mid++er
  let finishArgs := ready.set .r1 gq
  let j := grown.length
  let params : Cell ℕ := .pair graph gq
  let result : Cell ℕ := .pair j out
  let extra : NaturalHeap := [params,result]
  have atGraph : grown[r.c]?=some (.pair graph rest) := lookup_extend (lookup_extend atShared ez) er
  have finish : NaturalRun program 4 (state grown finishArgs [outer] tape 22) []
      (state (grown++extra) (r.set .r2 (j+1)) [] tape 2) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,finishArgs,ready,outer,atGraph,params,result,extra,j]
  have read (i : ℕ) : (grown++extra)[j+i]?=extra[i]? := allocated grown extra i
  have final : CandidateFamilyScanProgram.Context (grown++extra) (j+1) D vertices grid (capWord scale) := by
    refine ⟨j,out,graph,gq,g,b,?_,?_,lookup_extend restRead extra,
      graph_extend (graph_extend (graph_extend graphRep ez) er) extra,CandidateDemandRowProgram.grid_extend gridAt extra,
      boolList_extend boundAt extra,?_⟩
    · simpa [extra,result] using read 1
    · simpa [extra,params] using read 0
    · simpa only [len] using list_extend (list_extend zeros er) extra
  refine ⟨ez++er++extra,j+1,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc] using final
  · have trace := append_run enter (append_run zeroRun (.step zeroRet (append_run restRun finish)))
    have count : 4+(ZeroWeightRowProgram.steps n+2+(11+4+1))=ZeroWeightRowProgram.steps n+22 := by omega
    rw [← count]
    simpa only [mid,grown,List.append_assoc,List.nil_append,Nat.add_assoc] using trace

theorem natural_family {n L S : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {D : Input n}
    {a : PairFlags n} {vertices grid scale : Bits} (positive : 0<L)
    (feasible : ∀ p,flag a p=true→CandidateFeasible D.graph p.1 p.2 D.cut L (4*S))
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (keys : EdgeList heap r.a ((pairOrder n).map labelPair)) (active : RowsAt heap r.b a)
    (shared : Shared heap r.c D vertices grid) (current : StateAt heap r.d D scale)
    (size : value vertices=n) (gridValue : value grid=L) (width : value scale=S) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      TableAt (heap++ext) root ((pairOrder n).map (CandidateFamilyScanProgram.selectedRow D a (4*S) grid EN E)) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 3) ∧
      k ≤ instructionBound n L vertices.length grid.length scale.length := by
  obtain ⟨ef,flags,mask,flatten⟩ := flatten_call active tape
  let mid := heap++ef
  let ready := r.set .r1 flags
  obtain ⟨ep,context,contextRep,prepare⟩ := context_call (r:=ready) (shared_extend shared ef) (state_extend current ef) tape
  let grown := mid++ep
  let args := ready.set .r2 context
  have cap : value (capWord scale)=4*S := by rw [cap_value,width]
  obtain ⟨es,root,k,rep,scan,within⟩ := CandidateFamilyScanProgram.natural_family (r:=args) positive feasible EN E
    (edgeList_extend (edgeList_extend keys ef) ep) (boolList_extend mask ep) contextRep size gridValue cap tape
  have invoke := ReferenceProgramInvocation.call scanLabel scan_slots (caller:=2) (continuation:=3)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [] scan
  have scanRun : NaturalRun program (k+2) (state grown args [] tape 2) []
      (state (grown++es) (args.set .r3 root) [] tape 3) := by
    simpa only [Registers.get,Registers.set,mid,grown] using invoke
  refine ⟨ef++ep++es,args,root,(flatSteps n+5)+(ZeroWeightRowProgram.steps n+22+(k+2)),?_,?_,?_⟩
  · simpa only [grown,mid,List.append_assoc] using rep
  · simpa only [grown,mid,List.append_assoc,List.nil_append] using append_run flatten (append_run prepare scanRun)
  · change k ≤ CandidateFamilyScanProgram.instructionBound n L vertices.length grid.length (scale.length+2) at within
    unfold instructionBound
    omega

end DirectedFlowCutGap.CandidateFamilyProgram
