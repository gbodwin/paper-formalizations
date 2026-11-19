import DirectedFlowCutGap.InitialDemandPairProgram
import DirectedFlowCutGap.RetainedDemandEraseProgram

/-! Materialize all original threshold demands in row-major storage. -/

namespace DirectedFlowCutGap.InitialDemandMaskProgram

open BooleanTableRead (BoolList)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor IntegralNetworkFlow
open RetainedGridState (PairFlags Pair flag)
open ConcreteExpressionProgram (append_run)
open InitialDemandFlagProgram (units)
open IntegerDistanceFromPhysical (encodedRow)
open PathCostMaterialization (WordList list_extend)
open BinaryPointerListRead (PointerList pointerList_extend)

def pairLabel (pc : Fin 3060) : Fin 3124 := ⟨64+pc.val,by omega⟩

def program : Program 3124 := fun pc =>
  if pc.val < 64 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .branch .r0 10 63 63 12
    | 10 => .make .r3 .nil 17
    | 12 => .field .r3 .r0 false 13
    | 13 => .field .r0 .r0 true 14
    | 14 => .call 8 15 .r0
    | 15 => .call 32 16 .r3
    | 16 => .make .r3 (.pair .r3 .r0) 17
    | 17 => .ret .r3
    | 32 => .move .r0 .r3 33
    | 33 => .call 40 34 .r3
    | 34 => .ret .r3
    | 40 => .branch .r1 10 63 63 41
    | 41 => .field .r3 .r1 false 42
    | 42 => .field .r1 .r1 true 43
    | 43 => .call 40 44 .r1
    | 44 => .call 52 45 .r3
    | 45 => .make .r3 (.pair .r3 .r1) 17
    | 52 => .make .r0 (.pair .r0 .r3) 53
    | 53 => .field .r1 .r2 false 54
    | 54 => .field .r2 .r2 true 55
    | 55 => .call (pairLabel 0) 56 .r3
    | 56 => .ret .r3
    | _ => .halt
  else if pc.val=72 then .ret .r3
  else ReferenceProgramLabels.instruction pairLabel (InitialDemandPairProgram.program ⟨pc.val-64,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 3124

def Context {n : ℕ} (heap : NaturalHeap) (root : ℕ) (adj : PairFlags n)
    (E : ResidualSearch.Enumeration (Fin n)) (label : Fin n→Bits) (level : Bits) : Prop :=
  ∃ shared grid,heap[root]?=some (.pair shared grid) ∧ BoolList heap grid level ∧
    DemandCollection.Shared heap shared (E.vertices.map label) (GraphRelaxationRefinement.matrix adj) (encodedRow (units n)).toList

theorem context_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {adj : PairFlags n} {E : ResidualSearch.Enumeration (Fin n)}
    {label : Fin n→Bits} {level : Bits} (h : Context heap root adj E label level) (ext : NaturalHeap) :
    Context (heap++ext) root adj E label level := by
  obtain ⟨shared,grid,h,word,s⟩ := h
  exact ⟨shared,grid,lookup_extend h ext,boolList_extend word ext,DemandCollection.shared_extend s ext⟩

def pairCap (n W : ℕ) : ℕ := InitialDemandFlagProgram.instructionBound n W W+21

def rowCap (n W cols : ℕ) : ℕ := cols*(pairCap n W+13)+3

def instructionBound (n W : ℕ) : ℕ := n*(rowCap n W n+10)+4

private theorem pair_slots (pc : Fin 3060) (h : InitialDemandPairProgram.program pc≠.halt) :
    program (pairLabel pc)=ReferenceProgramLabels.instruction pairLabel (InitialDemandPairProgram.program pc) := by
  by_cases stop : pc.val=8
  · have eq : pc=8 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,pairLabel,show ¬64+pc.val<64 by omega,show 64+pc.val≠72 by omega]

private theorem pairCap_mono (n W : ℕ) {S : ℕ} (h : S≤W) :
    InitialDemandFlagProgram.instructionBound n W S+21≤ pairCap n W := by
  unfold pairCap InitialDemandFlagProgram.instructionBound GraphRecoveryController.instructionBound
    GraphDiscoveryProgram.discoveryBudget GraphDiscoveryProgram.roundBudget GraphDiscoveryProgram.passBudget
    GraphRelaxationProgram.instructionBound
  gcongr

set_option maxHeartbeats 2600000 in
private theorem pair_call {n W : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (E : ResidualSearch.Enumeration (Fin n)) (p : Pair n) (label : Fin n→Bits) (labels : ∀ i,value (label i)=i.val)
    {level : Bits} (src : BoolList heap r.a (label p.1)) (dst : BoolList heap r.d (label p.2))
    (context : Context heap r.c adj E label level) (hW : 1≤W) (lw : ∀ i,(label i).length≤W) (gw : level.length≤W)
    (stack : List (Frame ℕ 3124)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      (heap++ext)[root]?=some (.flag (flag (RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E (value level)) p)) ∧
      NaturalRun program k (state heap r stack tape 44) [] (state (heap++ext) (r.set .r3 root) stack tape 45) ∧
      k≤ pairCap n W+7 := by
  obtain ⟨shared,grid,atCtx,levelRep,sharedRep⟩ := context
  let frame : Frame ℕ 3124 := ⟨45,.r3,r⟩
  let keyCell : Cell ℕ := .pair r.a r.d
  let mid := heap++[keyCell]
  let args : Registers ℕ := ⟨heap.length,shared,grid,r.d⟩
  have atRecord : mid[r.c]?=some (.pair shared grid) := lookup_extend atCtx _
  have load : NaturalRun program 4 (state heap r stack tape 44) []
      (state mid args (frame::stack) tape 55) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,mid,keyCell,atRecord,frame,allocateNatural,Recipe.cell]
  have key : GraphWalkExtension.Edge mid args.a (label p.1,label p.2) :=
    ⟨r.a,r.d,by simp [mid,args,keyCell],boolList_extend src _,boolList_extend dst _⟩
  obtain ⟨ext,root,a,b,c,k,answer,body,time⟩ := InitialDemandPairProgram.natural_pair (r:=args) E p label labels level
    key (DemandCollection.shared_extend sharedRep _) (boolList_extend levelRep _) hW lw gw tape
  have invoke := ReferenceProgramInvocation.call pairLabel pair_slots (caller:=55) (continuation:=56)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) (frame::stack) body
  let stop := state (mid++ext) (args.set .r3 root) (frame::stack) tape 56
  have finish : tickNatural program stop=some ⟨state (mid++ext) (r.set .r3 root) stack tape 45,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  have cap := time.trans (pairCap_mono n W (lw p.1))
  refine ⟨[keyCell]++ext,root,k+7,?_,?_,by omega⟩
  · simpa only [mid,List.append_assoc] using answer
  · have count : 4+(k+2+1)=k+7 := by omega
    rw [← count]
    simpa only [mid,stop,Registers.get,Registers.set,List.append_assoc,List.nil_append] using
      append_run load (append_run invoke (.step finish (.done _)))

private theorem append_flag {heap : NaturalHeap} {r : Registers ℕ} {bit : Bool} {bits : Bits}
    (head : heap[r.d]?=some (.flag bit)) (row : BoolList heap r.b bits)
    (frame : Frame ℕ 3124) (stack : List (Frame ℕ 3124)) (tape : Bits) :
    let record : Cell ℕ := .pair r.d r.b
    BoolList (heap++[record]) heap.length (bit::bits) ∧
      NaturalRun program 2 (state heap r (frame::stack) tape 45) []
        (state (heap++[record]) (frame.saved.set frame.destination heap.length) stack tape frame.continuation) := by
  refine ⟨.cons (by simp) (lookup_extend head _) (boolList_extend row _),?_⟩
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
    allocateNatural,Recipe.cell]

set_option maxHeartbeats 3100000 in
private theorem row_return {n W : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (E : ResidualSearch.Enumeration (Fin n)) (s : Fin n) (ts : List (Fin n))
    (label : Fin n→Bits) (labels : ∀ i,value (label i)=i.val) {level : Bits}
    (src : BoolList heap r.a (label s)) (targets : WordList heap r.b (ts.map label))
    (context : Context heap r.c adj E label level) (hW : 1≤W) (lw : ∀ i,(label i).length≤W) (gw : level.length≤W)
    (frame : Frame ℕ 3124) (stack : List (Frame ℕ 3124)) (tape : Bits) :
    let mask := RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E (value level)
    ∃ (ext : NaturalHeap) (root k : ℕ),BoolList (heap++ext) root (ts.map fun t=>flag mask (s,t)) ∧
      NaturalRun program k (state heap r (frame::stack) tape 40) []
        (state (heap++ext) (frame.saved.set frame.destination root) stack tape frame.continuation) ∧
      k≤ rowCap n W ts.length := by
  induction ts generalizing heap r frame stack with
  | nil =>
    cases targets with
    | nil atNil =>
      let ext : NaturalHeap := [.nil]
      refine ⟨ext,heap.length,3,.nil (by simp [ext]),?_,by simp [rowCap]⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        atNil,tagBranch,allocateNatural,Recipe.cell,ext]
  | cons t ts ih =>
    cases targets with
    | cons atHead target rest =>
      rename_i targetRoot restRoot
      let args : Registers ℕ := ⟨r.a,restRoot,r.c,targetRoot⟩
      let saved := frame::stack
      let recur : Frame ℕ 3124 := ⟨44,.r1,args⟩
      have first : NaturalRun program 4 (state heap r saved tape 40) [] (state heap args (recur::saved) tape 40) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
          args,recur,atHead,tagBranch]
      obtain ⟨et,tail,k,tailRep,callTail,tailBound⟩ := ih (r:=args) src rest context recur saved
      let withTail := args.set .r1 tail
      let mid := heap++et
      obtain ⟨eh,head,kp,marked,callHead,pairBound⟩ := pair_call (r:=withTail) E (s,t) label labels
        (boolList_extend src et) (boolList_extend target et) (context_extend context et) hW lw gw saved tape
      let grown := mid++eh
      let finalRegs := withTail.set .r3 head
      obtain ⟨result,finish⟩ := append_flag (r:=finalRegs) marked (boolList_extend tailRep eh) frame stack tape
      refine ⟨et++eh++[.pair head tail],grown.length,4+(k+(kp+2)),?_,?_,?_⟩
      · simpa only [mid,grown,finalRegs,withTail,Registers.set,List.append_assoc,List.map_cons] using result
      · simpa only [mid,grown,finalRegs,withTail,Registers.set,List.append_assoc,List.nil_append] using
          append_run first (append_run callTail (append_run callHead finish))
      · simp only [rowCap,List.length_cons,Nat.succ_mul] at tailBound ⊢
        omega

private def Rows (heap : NaturalHeap) (root : ℕ) (rows : List Bits) : Prop :=
  ∃ pointers,PointerList heap root pointers ∧ List.Forall₂ (BoolList heap) pointers rows

private theorem rows_extend {heap : NaturalHeap} {root : ℕ} {rows : List Bits} (h : Rows heap root rows) (ext : NaturalHeap) :
    Rows (heap++ext) root rows := by
  obtain ⟨refs,list,body⟩ := h
  exact ⟨refs,pointerList_extend list ext,body.imp (fun _ _ rep => boolList_extend rep ext)⟩

private theorem append_row {heap : NaturalHeap} {r : Registers ℕ} {head : Bits} {rows : List Bits}
    (current : BoolList heap r.d head) (tail : Rows heap r.a rows)
    (frame : Frame ℕ 3124) (stack : List (Frame ℕ 3124)) (tape : Bits) :
    let record : Cell ℕ := .pair r.d r.a
    Rows (heap++[record]) heap.length (head::rows) ∧
      NaturalRun program 2 (state heap r (frame::stack) tape 16) []
        (state (heap++[record]) (frame.saved.set frame.destination heap.length) stack tape frame.continuation) := by
  let record : Cell ℕ := .pair r.d r.a
  obtain ⟨refs,spine,rep⟩ := rows_extend tail [record]
  refine ⟨⟨r.d::refs,.cons (by simp) spine,.cons (boolList_extend current [record]) rep⟩,?_⟩
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
    allocateNatural,Recipe.cell]

private theorem row_call {n W : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (E : ResidualSearch.Enumeration (Fin n)) (s : Fin n) (ts : List (Fin n))
    (label : Fin n→Bits) (labels : ∀ i,value (label i)=i.val) {level : Bits}
    (src : BoolList heap r.d (label s)) (targets : WordList heap r.b (ts.map label))
    (context : Context heap r.c adj E label level) (hW : 1≤W) (lw : ∀ i,(label i).length≤W) (gw : level.length≤W)
    (stack : List (Frame ℕ 3124)) (tape : Bits) :
    let mask := RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E (value level)
    ∃ (ext : NaturalHeap) (root k : ℕ),BoolList (heap++ext) root (ts.map fun t=>flag mask (s,t)) ∧
      NaturalRun program k (state heap r stack tape 15) [] (state (heap++ext) (r.set .r3 root) stack tape 16) ∧
      k≤ rowCap n W ts.length+4 := by
  let frame : Frame ℕ 3124 := ⟨16,.r3,r⟩
  let args := r.set .r0 r.d
  let inner : Frame ℕ 3124 := ⟨34,.r3,args⟩
  have load : NaturalRun program 3 (state heap r stack tape 15) []
      (state heap args (inner::frame::stack) tape 40) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,inner,frame]
  obtain ⟨ext,root,k,output,body,time⟩ := row_return E s ts label labels (r:=args) src targets context hW lw gw inner (frame::stack) tape
  have ret : tickNatural program (state (heap++ext) (args.set .r3 root) (frame::stack) tape 34)=
      some ⟨state (heap++ext) (r.set .r3 root) stack tape 16,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame,args]
  refine ⟨ext,root,k+4,output,?_,by omega⟩
  have count : 3+(k+1)=k+4 := by omega
  rw [← count]
  exact append_run load (append_run body (.step ret (.done _)))

set_option maxHeartbeats 3200000 in
private theorem matrix_return {n W : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (E : ResidualSearch.Enumeration (Fin n)) (ss ts : List (Fin n)) (label : Fin n→Bits)
    (labels : ∀ i,value (label i)=i.val) {level : Bits}
    (sources : WordList heap r.a (ss.map label)) (targets : WordList heap r.b (ts.map label))
    (context : Context heap r.c adj E label level) (hW : 1≤W) (lw : ∀ i,(label i).length≤W) (gw : level.length≤W)
    (frame : Frame ℕ 3124) (stack : List (Frame ℕ 3124)) (tape : Bits) :
    let mask := RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E (value level)
    ∃ (ext : NaturalHeap) (root k : ℕ),Rows (heap++ext) root (ss.map fun s=>ts.map fun t=>flag mask (s,t)) ∧
      NaturalRun program k (state heap r (frame::stack) tape 8) []
        (state (heap++ext) (frame.saved.set frame.destination root) stack tape frame.continuation) ∧
      k≤ ss.length*(rowCap n W ts.length+10)+3 := by
  induction ss generalizing heap r frame stack with
  | nil =>
    cases sources with
    | nil atNil =>
      let ext : NaturalHeap := [.nil]
      refine ⟨ext,heap.length,3,⟨[],.nil (by simp [ext]),.nil⟩,?_,by simp⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
        atNil,tagBranch,allocateNatural,Recipe.cell,ext]
  | cons s ss ih =>
    cases sources with
    | cons atHead source rest =>
      rename_i sourceRoot restRoot
      let args : Registers ℕ := ⟨restRoot,r.b,r.c,sourceRoot⟩
      let saved := frame::stack
      let recur : Frame ℕ 3124 := ⟨15,.r0,args⟩
      have first : NaturalRun program 4 (state heap r saved tape 8) [] (state heap args (recur::saved) tape 8) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
          args,recur,atHead,tagBranch]
      obtain ⟨et,tail,k,tailRep,callTail,tailBound⟩ := ih (r:=args) rest targets context recur saved
      let withTail := args.set .r0 tail
      let mid := heap++et
      obtain ⟨eh,head,kp,headRep,callHead,pairBound⟩ := row_call (r:=withTail) E s ts label labels
        (boolList_extend source et) (list_extend targets et) (context_extend context et) hW lw gw saved tape
      let grown := mid++eh
      let finalRegs := withTail.set .r3 head
      obtain ⟨result,finish⟩ := append_row (r:=finalRegs) headRep (rows_extend tailRep eh) frame stack tape
      refine ⟨et++eh++[.pair head tail],grown.length,4+(k+(kp+2)),?_,?_,?_⟩
      · simpa only [mid,grown,finalRegs,withTail,Registers.set,List.append_assoc,List.map_cons] using result
      · simpa only [mid,grown,finalRegs,withTail,Registers.set,List.append_assoc,List.nil_append] using
          append_run first (append_run callTail (append_run callHead finish))
      · simp only [List.length_cons,Nat.succ_mul]
        omega

theorem natural_mask {n L W : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    (E : ResidualSearch.Enumeration (Fin n)) (label : Fin n→Bits) (labels : ∀ i,value (label i)=i.val) {level : Bits}
    (grid : value level=L)
    (sources : WordList heap r.a ((List.finRange n).map label)) (targets : WordList heap r.b ((List.finRange n).map label))
    (context : Context heap r.c adj E label level) (hW : 1≤W) (lw : ∀ i,(label i).length≤W) (gw : level.length≤W)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      RetainedDemandEraseProgram.RowsAt (heap++ext) root (RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E L) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) ∧
      k≤ instructionBound n W := by
  let frame : Frame ℕ 3124 := ⟨1,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,k,⟨pointers,rows,flags⟩,work,bound⟩ := matrix_return E (List.finRange n) (List.finRange n)
    label labels sources targets context hW lw gw frame [] tape
  refine ⟨ext,root,k+1,⟨pointers,rows,?_⟩,.step enter work,?_⟩
  · have same : ((RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E L).toList.map Vector.toList)=
        (List.finRange n).map (fun s => (List.finRange n).map
          (fun t => flag (RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E (value level)) (s,t))) := by
      simp only [RetainedDemandMask.compute,flag,grid,List.finRange,List.map_ofFn,Vector.toList_ofFn,Vector.getElem_ofFn,
        Function.comp_def,Fin.eta]
    exact (List.forall₂_map_right_iff).mp (same.symm ▸ flags : List.Forall₂ (BoolList (heap++ext)) pointers
      ((RetainedDemandMask.compute (EncodedIntegerShortestPaths.graph adj) E L).toList.map Vector.toList))
  · simp only [List.length_finRange,instructionBound] at bound ⊢
    omega

end DirectedFlowCutGap.InitialDemandMaskProgram
