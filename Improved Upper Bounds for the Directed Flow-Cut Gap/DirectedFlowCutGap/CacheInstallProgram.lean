import DirectedFlowCutGap.AdaptiveControllerStorage

/-! Install the cached optimum by reusing its table and mass pointers. -/

namespace DirectedFlowCutGap.CacheInstallProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open ConcreteExpressionProgram (append_run)
open AdaptiveControllerStorage (StateAt CacheAt cache_extend)

def program : Program 48 := fun pc =>
  match pc.val with
  | 0 => .call 8 1 .r0
  | 1 => .call 24 2 .r1
  | 2 => .make .r3 (.pair .r0 .r1) 3
  | 8 => .field .r0 .r3 false 9
  | 9 => .field .r0 .r0 false 10
  | 10 => .field .r0 .r0 false 11
  | 11 => .field .r1 .r3 true 12
  | 12 => .field .r1 .r1 true 13
  | 13 => .make .r0 (.pair .r0 .r1) 14
  | 14 => .ret .r0
  | 24 => .call 40 25 .r1
  | 25 => .field .r0 .r3 true 26
  | 26 => .field .r0 .r0 false 27
  | 27 => .field .r2 .r3 false 28
  | 28 => .field .r2 .r2 true 29
  | 29 => .field .r2 .r2 false 30
  | 30 => .field .r2 .r2 true 31
  | 31 => .make .r0 (.pair .r0 .r2) 32
  | 32 => .make .r1 (.pair .r0 .r1) 33
  | 33 => .ret .r1
  | 40 => .field .r2 .r3 false 41
  | 41 => .field .r2 .r2 true 42
  | 42 => .field .r1 .r2 true 43
  | 43 => .field .r2 .r2 false 44
  | 44 => .field .r2 .r2 true 45
  | 45 => .make .r1 (.pair .r2 .r1) 46
  | 46 => .make .r1 (.pair .r2 .r1) 47
  | 47 => .ret .r1
  | _ => .halt

abbrev state := @ReferenceProgramInvocation.state 48

set_option maxHeartbeats 1300000 in
private theorem replace_mass {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {d : Data n}
    {optimum : ℕ} {cand : Family n} {words optWords : List (List Bits)} {scale : Bits}
    (cache : CacheAt heap r.d d optimum cand words optWords scale) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),ext.length=1 ∧ RoundStateUpdateProgram.UpdatedAt (heap++ext) root (d.install cand optimum) ∧
      NaturalRun program 8 (state heap r [] tape 0) [] (state (heap++ext) (r.set .r0 root) [] tape 1) := by
  obtain ⟨live,best,atCache,⟨packed,runtime,context,scaleRoot,weights,free,atState,update,rr,rc,w,f,s,v,rd⟩,
    ⟨optTable,optMass,optBits,atBest,op,od,m,b⟩⟩ := cache
  obtain ⟨masks,mass,massBits,atPacked,maskRep,cur,cv⟩ := update
  let frame : Frame ℕ 48 := ⟨1,.r0,r⟩
  let args : Registers ℕ := ⟨masks,optMass,r.c,r.d⟩
  let ext : NaturalHeap := [.pair masks optMass]
  have read : NaturalRun program 6 (state heap r [] tape 0) [] (state heap args [frame] tape 13) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,args,atCache,atState,atPacked,atBest]
  have save : NaturalRun program 2 (state heap args [frame] tape 13) []
      (state (heap++ext) (r.set .r0 heap.length) [] tape 1) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      frame,args,ext,allocateNatural,Recipe.cell]
  exact ⟨ext,heap.length,rfl,⟨masks,optMass,optBits,by simp [ext],RoundInputPackProgram.masks_extend maskRep ext,
    boolList_extend m ext,b⟩,append_run read save⟩

set_option maxHeartbeats 2000000 in
private theorem replace_runtime {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {d : Data n}
    {optimum : ℕ} {cand : Family n} {words optWords : List (List Bits)} {scale : Bits}
    (cache : CacheAt heap r.d d optimum cand words optWords scale) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root context scaleRoot weights free : ℕ), ext.length=4 ∧
      (heap++ext)[root]?=some (.pair context scaleRoot) ∧ (heap++ext)[context]?=some (.pair weights free) ∧
      RetainedMassTableProgram.TableAt (heap++ext) weights optWords ∧ (heap++ext)[free]?=some (.flag false) ∧
      BoolList (heap++ext) scaleRoot (false::false::scale) ∧ value scale=d.scale ∧
      RetainedMassTableProgram.DataRows cand optWords ∧
      NaturalRun program 19 (state heap r [] tape 1) [] (state (heap++ext) (r.set .r1 root) [] tape 2) := by
  obtain ⟨live,best,atCache,⟨packed,runtime,context,scaleRoot,weights,free,atState,update,atRuntime,atContext,w,f,s,v,rd⟩,
    ⟨optTable,optMass,optBits,atBest,op,od,m,b⟩⟩ := cache
  let outer : Frame ℕ 48 := ⟨2,.r1,r⟩
  let shift : Frame ℕ 48 := ⟨25,.r1,r⟩
  let first : Registers ℕ := ⟨r.a,scaleRoot,free,r.d⟩
  let addr := heap.length
  let bit1 : Cell ℕ := .pair free scaleRoot
  let bit2 : Cell ℕ := .pair free addr
  let newContext : Cell ℕ := .pair optTable free
  let newRuntime : Cell ℕ := .pair (addr+2) (addr+1)
  let shifts : NaturalHeap := [bit1,bit2]
  let mid := heap++shifts
  let extra : NaturalHeap := [newContext,newRuntime]
  let second := r.set .r1 (addr+1)
  let third : Registers ℕ := ⟨optTable,addr+1,free,r.d⟩
  have enter : NaturalRun program 2 (state heap r [] tape 1) [] (state heap r [shift,outer] tape 40) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,shift,outer]
  let args : Registers ℕ := ⟨r.a,scaleRoot,runtime,r.d⟩
  have load : NaturalRun program 3 (state heap r [shift,outer] tape 40) [] (state heap args [shift,outer] tape 43) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,atCache,atState,atRuntime]
  have field : NaturalRun program 2 (state heap args [shift,outer] tape 43) [] (state heap first [shift,outer] tape 45) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,first,atRuntime,atContext]
  have prepend : NaturalRun program 3 (state heap first [shift,outer] tape 45) [] (state mid second [outer] tape 25) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      first,second,shift,outer,mid,shifts,bit1,bit2,addr,allocateNatural,Recipe.cell]
  have fields : NaturalRun program 6 (state mid second [outer] tape 25) [] (state mid third [outer] tape 31) := by
    have hc := lookup_extend atCache shifts
    have hs := lookup_extend atState shifts
    have hr := lookup_extend atRuntime shifts
    have hx := lookup_extend atContext shifts
    have hb := lookup_extend atBest shifts
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      second,third,outer,mid,hc,hs,hr,hx,hb]
  have finish : NaturalRun program 3 (state mid third [outer] tape 31) []
      (state (mid++extra) (r.set .r1 (addr+3)) [] tape 2) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      third,outer,mid,shifts,extra,newContext,newRuntime,addr,allocateNatural,Recipe.cell,Nat.add_assoc]
  let ext := shifts++extra
  have firstBit : (heap++ext)[addr]?=some bit1 := by simp [ext,shifts,extra,addr]
  have secondBit : (heap++ext)[addr+1]?=some bit2 := by simp [ext,shifts,extra,addr]
  refine ⟨ext,addr+3,addr+2,addr+1,optTable,free,rfl,?_,?_,RoundInputPackProgram.weights_extend op ext,
    lookup_extend f ext,.cons secondBit (lookup_extend f ext) (.cons firstBit (lookup_extend f ext) (boolList_extend s ext)),
    v,od,?_⟩
  · simp [ext,shifts,extra,addr,newRuntime]
  · simp [ext,shifts,extra,addr,newContext]
  · simpa only [mid,ext,List.append_assoc,List.nil_append] using append_run enter (append_run load (append_run field (append_run prepend (append_run fields finish))))

theorem natural_install {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {d : Data n}
    {optimum : ℕ} {cand : Family n} {words optWords : List (List Bits)} {scale : Bits}
    (cache : CacheAt heap r.d d optimum cand words optWords scale) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root packed runtime : ℕ),ext.length=6 ∧ (heap++ext)[root]?=some (.pair packed runtime) ∧
      StateAt (heap++ext) root (d.install cand optimum) optWords (false::false::scale) ∧
      NaturalRun program 28 (state heap r [] tape 0) []
        (state (heap++ext) ⟨packed,runtime,r.c,root⟩ [] tape 3) := by
  obtain ⟨em,packed,one,mass,replaceMass⟩ := replace_mass cache tape
  let mid := heap++em
  let withMass := r.set .r0 packed
  obtain ⟨er,runtime,context,scaleRoot,weights,free,four,atRuntime,atContext,table,atFree,scaleRep,scaleValue,data,replaceRuntime⟩ :=
    replace_runtime (r:=withMass) (cache_extend cache em) tape
  let ready := mid++er
  let root := ready.length
  let record : Cell ℕ := .pair packed runtime
  let args : Registers ℕ := ⟨packed,runtime,r.c,r.d⟩
  have finish : tickNatural program (state ready args [] tape 2)=
      some ⟨state (ready++[record]) ⟨packed,runtime,r.c,root⟩ [] tape 3,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,args,root,
      allocateNatural,Recipe.cell,record]
  let ext := em++er++[record]
  have outer : (ready++[record])[root]?=some (.pair packed runtime) := by simp [root,record]
  have scaleValid : value (false::false::scale)=(d.install cand optimum).scale := by
    simp [value,Data.install,scaleValue]
    omega
  have stored : StateAt (ready++[record]) root (d.install cand optimum) optWords (false::false::scale) :=
    ⟨packed,runtime,context,scaleRoot,weights,free,outer,
      AdaptiveControllerStorage.updated_extend (AdaptiveControllerStorage.updated_extend mass er) [record],
      lookup_extend atRuntime _,lookup_extend atContext _,RoundInputPackProgram.weights_extend table _,
      lookup_extend atFree _,boolList_extend scaleRep _,scaleValid,data⟩
  refine ⟨ext,root,packed,runtime,by simp [ext,one,four],?_,?_,?_⟩
  · simpa only [ext,ready,mid,List.append_assoc] using outer
  · simpa only [ext,ready,mid,List.append_assoc] using stored
  · simpa only [mid,withMass,ready,args,Registers.set,List.append_assoc,List.nil_append,ext] using
      append_run replaceMass (append_run replaceRuntime (.step finish (.done _)))

end DirectedFlowCutGap.CacheInstallProgram
