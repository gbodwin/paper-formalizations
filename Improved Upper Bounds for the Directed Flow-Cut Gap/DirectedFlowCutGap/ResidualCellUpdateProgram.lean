import DirectedFlowCutGap.ResidualUnitUpdateProgram
import DirectedFlowCutGap.ResidualRowProgram
import DirectedFlowCutGap.ActualSupportSearch

/-!
# Signed flow update from returned residual path edges

Each cell tests membership in both directions using the represented edge
list. It increments for the forward edge and decrements for the reverse
edge. Each applied update preserves canonical signed representation and
keeps the original capacity pointer.
-/

namespace DirectedFlowCutGap.ResidualCellUpdateProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor GraphWalkExtension
open BinarySigned (Canonical Signed decode)
open ResidualCapacityProgram (Stored)
open ResidualRowProgram (Entry StoredEntry entry_extend)
open ResidualUnitUpdateProgram (moveUnit)
open SupportRecoveryProgram (member memberSteps)

def conditionalMove (take down : Bool) (z : Signed) : Signed :=
  if take then moveUnit z down else z

theorem conditionalMove_spec (take down : Bool) (z : Signed) (h : Canonical z) :
    Canonical (conditionalMove take down z) ∧
      decode (conditionalMove take down z)=decode z+(if take then if down then -1 else 1 else 0) := by
  cases take
  · simp [conditionalMove,h]
  · simpa only [conditionalMove,ite_true] using ResidualUnitUpdateProgram.moveUnit_spec z down h

def updated (es : List (Bits×Bits)) (u v : Bits) (z : Signed) : Signed :=
  conditionalMove (member (v,u) es) true (conditionalMove (member (u,v) es) false z)

theorem updated_spec (es : List (Bits×Bits)) (u v : Bits) (z : Signed) (h : Canonical z) :
    Canonical (updated es u v z) ∧ decode (updated es u v z)=decode z+
      (if member (u,v) es then 1 else 0)-(if member (v,u) es then 1 else 0) := by
  have forward := conditionalMove_spec (member (u,v) es) false z h
  have reverse := conditionalMove_spec (member (v,u) es) true _ forward.1
  refine ⟨reverse.1,?_⟩
  unfold updated
  rw [reverse.2,forward.2]
  cases member (u,v) es <;> cases member (v,u) es <;> simp
  omega

open IntegralNetworkFlow IntegralNetworkFlow.Tabulated SupportSearchEncoding

theorem update_matches_augment {n : ℕ} {s t : Fin n} {c : Capacity (Fin n)}
    (f : Flow c s t) (p : SimplePath f.residual s t) (u v : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (z : Signed) (h : Canonical z) (hz : decode z=f.amount u v) :
    decode (updated ((FlowTable.edgeList p).map (encodeEdge label)) (label u) (label v) z) =
      (f.augment p).amount u v := by
  have values := (updated_spec ((FlowTable.edgeList p).map (encodeEdge label)) (label u) (label v) z h).2
  rw [values,hz]
  change f.amount u v+_ - _=f.amount u v+pathSignal p u v-pathSignal p v u
  rw [show (label u,label v)=encodeEdge label (u,v) by rfl,
    show (label v,label u)=encodeEdge label (v,u) by rfl,member_encode label hlabel,member_encode label hlabel]
  simp [pathSignal]

def memberLabel (pc : Fin 280) : Fin 424 := if pc.val=279 then 35 else ⟨48+pc.val,by omega⟩
def unitLabel (pc : Fin 96) : Fin 424 := ⟨328+pc.val,by omega⟩

def program : Program 424 := fun pc =>
  if pc.val<48 then
    match pc.val with
    | 0 => .call 16 1 .r0
    | 1 => .call 25 2 .r3
    | 2 => .ret .r3
    | 16 => .make .r3 (.pair .r2 .r3) 17
    | 17 => .call 32 18 .r3
    | 18 => .branch .r3 31 19 20 31
    | 19 => .ret .r0
    | 20 => .make .r1 (.flag false) 21
    | 21 => .call 38 22 .r3
    | 22 => .ret .r3
    | 25 => .make .r3 (.pair .r3 .r2) 26
    | 26 => .call 32 27 .r3
    | 27 => .branch .r3 31 19 28 31
    | 28 => .make .r1 (.flag true) 21
    | 30 => .call 0 31 .r3
    | 32 => .move .r0 .r1 33
    | 33 => .move .r1 .r3 34
    | 34 => .call (memberLabel 90) 35 .r3
    | 35 => .ret .r3
    | 38 => .field .r2 .r0 true 39
    | 39 => .field .r0 .r0 false 40
    | 40 => .call (unitLabel 14) 41 .r3
    | 41 => .make .r3 (.pair .r3 .r2) 42
    | 42 => .ret .r3
    | _ => .halt
  else if h : pc.val<328 then ReferenceProgramLabels.instruction memberLabel
    (SupportRecoveryProgram.program ⟨pc.val-48,by omega⟩)
  else if pc.val=343 then .ret .r3
  else ReferenceProgramLabels.instruction unitLabel
    (ResidualUnitUpdateProgram.program ⟨pc.val-328,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 424)) (tape : Bits)
    (pc : Fin 424) : NaturalState 424 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def oneDirectionSteps (es : List (Bits×Bits)) (e : Bits×Bits) (down : Bool) (z : Signed) : ℕ :=
  memberSteps e es + (if member e es then ResidualUnitUpdateProgram.steps z down+17 else 8)

def steps (es : List (Bits×Bits)) (u v : Bits) (z : Signed) : ℕ :=
  oneDirectionSteps es (u,v) false z +
    oneDirectionSteps es (v,u) true (conditionalMove (member (u,v) es) false z) + 4

private theorem member_slots (pc : Fin 280) (h : SupportRecoveryProgram.program pc≠.halt) :
    program (memberLabel pc) = ReferenceProgramLabels.instruction memberLabel (SupportRecoveryProgram.program pc) := by
  by_cases hp : pc.val=279
  · have eq : pc=279 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,memberLabel,hp,show ¬48+pc.val<48 by omega,show 48+pc.val<328 by omega]

private theorem unit_slots (pc : Fin 96) (h : ResidualUnitUpdateProgram.program pc≠.halt) :
    program (unitLabel pc) =
      ReferenceProgramLabels.instruction unitLabel (ResidualUnitUpdateProgram.program pc) := by
  by_cases hp : pc.val=15
  · have eq : pc=15 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,unitLabel,show ¬328+pc.val<48 by omega,show ¬328+pc.val<328 by omega,
      show 328+pc.val≠343 by omega]

private theorem join {s u v : NaturalState 424} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem member_call {heap : NaturalHeap} {r : Registers ℕ} {es : List (Bits×Bits)}
    {e : Bits×Bits} (input : EdgeList heap r.b es) (query : Edge heap r.d e) (down : Bool)
    (stack : List (Frame ℕ 424)) (tape : Bits) :
    ∃ ext root,(heap++ext)[root]?=some (.flag (member e es)) ∧
      NaturalRun program (memberSteps e es+5) (state heap r stack tape (if down then 26 else 17)) []
        (state (heap++ext) (r.set .r3 root) stack tape (if down then 27 else 18)) := by
  let cont : Fin 424 := if down then 27 else 18
  let outer : Frame ℕ 424 := ⟨cont,.r3,r⟩
  let first := r.set .r0 r.b
  let args := first.set .r1 r.d
  let inner : Frame ℕ 424 := ⟨35,.r3,args⟩
  have path : EdgeList heap args.a es := input
  have edge : Edge heap args.b e := query
  obtain ⟨ext,root,_,body,flag⟩ := SupportRecoveryProgram.member_return path edge heap.length
    args.c args.d rfl args 279 [] tape
  have t0 : tickNatural program (state heap r stack tape (if down then 26 else 17))=
      some ⟨state heap r (outer::stack) tape 32,[],0⟩ := by cases down <;> rfl
  have t1 : tickNatural program (state heap r (outer::stack) tape 32)=
      some ⟨state heap first (outer::stack) tape 33,[],0⟩ := rfl
  have t2 : tickNatural program (state heap first (outer::stack) tape 33)=
      some ⟨state heap args (outer::stack) tape 34,[],0⟩ := rfl
  have t3 : tickNatural program (state heap args (outer::stack) tape 34)=
      some ⟨state heap args (inner::outer::stack) tape (memberLabel 90),[],0⟩ := rfl
  let before := state (heap++ext) (args.set .r3 root) (outer::stack) tape 35
  have lift := ReferenceProgramLabels.run memberLabel SupportRecoveryProgram.program program member_slots body
  have lift := ReferenceProgramStack.run program (outer::stack) lift
  have trace : NaturalRun program (memberSteps e es)
      (state heap args (inner::outer::stack) tape (memberLabel 90)) [] before := by
    cases r
    simpa [before,state,SupportRecoveryProgram.state,ReferenceProgramLabels.state,ReferenceProgramLabels.frame,
      ReferenceProgramStack.state,memberLabel,inner,args,first,Registers.set] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) stack tape cont,[],0⟩ := by
    cases r
    simp [before,outer,state,program,tickNatural,Registers.get,Registers.set]
  refine ⟨ext,root,flag,?_⟩
  have run := NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (join trace (.step ret (.done _))))))
  simpa only [cont,List.append_nil,Nat.add_assoc,Nat.reduceAdd] using run

private theorem unit_call {heap : NaturalHeap} {r : Registers ℕ} {z : Signed} {down : Bool}
    (amount : Stored heap r.a z) (direction : heap[r.b]?=some (.flag down))
    (stack : List (Frame ℕ 424)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root (moveUnit z down) ∧
      NaturalRun program (ResidualUnitUpdateProgram.steps z down+3) (state heap r stack tape 40) []
        (state (heap++ext) (r.set .r3 root) stack tape 41) := by
  obtain ⟨ext,root,rep,body⟩ := ResidualUnitUpdateProgram.natural_unit amount direction tape
  let frame : Frame ℕ 424 := ⟨41,.r3,r⟩
  let before := state (heap++ext) (r.set .r3 root) (frame::stack) tape (unitLabel 15)
  have call : tickNatural program (state heap r stack tape 40)=
      some ⟨state heap r (frame::stack) tape (unitLabel 14),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run unitLabel ResidualUnitUpdateProgram.program program unit_slots body
  have lift := ReferenceProgramStack.run program (frame::stack) lift
  have trace : NaturalRun program (ResidualUnitUpdateProgram.steps z down+1)
      (state heap r (frame::stack) tape (unitLabel 14)) [] before := by
    simpa [before,state,ResidualUnitUpdateProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) stack tape 41,[],0⟩ := by
    cases r
    simp [before,frame,state,program,unitLabel,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step call (join trace (.step ret (.done _)))⟩

private theorem update_cell {heap : NaturalHeap} {r : Registers ℕ} {x : Entry} {down : Bool}
    (cell : StoredEntry heap r.a x) (direction : heap[r.b]?=some (.flag down))
    (caller : Frame ℕ 424) (stack : List (Frame ℕ 424)) (tape : Bits) :
    ∃ ext root,StoredEntry (heap++ext) root (moveUnit x.1 down,x.2) ∧
      NaturalRun program (ResidualUnitUpdateProgram.steps x.1 down+7)
        (state heap r (caller::stack) tape 38) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  obtain ⟨amount,cap,hpair,hamount,hcap⟩ := cell
  let saved := caller::stack
  let first := r.set .r2 cap
  let args := first.set .r0 amount
  have capField : tickNatural program (state heap r saved tape 38)=
      some ⟨state heap first saved tape 39,[],0⟩ := by
    simp [first,state,program,tickNatural,Registers.get,hpair]
  have amountField : tickNatural program (state heap first saved tape 39)=
      some ⟨state heap args saved tape 40,[],0⟩ := by
    cases r
    simp [first,args,state,program,tickNatural,Registers.get,Registers.set,hpair]
  have input : Stored heap args.a x.1 := hamount
  have dir : heap[args.b]?=some (.flag down) := direction
  obtain ⟨ext,word,rep,body⟩ := unit_call input dir saved tape
  let mid := heap++ext
  let returned := args.set .r3 word
  let fresh := mid.length
  let result : Cell ℕ := .pair word cap
  let out := mid++[result]
  let before := state out (returned.set .r3 fresh) saved tape 42
  have alloc : tickNatural program (state mid returned saved tape 41)=some ⟨before,[],0⟩ := by
    cases r
    simp [mid,returned,fresh,result,out,before,args,first,state,program,tickNatural,
      Registers.get,Registers.set,allocateNatural,Recipe.cell,Nat.add_assoc]
  have ret : tickNatural program before=
      some ⟨state out (caller.saved.set caller.destination fresh) stack tape caller.continuation,[],0⟩ := by
    cases r
    simp [before,returned,args,first,saved,state,program,tickNatural,Registers.get,Registers.set]
  have capRep := boolList_extend hcap (ext++[result])
  obtain ⟨mag,neg,hword,hmag,hneg⟩ := rep
  have packed : StoredEntry out fresh (moveUnit x.1 down,x.2) :=
    ⟨word,cap,by simp [fresh,out,result],⟨mag,neg,lookup_extend hword [result],
      boolList_extend hmag [result],lookup_extend hneg [result]⟩,by
      simpa only [out,mid,List.append_assoc] using capRep⟩
  refine ⟨ext++[result],fresh,?_,?_⟩
  · simpa only [out,mid,List.append_assoc] using packed
  · have trace := NaturalRun.step capField (.step amountField (join body (.step alloc (.step ret (.done _)))))
    convert trace using 1 <;> first | rfl | omega | simp only [out,mid,List.append_assoc]

private theorem direction_return {heap : NaturalHeap} {r : Registers ℕ} {x : Entry} {u v : Bits}
    {es : List (Bits×Bits)} (input : StoredEntry heap r.a x) (path : EdgeList heap r.b es)
    (hu : BoolList heap r.c u) (hv : BoolList heap r.d v) (down : Bool)
    (caller : Frame ℕ 424) (stack : List (Frame ℕ 424)) (tape : Bits) :
    let e := if down then (v,u) else (u,v)
    ∃ ext root,StoredEntry (heap++ext) root (conditionalMove (member e es) down x.1,x.2) ∧
      NaturalRun program (oneDirectionSteps es e down x.1)
        (state heap r (caller::stack) tape (if down then 25 else 16)) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let e : Bits×Bits := if down then (v,u) else (u,v)
  change ∃ ext root,StoredEntry (heap++ext) root (conditionalMove (member e es) down x.1,x.2) ∧
    NaturalRun program (oneDirectionSteps es e down x.1)
      (state heap r (caller::stack) tape (if down then 25 else 16)) []
      (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation)
  let saved := caller::stack
  let query : Cell ℕ := if down then .pair r.d r.c else .pair r.c r.d
  let first := heap++[query]
  let args := r.set .r3 heap.length
  have make : tickNatural program (state heap r saved tape (if down then 25 else 16))=
      some ⟨state first args saved tape (if down then 26 else 17),[],0⟩ := by
    cases down <;> simp [first,args,query,state,program,tickNatural,Registers.get,allocateNatural,Recipe.cell]
  have queryRep : Edge first args.d e := by
    cases down
    · exact ⟨r.c,r.d,by simp [first,args,query,Registers.set],
        boolList_extend hu [query],boolList_extend hv [query]⟩
    · exact ⟨r.d,r.c,by simp [first,args,query,Registers.set],
        boolList_extend hv [query],boolList_extend hu [query]⟩
  have pathRep : EdgeList first args.b es := edgeList_extend path [query]
  obtain ⟨ext,flag,hflag,check⟩ := member_call pathRep queryRep down saved tape
  let grown := first++ext
  let returned := args.set .r3 flag
  have seen : grown[returned.d]?=some (.flag (member e es)) := hflag
  cases found : member e es with
  | false =>
    have branch : tickNatural program (state grown returned saved tape (if down then 27 else 18))=
        some ⟨state grown returned saved tape 19,[],0⟩ := by
      have tag := seen
      rw [found] at tag
      cases down <;> simp [state,program,tickNatural,Registers.get,tagBranch,tag]
    have ret : tickNatural program (state grown returned saved tape 19)=
        some ⟨state grown (caller.saved.set caller.destination r.a) stack tape caller.continuation,[],0⟩ := by
      simp [returned,args,saved,state,program,tickNatural,Registers.get,Registers.set]
    refine ⟨query::ext,r.a,?_,?_⟩
    · simpa only [conditionalMove,found,Bool.false_eq_true,ite_false] using entry_extend input (query::ext)
    · have trace := NaturalRun.step make (join check (.step branch (.step ret (.done _))))
      simp only [oneDirectionSteps,found,Bool.false_eq_true,ite_false]
      convert trace using 1 <;> first | rfl | omega | simp only [grown,first,List.append_assoc,List.singleton_append]
  | true =>
    let sig : Cell ℕ := .flag down
    let allocated := grown++[sig]
    let withSign := returned.set .r1 grown.length
    let localFrame : Frame ℕ 424 := ⟨22,.r3,withSign⟩
    have branch : tickNatural program (state grown returned saved tape (if down then 27 else 18))=
        some ⟨state grown returned saved tape (if down then 28 else 20),[],0⟩ := by
      have tag := seen
      rw [found] at tag
      cases down <;> simp [state,program,tickNatural,Registers.get,tagBranch,tag]
    have makeSign : tickNatural program (state grown returned saved tape (if down then 28 else 20))=
        some ⟨state allocated withSign saved tape 21,[],0⟩ := by
      cases down <;> simp [withSign,allocated,sig,state,program,tickNatural,allocateNatural,Recipe.cell]
    have call : tickNatural program (state allocated withSign saved tape 21)=
        some ⟨state allocated withSign (localFrame::saved) tape 38,[],0⟩ := rfl
    have hcell : StoredEntry allocated withSign.a x :=
      entry_extend (entry_extend (entry_extend input [query]) ext) [sig]
    have sign : allocated[withSign.b]?=some (.flag down) := by simp [allocated,withSign,sig,Registers.set]
    obtain ⟨finish,root,hout,body⟩ := update_cell hcell sign localFrame saved tape
    let out := allocated++finish
    let before := state out (withSign.set .r3 root) saved tape 22
    have ret : tickNatural program before=some ⟨state out (caller.saved.set caller.destination root)
        stack tape caller.continuation,[],0⟩ := by
      simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
    refine ⟨query::(ext++sig::finish),root,?_,?_⟩
    · simpa only [conditionalMove,found,ite_true,allocated,grown,first,List.append_assoc,
        List.cons_append,List.nil_append] using hout
    · have trace := NaturalRun.step make (join check (.step branch (.step makeSign (.step call
        (join body (.step ret (.done _)))))))
      simp only [oneDirectionSteps,found,ite_true]
      convert trace using 1 <;> first | rfl | omega |
        simp only [out,allocated,grown,first,List.append_assoc,List.cons_append,List.nil_append]

theorem update_return {heap : NaturalHeap} {r : Registers ℕ} {x : Entry} {u v : Bits}
    {es : List (Bits×Bits)} (input : StoredEntry heap r.a x) (path : EdgeList heap r.b es)
    (hu : BoolList heap r.c u) (hv : BoolList heap r.d v)
    (caller : Frame ℕ 424) (stack : List (Frame ℕ 424)) (tape : Bits) :
    ∃ ext root,StoredEntry (heap++ext) root (updated es u v x.1,x.2) ∧
      NaturalRun program (steps es u v x.1-1) (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let saved := caller::stack
  let firstFrame : Frame ℕ 424 := ⟨1,.r0,r⟩
  obtain ⟨ef,first,hfirst,forward⟩ := direction_return input path hu hv false firstFrame saved tape
  have call0 : tickNatural program (state heap r saved tape 0)=
      some ⟨state heap r (firstFrame::saved) tape 16,[],0⟩ := rfl
  let middle := heap++ef
  let args := r.set .r0 first
  let secondFrame : Frame ℕ 424 := ⟨2,.r3,args⟩
  have hinput : StoredEntry middle args.a (conditionalMove (member (u,v) es) false x.1,x.2) := hfirst
  have hpath : EdgeList middle args.b es := edgeList_extend path ef
  have hleft : BoolList middle args.c u := boolList_extend hu ef
  have hright : BoolList middle args.d v := boolList_extend hv ef
  obtain ⟨er,root,hresult,reverse⟩ := direction_return hinput hpath hleft hright true secondFrame saved tape
  have call1 : tickNatural program (state middle args saved tape 1)=
      some ⟨state middle args (secondFrame::saved) tape 25,[],0⟩ := rfl
  let out := middle++er
  let before := state out (args.set .r3 root) saved tape 2
  have ret : tickNatural program before=some ⟨state out
      (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
    simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
  refine ⟨ef++er,root,?_,?_⟩
  · simpa only [middle,List.append_assoc,updated,ite_true] using hresult
  · have trace := NaturalRun.step call0 (join forward (.step call1 (join reverse (.step ret (.done _)))))
    simp only [steps]
    convert trace using 1 <;> first | rfl | omega | simp only [out,middle,List.append_assoc]

theorem natural_update {heap : NaturalHeap} {r : Registers ℕ} {x : Entry} {u v : Bits}
    {es : List (Bits×Bits)} (input : StoredEntry heap r.a x) (path : EdgeList heap r.b es)
    (hu : BoolList heap r.c u) (hv : BoolList heap r.d v) (tape : Bits) :
    ∃ ext root,StoredEntry (heap++ext) root (updated es u v x.1,x.2) ∧
      NaturalRun program (steps es u v x.1) (state heap r [] tape 30) []
        (state (heap++ext) (r.set .r3 root) [] tape 31) := by
  let frame : Frame ℕ 424 := ⟨31,.r3,r⟩
  obtain ⟨ext,root,hrep,body⟩ := update_return input path hu hv frame [] tape
  have call : tickNatural program (state heap r [] tape 30)=some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,hrep,.step call body⟩

private theorem conditional_width (z : Signed) (h : Canonical z) (take down : Bool) :
    (conditionalMove take down z).magnitude.length ≤ z.magnitude.length+1 := by
  cases take
  · simp [conditionalMove]
  · simp only [conditionalMove,ite_true]
    unfold moveUnit
    split
    · exact (increment_spec true z.magnitude).2.1
    · split
      · simp
      · simp only
        rw [(predecessor_spec z.magnitude).2.1, h.1]
        exact (Nat.size_le_size (Nat.sub_le _ _)).trans (Nat.le_succ _)

def instructionBound (m W B : ℕ) : ℕ :=
  2*(m*(64*W+57)+ResidualUnitUpdateProgram.instructionBound (B+1)+19)+4

theorem steps_le (es : List (Bits×Bits)) (u v : Bits) (z : Signed) (h : Canonical z) (W B : ℕ)
    (hu : u.length≤W) (hv : v.length≤W) (hz : z.magnitude.length≤B)
    (he : ∀ e ∈ es,SupportRecoveryProgram.EdgeWidths W e) :
    steps es u v z ≤ instructionBound es.length W B := by
  let first := conditionalMove (member (u,v) es) false z
  have shr (e : Bits×Bits) (down : Bool) (value : Signed) (hw : value.magnitude.length≤B+1)
      (labels : SupportRecoveryProgram.EdgeWidths W e) :
      oneDirectionSteps es e down value ≤
        es.length*(64*W+57)+ResidualUnitUpdateProgram.instructionBound (B+1)+19 := by
    have m := SupportRecoveryProgram.member_steps_le W e es labels he
    have a := ResidualUnitUpdateProgram.steps_le value down (B+1) hw
    unfold oneDirectionSteps
    split <;> omega
  have wfirst : first.magnitude.length≤B+1 :=
    (conditional_width z h (member (u,v) es) false).trans (Nat.add_le_add_right hz 1)
  have a := shr (u,v) false z (hz.trans (Nat.le_succ _)) ⟨hu,hv⟩
  have b := shr (v,u) true first wfirst ⟨hv,hu⟩
  exact Nat.add_le_add_right (by rw [two_mul]; exact Nat.add_le_add a b) 4

private theorem at_entry (s : NaturalState 424) (hp : s.pc=30) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 30 := by
  cases s
  simp_all [state]

theorem physical_update {H A W B : ℕ} {x : Entry} {u v : Bits} {es : List (Bits×Bits)}
    (canonical : Canonical x.1) (hu : u.length≤W) (hv : v.length≤W) (hz : x.1.magnitude.length≤B)
    (he : ∀ e ∈ es,SupportRecoveryProgram.EdgeWidths W e)
    (initial : BitState 424) (bounded : initial.Bounded H A) (hp : initial.pc=30) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : StoredEntry (eraseState initial).heap (eraseState initial).registers.a x)
    (path : EdgeList (eraseState initial).heap (eraseState initial).registers.b es)
    (left : BoolList (eraseState initial).heap (eraseState initial).registers.c u)
    (right : BoolList (eraseState initial).heap (eraseState initial).registers.d v) :
    ∃ charge out,Run program (steps es u v x.1) charge initial [] out ∧
      StoredEntry (eraseState out).heap (eraseState out).registers.d (updated es u v x.1,x.2) ∧
      Canonical (updated es u v x.1) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=31 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 424 H A (instructionBound es.length W B) := by
  let old := eraseState initial
  obtain ⟨ext,root,hrep,body⟩ := natural_update input path left right old.source
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] old.source 31
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program (steps es u v x.1) old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  refine ⟨charge,out,hr,?_,(updated_spec es u v x.1 canonical).1,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout]; exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · exact SupportSearchEncoding.complete_mono _ _ _ _ _ (steps_le es u v x.1 canonical W B hu hv hz he)

end DirectedFlowCutGap.ResidualCellUpdateProgram
