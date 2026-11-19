import DirectedFlowCutGap.ResidualCapacityProgram
import DirectedFlowCutGap.BinaryIncrementProgram
import DirectedFlowCutGap.BinaryPredecessorExecution

/-!
# Physical signed unit augmentation

One call updates a represented skew-flow amount by a positive or negative
unit. The sign dispatch calls binary increment or predecessor on the
stored magnitude and uses the nonnegative sign when the result is zero.
-/

namespace DirectedFlowCutGap.ResidualUnitUpdateProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open BinarySigned (Signed Canonical decode)
open ResidualCapacityProgram (Stored)

def moveUnit (z : Signed) (down : Bool) : Signed :=
  if z.negative = down then
    ⟨z.negative,(increment true z.magnitude).1⟩
  else if z.magnitude = [] then
    ⟨down,[true]⟩
  else
    let p := (predecessor z.magnitude).1
    ⟨if p = [] then false else z.negative,p⟩

private theorem trim_eq_of_length (xs : Bits) (h : (trim xs).1.length=xs.length) :
    (trim xs).1=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases he : (trim xs).1.isEmpty && !b with
    | false =>
      have hlen : (trim xs).1.length=xs.length := by simpa [trim,he] using h
      rw [trim,he]
      exact congrArg (List.cons b) (ih hlen)
    | true => simp [trim,he] at h

private theorem inc_normal {xs : Bits} (hn : Normal xs) : Normal (increment true xs).1 := by
  induction hn with
  | nil => exact .digit .nil (fun _ => rfl)
  | @digit b xs h last ih =>
    cases b with
    | false => exact .digit h (fun _ => rfl)
    | true =>
      have nonzero : (increment true xs).1 ≠ [] := by
        intro eq
        have spec := (increment_spec true xs).1
        simp [eq,value] at spec
      exact .digit ih (fun hz => (nonzero hz).elim)

theorem moveUnit_spec (z : Signed) (down : Bool) (hc : Canonical z) :
    Canonical (moveUnit z down) ∧
      decode (moveUnit z down)=decode z+(if down then -1 else 1) := by
  have inNormal : Normal z.magnitude := by
    have ht := (trim_spec z.magnitude).1
    simpa only [trim_eq_of_length _ ((trim_length _).trans hc.1.symm)] using ht
  have incVal : value (increment true z.magnitude).1=value z.magnitude+1 :=
    (increment_spec true z.magnitude).1
  by_cases e : z.negative=down
  · simp only [moveUnit,e,ite_true]
    refine ⟨⟨?_,?_⟩,?_⟩
    · change (increment true z.magnitude).1.length = (value (increment true z.magnitude).1).size
      rw [← Nat.size_eq_bits_len,normal_bits (inc_normal inNormal)]
    · intro h
      change value (increment true z.magnitude).1=0 at h
      omega
    · cases down <;> simp [decode,e,incVal,add_comm]
  · by_cases hz : z.magnitude=[]
    · simp only [moveUnit,e,ite_false,hz,ite_true]
      have hsign : z.negative=false := hc.2 (by rw [hz]; rfl)
      cases down <;> simp_all [Canonical,decode,value]
    · let p := (predecessor z.magnitude).1
      have hpVal : value p=value z.magnitude-1 := (predecessor_spec z.magnitude).1
      have hpLen : p.length=(value p).size := by rw [hpVal]; exact (predecessor_spec z.magnitude).2.1
      have positive : 0<value z.magnitude := Nat.pos_of_ne_zero (fun h => hz ((normal_zero inNormal).mp h))
      have hpZero : value p=0 → p=[] := by
        intro h
        apply List.length_eq_zero_iff.mp
        simp [hpLen,h]
      simp only [moveUnit,e,ite_false,hz]
      change Canonical ⟨if p=[] then false else z.negative,p⟩ ∧
        decode ⟨if p=[] then false else z.negative,p⟩=_
      refine ⟨⟨hpLen,?_⟩,?_⟩
      · intro h
        simp [hpZero h]
      · have hval : (value p : ℤ)=(value z.magnitude : ℤ)-1 := by omega
        have hdecode : decode ⟨if p=[] then false else z.negative,p⟩=decode ⟨z.negative,p⟩ := by
          by_cases h : p=[]
          · simp [h,decode,value]
          · simp [h]
        rw [hdecode]
        cases h : z.negative <;> cases down <;> simp_all [decode] <;> omega

def incLabel (pc : Fin 16) : Fin 96 := ⟨16+pc.val,by omega⟩
def predLabel (pc : Fin 64) : Fin 96 := ⟨32+pc.val,by omega⟩

def program : Program 96 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .field .r2 .r0 true 1
    | 1 => .field .r0 .r0 false 2
    | 2 => .branch .r2 15 3 4 15
    | 3 => .branch .r1 15 6 5 15
    | 4 => .branch .r1 15 5 6 15
    | 5 => .branch .r0 11 15 15 7
    | 6 => .call (incLabel 15) 9 .r3
    | 7 => .call (predLabel 62) 8 .r3
    | 8 => .branch .r3 10 15 15 9
    | 9 => .make .r3 (.pair .r3 .r2) 12
    | 10 => .make .r2 (.flag false) 9
    | 11 => .move .r2 .r1 6
    | 12 => .ret .r3
    | 14 => .call 0 15 .r3
    | _ => .halt
  else if h : pc.val<32 then
    if pc.val=30 then .ret .r3
    else ReferenceProgramLabels.instruction incLabel
      (BinaryIncrementProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=95 then .ret .r3
  else ReferenceProgramLabels.instruction predLabel
    (BinaryPredecessorProgram.program ⟨pc.val-32,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 96))
    (tape : Bits) (pc : Fin 96) : NaturalState 96 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def steps (z : Signed) (down : Bool) : ℕ :=
  if z.negative=down then BinaryIncrementProgram.steps z.magnitude+9
  else if z.magnitude=[] then BinaryIncrementProgram.steps []+11
  else BinaryPredecessorProgram.steps z.magnitude+
    (if (predecessor z.magnitude).1=[] then 12 else 11)

private theorem inc_slots (pc : Fin 16) (h : BinaryIncrementProgram.program pc≠.halt) :
    program (incLabel pc) = ReferenceProgramLabels.instruction incLabel (BinaryIncrementProgram.program pc) := by
  by_cases hp : pc.val=14
  · have eq : pc=14 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,incLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<32 by omega,
      show 16+pc.val≠30 by omega]

private theorem pred_slots (pc : Fin 64) (h : BinaryPredecessorProgram.program pc≠.halt) :
    program (predLabel pc) = ReferenceProgramLabels.instruction predLabel (BinaryPredecessorProgram.program pc) := by
  by_cases hp : pc.val=63
  · have eq : pc=63 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,predLabel,show ¬32+pc.val<16 by omega,show ¬32+pc.val<32 by omega,
      show 32+pc.val≠95 by omega]

private theorem join {s u v : NaturalState 96} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem increment_call {heap : NaturalHeap} {r : Registers ℕ} {bs : Bits}
    (input : BoolList heap r.a bs) (stack : List (Frame ℕ 96)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (increment true bs).1 ∧
      NaturalRun program (BinaryIncrementProgram.steps bs+3) (state heap r stack tape 6) []
        (state (heap++ext) (r.set .r3 root) stack tape 9) := by
  obtain ⟨ext,root,len,body,rep⟩ := BinaryIncrementProgram.increment_return input heap.length
    r.b r.c r.d rfl r 14 [] tape
  let frame : Frame ℕ 96 := ⟨9,.r3,r⟩
  let before := state (heap++ext) (r.set .r3 root) (frame::stack) tape (incLabel 14)
  have first : tickNatural program (state heap r stack tape 6)=
      some ⟨state heap r (frame::stack) tape (incLabel 15),[],0⟩ := rfl
  have enter : tickNatural program (state heap r (frame::stack) tape (incLabel 15))=
      some ⟨state heap r (⟨incLabel 14,.r3,r⟩::frame::stack) tape (incLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run incLabel BinaryIncrementProgram.program program inc_slots body
  have lift := ReferenceProgramStack.run program (frame::stack) lift
  have run : NaturalRun program (BinaryIncrementProgram.steps bs)
      (state heap r (⟨incLabel 14,.r3,r⟩::frame::stack) tape (incLabel 0)) [] before := by
    cases r
    simpa [before,state,BinaryIncrementProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,Registers.set,len] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) stack tape 9,[],0⟩ := by
    cases r
    simp [before,frame,state,program,incLabel,tickNatural,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have trace := NaturalRun.step first (.step enter (join run (.step ret (.done _))))
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_nil] using trace

private theorem predecessor_call {heap : NaturalHeap} {r : Registers ℕ} {bs : Bits}
    (input : BoolList heap r.a bs) (stack : List (Frame ℕ 96)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (predecessor bs).1 ∧
      NaturalRun program (BinaryPredecessorProgram.steps bs+3) (state heap r stack tape 7) []
        (state (heap++ext) (r.set .r3 root) stack tape 8) := by
  obtain ⟨ext,root,_,body,rep⟩ := BinaryPredecessorProgram.pred input heap.length
    r.b r.c r.d rfl [] tape
  let frame : Frame ℕ 96 := ⟨8,.r3,r⟩
  let before := state (heap++ext) (r.set .r3 root) (frame::stack) tape (predLabel 63)
  have first : tickNatural program (state heap r stack tape 7)=
      some ⟨state heap r (frame::stack) tape (predLabel 62),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run predLabel BinaryPredecessorProgram.program program pred_slots body
  have lift := ReferenceProgramStack.run program (frame::stack) lift
  have run : NaturalRun program (BinaryPredecessorProgram.steps bs+1)
      (state heap r (frame::stack) tape (predLabel 62)) [] before := by
    cases r
    simpa [before,state,BinaryPredecessorProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state,Registers.set] using lift
  have ret : tickNatural program before=some ⟨state (heap++ext) (r.set .r3 root) stack tape 8,[],0⟩ := by
    cases r
    simp [before,frame,state,program,predLabel,tickNatural,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have trace := NaturalRun.step first (join run (.step ret (.done _)))
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_nil] using trace

private theorem pair_return {heap : NaturalHeap} {r : Registers ℕ} {bs : Bits} {neg : Bool}
    (hm : BoolList heap r.d bs) (hs : heap[r.c]?=some (.flag neg))
    (caller : Frame ℕ 96) (stack : List (Frame ℕ 96)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root ⟨neg,bs⟩ ∧
      NaturalRun program 2 (state heap r (caller::stack) tape 9) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let root := heap.length
  let ext : NaturalHeap := [.pair r.d r.c]
  let mid := state (heap++ext) (r.set .r3 root) (caller::stack) tape 12
  have alloc : tickNatural program (state heap r (caller::stack) tape 9)=some ⟨mid,[],0⟩ := by
    simp [root,ext,mid,state,program,tickNatural,Registers.get,allocateNatural,Recipe.cell]
  have ret : tickNatural program mid=
      some ⟨state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
    cases r
    simp [mid,state,program,tickNatural,Registers.get,Registers.set]
  have hp : (heap++ext)[root]?=some (.pair r.d r.c) := by simp [ext,root]
  exact ⟨ext,root,⟨r.d,r.c,hp,boolList_extend hm ext,lookup_extend hs ext⟩,
    .step alloc (.step ret (.done _))⟩

private theorem predecessor_return {heap : NaturalHeap} {r : Registers ℕ} {bs : Bits} {neg : Bool}
    (hm : BoolList heap r.d bs) (hs : heap[r.c]?=some (.flag neg))
    (caller : Frame ℕ 96) (stack : List (Frame ℕ 96)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root ⟨if bs=[] then false else neg,bs⟩ ∧
      NaturalRun program (if bs=[] then 4 else 3) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let saved := caller::stack
  cases hm with
  | nil hp =>
    let cell : Cell ℕ := .flag false
    let next := heap++[cell]
    let args := r.set .r2 heap.length
    have branch : tickNatural program (state heap r saved tape 8)=
        some ⟨state heap r saved tape 10,[],0⟩ := by
      simp [state,program,tickNatural,Registers.get,tagBranch,hp]
    have alloc : tickNatural program (state heap r saved tape 10)=
        some ⟨state next args saved tape 9,[],0⟩ := by
      simp [next,args,cell,state,program,tickNatural,allocateNatural,Recipe.cell]
    have mag : BoolList next args.d [] := by cases r; exact .nil (lookup_extend hp [cell])
    have sign : next[args.c]?=some (.flag false) := by cases r; simp [next,args,cell,Registers.set]
    obtain ⟨ext,root,hrep,hrun⟩ := pair_return mag sign caller stack tape
    exact ⟨cell::ext,root,by simpa [next,List.append_assoc] using hrep,
      by simpa [next,List.append_assoc] using NaturalRun.step branch (.step alloc hrun)⟩
  | cons hp hb ht =>
    have branch : tickNatural program (state heap r saved tape 8)=
        some ⟨state heap r saved tape 9,[],0⟩ := by
      simp [state,program,tickNatural,Registers.get,tagBranch,hp]
    obtain ⟨ext,root,hrep,hrun⟩ := pair_return (.cons hp hb ht) hs caller stack tape
    exact ⟨ext,root,by simpa using hrep,by simpa using NaturalRun.step branch hrun⟩

theorem unit_return {heap : NaturalHeap} {r : Registers ℕ} {z : Signed} {down : Bool}
    (amount : Stored heap r.a z) (direction : heap[r.b]?=some (.flag down))
    (caller : Frame ℕ 96) (stack : List (Frame ℕ 96)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root (moveUnit z down) ∧
      NaturalRun program (steps z down) (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  obtain ⟨mag,sign,hpair,hm,hs⟩ := amount
  let saved := caller::stack
  let readSign := r.set .r2 sign
  let args := readSign.set .r0 mag
  let pc : Fin 96 := if z.negative then 4 else 3
  let target : Fin 96 := if z.negative=down then 6 else 5
  have first : tickNatural program (state heap r saved tape 0)=
      some ⟨state heap readSign saved tape 1,[],0⟩ := by
    simp [readSign,state,program,tickNatural,Registers.get,hpair]
  have second : tickNatural program (state heap readSign saved tape 1)=
      some ⟨state heap args saved tape 2,[],0⟩ := by
    cases r
    simp [args,readSign,state,program,tickNatural,Registers.get,Registers.set,hpair]
  have third : tickNatural program (state heap args saved tape 2)=
      some ⟨state heap args saved tape pc,[],0⟩ := by
    cases r
    cases h : z.negative <;>
      simp [pc,h,args,readSign,state,program,tickNatural,Registers.get,Registers.set,tagBranch,hs]
  have fourth : tickNatural program (state heap args saved tape pc)=
      some ⟨state heap args saved tape target,[],0⟩ := by
    cases r
    cases h : z.negative <;> cases down <;>
      simp [pc,target,h,args,readSign,state,program,tickNatural,Registers.get,Registers.set,tagBranch,direction]
  have startRun : NaturalRun program 4 (state heap r saved tape 0) [] (state heap args saved tape target) :=
    .step first (.step second (.step third (.step fourth (.done _))))
  have sameMag : BoolList heap args.a z.magnitude := by cases r; exact hm
  have sameSign : heap[args.c]?=some (.flag z.negative) := by cases r; exact hs
  by_cases e : z.negative=down
  · simp only [target,e,ite_true] at startRun
    obtain ⟨ext,root,rep,run⟩ := increment_call sameMag saved tape
    have signRep : (heap++ext)[(args.set .r3 root).c]?=some (.flag z.negative) := by
      simpa only [Registers.set] using lookup_extend sameSign ext
    have magRep : BoolList (heap++ext) (args.set .r3 root).d (increment true z.magnitude).1 := by
      cases args; exact rep
    obtain ⟨finish,out,hout,tail⟩ := pair_return magRep signRep caller stack tape
    refine ⟨ext++finish,out,?_,?_⟩
    · simpa only [moveUnit,e,ite_true,List.append_assoc] using hout
    · have trace := join startRun (join run tail)
      simp only [steps,e,ite_true]
      convert trace using 1 <;> first | rfl | omega | simp only [List.append_assoc]
  · simp only [target,e,ite_false] at startRun
    by_cases hz : z.magnitude=[]
    · have empty : heap[args.a]?=some .nil := by
        rw [hz] at sameMag
        cases sameMag with | nil h => exact h
      let fromZero := args.set .r2 args.b
      have branch : tickNatural program (state heap args saved tape 5)=
          some ⟨state heap args saved tape 11,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,empty]
      have move : tickNatural program (state heap args saved tape 11)=
          some ⟨state heap fromZero saved tape 6,[],0⟩ := rfl
      have magRep : BoolList heap fromZero.a [] := by cases args; exact .nil empty
      have signRep : heap[fromZero.c]?=some (.flag down) := by cases r; exact direction
      obtain ⟨ext,root,rep,run⟩ := increment_call magRep saved tape
      have magOut : BoolList (heap++ext) (fromZero.set .r3 root).d [true] := by cases fromZero; exact rep
      have signOut : (heap++ext)[(fromZero.set .r3 root).c]?=some (.flag down) := by
        simpa only [Registers.set] using lookup_extend signRep ext
      obtain ⟨finish,out,hout,tail⟩ := pair_return magOut signOut caller stack tape
      refine ⟨ext++finish,out,?_,?_⟩
      · simpa only [moveUnit,e,ite_false,hz,ite_true,List.append_assoc] using hout
      · have trace := join startRun (.step branch (.step move (join run tail)))
        simp only [steps,e,ite_false,hz,ite_true]
        convert trace using 1 <;> first | rfl | omega | simp only [List.append_assoc]
    · have nonempty : ∃ h t,heap[args.a]?=some (.pair h t) := by
        cases he : z.magnitude with
        | nil => exact (hz he).elim
        | cons bit bits =>
          rw [he] at sameMag
          cases sameMag with | cons h _ _ => exact ⟨_,_,h⟩
      obtain ⟨head,rest,hp⟩ := nonempty
      have branch : tickNatural program (state heap args saved tape 5)=
          some ⟨state heap args saved tape 7,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      obtain ⟨ext,root,rep,run⟩ := predecessor_call sameMag saved tape
      have signRep : (heap++ext)[(args.set .r3 root).c]?=some (.flag z.negative) := by
        simpa only [Registers.set] using lookup_extend sameSign ext
      have magRep : BoolList (heap++ext) (args.set .r3 root).d (predecessor z.magnitude).1 := by
        cases args; exact rep
      obtain ⟨finish,out,hout,tail⟩ := predecessor_return magRep signRep caller stack tape
      refine ⟨ext++finish,out,?_,?_⟩
      · simpa only [moveUnit,e,ite_false,hz,List.append_assoc] using hout
      · have trace := join startRun (.step branch (join run tail))
        simp only [steps,e,ite_false,hz]
        convert trace using 1 <;> first | rfl | (split <;> omega) | simp only [List.append_assoc]

theorem natural_unit {heap : NaturalHeap} {r : Registers ℕ} {z : Signed} {down : Bool}
    (amount : Stored heap r.a z) (direction : heap[r.b]?=some (.flag down)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root (moveUnit z down) ∧
      NaturalRun program (steps z down+1) (state heap r [] tape 14) []
        (state (heap++ext) (r.set .r3 root) [] tape 15) := by
  let frame : Frame ℕ 96 := ⟨15,.r3,r⟩
  obtain ⟨ext,root,hrep,hrun⟩ := unit_return amount direction frame [] tape
  have call : tickNatural program (state heap r [] tape 14)=some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,hrep,.step call hrun⟩

def instructionBound (W : ℕ) : ℕ := 24*W+44

theorem steps_le (z : Signed) (down : Bool) (W : ℕ) (width : z.magnitude.length ≤ W) :
    steps z down+1 ≤ instructionBound W := by
  have i := BinaryIncrementProgram.steps_bound z.magnitude
  have i0 := BinaryIncrementProgram.steps_bound []
  have p := BinaryPredecessorProgram.steps_bound z.magnitude
  simp only [BinaryPredecessorProgram.inputSteps] at p
  unfold steps instructionBound
  split
  · omega
  · split
    · simp only [List.length_nil,Nat.mul_zero,Nat.zero_add] at i0
      omega
    · split <;> omega

private theorem at_entry (s : NaturalState 96) (hp : s.pc=14) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 14 := by
  cases s
  simp_all [state]

theorem physical_unit {H A W : ℕ} {z : Signed} {down : Bool}
    (canonical : Canonical z) (width : z.magnitude.length ≤ W)
    (initial : BitState 96) (bound : initial.Bounded H A) (hp : initial.pc=14) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (amount : Stored (eraseState initial).heap (eraseState initial).registers.a z)
    (direction : (eraseState initial).heap[(eraseState initial).registers.b]?=some (.flag down)) :
    ∃ charge out,Run program (steps z down+1) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (moveUnit z down) ∧
      Canonical (moveUnit z down) ∧
      decode (moveUnit z down)=decode z+(if down then -1 else 1) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=15 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 96 H A (instructionBound W) := by
  let old := eraseState initial
  obtain ⟨ext,root,hrep,hbody⟩ := natural_unit amount direction old.source
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] old.source 15
  have trace : NaturalRun program (steps z down+1) old [] final := by
    rw [at_entry old hp empty hn]
    exact hbody
  have halt : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bound trace halt
  obtain ⟨norm,denotation⟩ := moveUnit_spec z down canonical
  refine ⟨charge,out,hr,?_,norm,denotation,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout]; exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have k := steps_le z down W width
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.ResidualUnitUpdateProgram
