import DirectedFlowCutGap.ResidualCapacityProgram

/-!
# One physical row of residual adjacency

The input row stores a signed flow amount and a capacity for each entry.
The program tests each pair with the fixed residual predicate and
returns the Boolean row in the original order.
-/

namespace DirectedFlowCutGap.ResidualRowProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor IntegralNetworkFlow
open BinarySigned (Signed Canonical decode)

abbrev Entry := Signed × Bits

def StoredEntry (heap : NaturalHeap) (root : ℕ) (x : Entry) : Prop :=
  ∃ amount cap, heap[root]?=some (.pair amount cap) ∧
    ResidualCapacityProgram.Stored heap amount x.1 ∧ BoolList heap cap x.2

inductive StoredRow (heap : NaturalHeap) : ℕ → List Entry → Prop
  | nil {p : ℕ} : heap[p]?=some .nil → StoredRow heap p []
  | cons {p first rest : ℕ} {x : Entry} {xs : List Entry} :
      heap[p]?=some (.pair first rest) → StoredEntry heap first x → StoredRow heap rest xs →
        StoredRow heap p (x::xs)

def residualLabel (pc : Fin 60) : Fin 76 := ⟨16+pc.val,by omega⟩

def program : Program 76 := fun pc =>
  if pc.val < 16 then
    match pc.val with
    | 0 => .branch .r0 1 15 15 4
    | 1 => .make .r3 .nil 2
    | 2 => .ret .r3
    | 4 => .field .r2 .r0 false 5
    | 5 => .field .r0 .r0 true 6
    | 6 => .call 0 7 .r1
    | 7 => .call 10 8 .r3
    | 8 => .make .r3 (.pair .r3 .r1) 2
    | 10 => .field .r0 .r2 false 11
    | 11 => .field .r1 .r2 true 12
    | 12 => .call (residualLabel 0) 13 .r3
    | 13 => .ret .r3
    | 14 => .call 0 15 .r3
    | _ => .halt
  else if pc.val=26 then .ret .r3
  else ReferenceProgramLabels.instruction residualLabel
    (ResidualCapacityProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 76)) (tape : Bits)
    (pc : Fin 76) : NaturalState 76 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def flag (x : Entry) : Bool := ResidualCapacityProgram.residual x.1 x.2

def steps : List Entry → ℕ
  | [] => 3
  | x::xs => steps xs+ResidualCapacityProgram.instructions x.1 x.2+12

theorem entry_extend {heap : NaturalHeap} {p : ℕ} {x : Entry} (h : StoredEntry heap p x)
    (ext : NaturalHeap) : StoredEntry (heap++ext) p x := by
  obtain ⟨a,b,hp,⟨m,s,ha,hm,hs⟩,hb⟩ := h
  exact ⟨a,b,lookup_extend hp ext,⟨m,s,lookup_extend ha ext,boolList_extend hm ext,lookup_extend hs ext⟩,
    boolList_extend hb ext⟩

theorem row_extend {heap : NaturalHeap} {p : ℕ} {xs : List Entry} (h : StoredRow heap p xs)
    (ext : NaturalHeap) : StoredRow (heap++ext) p xs := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp he _ ih => exact .cons (lookup_extend hp ext) (entry_extend he ext) ih

private theorem residual_slots (pc : Fin 60) (h : ResidualCapacityProgram.program pc≠.halt) :
    program (residualLabel pc) = ReferenceProgramLabels.instruction residualLabel (ResidualCapacityProgram.program pc) := by
  by_cases hp : pc.val=10
  · have eq : pc=10 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,residualLabel,show ¬16+pc.val<16 by omega,show 16+pc.val≠26 by omega]

private theorem join {s u v : NaturalState 76} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem test_one {heap : NaturalHeap} {r : Registers ℕ} {x : Entry}
    (entry : StoredEntry heap r.c x) (canonical : Canonical x.1)
    (caller : Frame ℕ 76) (stack : List (Frame ℕ 76)) (tape : Bits) :
    ∃ ext bit,(heap++ext)[bit]?=some (.flag (flag x)) ∧
      NaturalRun program (ResidualCapacityProgram.instructions x.1 x.2+5)
        (state heap r (caller::stack) tape 10) []
        (state (heap++ext) (caller.saved.set caller.destination bit) stack tape caller.continuation) := by
  obtain ⟨amount,cap,hpair,hamount,hcap⟩ := entry
  let saved := caller::stack
  let withAmount := r.set .r0 amount
  let args := withAmount.set .r1 cap
  let frame : Frame ℕ 76 := ⟨13,.r3,args⟩
  have readAmount : tickNatural program (state heap r saved tape 10)=
      some ⟨state heap withAmount saved tape 11,[],0⟩ := by
    simp [withAmount,state,tickNatural,program,Registers.get,hpair]
  have readCap : tickNatural program (state heap withAmount saved tape 11)=
      some ⟨state heap args saved tape 12,[],0⟩ := by
    cases r
    simp [withAmount,args,state,tickNatural,program,Registers.get,Registers.set,hpair]
  have call : tickNatural program (state heap args saved tape 12)=
      some ⟨state heap args (frame::saved) tape (residualLabel 0),[],0⟩ := rfl
  have qa : ResidualCapacityProgram.Stored heap args.a x.1 := by cases r; exact hamount
  have qc : BoolList heap args.b x.2 := by cases r; exact hcap
  obtain ⟨ext,regs,hflag,hrun⟩ := ResidualCapacityProgram.natural_residual qa qc canonical tape
  have lift := ReferenceProgramLabels.run residualLabel ResidualCapacityProgram.program program residual_slots hrun
  have lift := ReferenceProgramStack.run program (frame::saved) lift
  let mid := heap++ext
  let before := state mid regs (frame::saved) tape (residualLabel 10)
  let after := state mid (args.set .r3 regs.d) saved tape 13
  let final := state mid (caller.saved.set caller.destination regs.d) stack tape caller.continuation
  have body : NaturalRun program (ResidualCapacityProgram.instructions x.1 x.2)
      (state heap args (frame::saved) tape (residualLabel 0)) [] before := by
    simpa [before,state,mid,ResidualCapacityProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program before=some ⟨after,[],0⟩ := rfl
  have endCall : tickNatural program after=some ⟨final,[],0⟩ := by
    cases r
    simp [after,final,saved,args,withAmount,state,tickNatural,program,Registers.set,Registers.get]
  exact ⟨ext,regs.d,hflag,.step readAmount (.step readCap (.step call (join body (.step ret (.step endCall (.done final))))))⟩

theorem row_return {heap : NaturalHeap} {r : Registers ℕ} {xs : List Entry}
    (input : StoredRow heap r.a xs) (canonical : ∀ x ∈ xs,Canonical x.1)
    (caller : Frame ℕ 76) (stack : List (Frame ℕ 76)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (xs.map flag) ∧
      NaturalRun program (steps xs) (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction xs generalizing heap r caller stack with
  | nil =>
    cases input with
    | nil hp =>
      let saved := caller::stack
      let empty := heap.length
      let ext : NaturalHeap := [.nil]
      let before := state (heap++ext) (r.set .r3 empty) saved tape 2
      have branch : tickNatural program (state heap r saved tape 0)=
          some ⟨state heap r saved tape 1,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hp]
      have alloc : tickNatural program (state heap r saved tape 1)=some ⟨before,[],0⟩ := by
        simp [before,empty,ext,state,tickNatural,program,allocateNatural,Recipe.cell]
      have ret : tickNatural program before=
          some ⟨state (heap++ext) (caller.saved.set caller.destination empty) stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [before,saved,state,tickNatural,program,Registers.get,Registers.set]
      exact ⟨ext,empty,.nil (by simp [ext,empty]),.step branch (.step alloc (.step ret (.done _)))⟩
  | cons x xs ih =>
    cases input with
    | @cons _ head tail _ _ hp hx ht =>
      let saved := caller::stack
      let first := r.set .r2 head
      let args := first.set .r0 tail
      let ftail : Frame ℕ 76 := ⟨7,.r1,args⟩
      have branch : tickNatural program (state heap r saved tape 0)=
          some ⟨state heap r saved tape 4,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hp]
      have readHead : tickNatural program (state heap r saved tape 4)=
          some ⟨state heap first saved tape 5,[],0⟩ := by
        simp [first,state,tickNatural,program,Registers.get,hp]
      have readTail : tickNatural program (state heap first saved tape 5)=
          some ⟨state heap args saved tape 6,[],0⟩ := by
        cases r
        simp [args,first,state,tickNatural,program,Registers.get,Registers.set,hp]
      have callTail : tickNatural program (state heap args saved tape 6)=
          some ⟨state heap args (ftail::saved) tape 0,[],0⟩ := rfl
      have inputTail : StoredRow heap args.a xs := by cases r; exact ht
      obtain ⟨et,rest,hrest,hrun⟩ := ih inputTail
        (fun x hx => canonical x (List.mem_cons_of_mem _ hx)) ftail saved
      let mid := heap++et
      let headArgs := args.set .r1 rest
      let fhead : Frame ℕ 76 := ⟨8,.r3,headArgs⟩
      have headInput : StoredEntry mid headArgs.c x := by cases r; exact entry_extend hx et
      have callHead : tickNatural program (state mid headArgs saved tape 7)=
          some ⟨state mid headArgs (fhead::saved) tape 10,[],0⟩ := rfl
      obtain ⟨eh,bit,hbit,hhead⟩ := test_one headInput (canonical x List.mem_cons_self) fhead saved tape
      let grown := mid++eh
      let cell : Cell ℕ := .pair bit rest
      let fresh := grown.length
      let out := grown++[cell]
      let returned := headArgs.set .r3 bit
      let before := state out (returned.set .r3 fresh) saved tape 2
      have alloc : tickNatural program (state grown returned saved tape 8)=some ⟨before,[],0⟩ := by
        cases r
        simp [before,out,cell,fresh,returned,headArgs,args,first,state,tickNatural,program,
          Registers.get,Registers.set,allocateNatural,Recipe.cell]
      have ret : tickNatural program before=some ⟨state out (caller.saved.set caller.destination fresh)
          stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [before,returned,headArgs,args,first,saved,state,tickNatural,program,Registers.get,Registers.set]
      have result : BoolList out fresh ((x::xs).map flag) :=
        .cons (by simp [out,fresh,cell]) (lookup_extend hbit [cell]) (boolList_extend (boolList_extend hrest eh) [cell])
      refine ⟨et++eh++[cell],fresh,?_,?_⟩
      · simpa only [out,grown,mid,List.append_assoc] using result
      · have trace := NaturalRun.step branch (.step readHead (.step readTail (.step callTail
          (join hrun (.step callHead (join hhead (.step alloc (.step ret (.done _)))))))))
        simp only [steps]
        convert trace using 1 <;> first | rfl | omega | simp only [out,grown,mid,List.append_assoc]

theorem natural_row {heap : NaturalHeap} {r : Registers ℕ} {xs : List Entry}
    (rows : StoredRow heap r.a xs) (canonical : ∀ x ∈ xs,Canonical x.1) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (xs.map flag) ∧
      NaturalRun program (steps xs+1) (state heap r [] tape 14) []
        (state (heap++ext) (r.set .r3 root) [] tape 15) := by
  let frame : Frame ℕ 76 := ⟨15,.r3,r⟩
  obtain ⟨ext,root,hrep,hrun⟩ := row_return rows canonical frame [] tape
  have call : tickNatural program (state heap r [] tape 14)=some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,hrep,.step call hrun⟩

def instructionBound (n W : ℕ) : ℕ := n*(16*(2*W+1)+24)+4

theorem steps_le (xs : List Entry) (W : ℕ) (width : ∀ x ∈ xs,x.1.magnitude.length ≤ W ∧ x.2.length ≤ W) :
    steps xs+1 ≤ instructionBound xs.length W := by
  have h (ys : List Entry) (hw : ∀ x ∈ ys,x.1.magnitude.length ≤ W ∧ x.2.length ≤ W) :
      steps ys ≤ ys.length*(16*(2*W+1)+24)+3 := by
    induction ys with
    | nil => simp [steps]
    | cons y ys ih =>
      obtain ⟨hy,hcap⟩ := hw y List.mem_cons_self
      have later := ih (fun z hz => hw z (List.mem_cons_of_mem _ hz))
      have compare := BinaryComparisonProgram.steps_bound y.2 y.1.magnitude
      have one : ResidualCapacityProgram.instructions y.1 y.2 ≤ 16*(2*W+1)+12 := by
        unfold ResidualCapacityProgram.instructions
        split <;> omega
      simp only [steps,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  simpa only [instructionBound,Nat.add_assoc] using Nat.add_le_add_right (h xs width) 1

theorem row_matches {V : Type} [Fintype V] {c : Capacity V} {s t : V}
    (f : Flow c s t) (u : V) (xs : List Entry) (vs : List V)
    (h : List.Forall₂ (fun x v => decode x.1=f.amount u v ∧ value x.2=c u v) xs vs) :
    xs.map flag = vs.map (fun v => decide (f.amount u v < (c u v : ℤ))) := by
  induction h with
  | nil => rfl
  | @cons x v xs vs he _ ih =>
    simp only [List.map_cons,flag,ResidualCapacityProgram.residual_matches_flow f u v x.1 x.2 he.1 he.2,ih]

private theorem at_entry (s : NaturalState 76) (hp : s.pc=14) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 14 := by
  cases s
  simp_all [state]

theorem physical_row {V : Type} [Fintype V] {c : Capacity V} {s t : V} {H A W : ℕ}
    (f : Flow c s t) (u : V) (xs : List Entry) (vs : List V)
    (values : List.Forall₂ (fun x v => decode x.1=f.amount u v ∧ value x.2=c u v) xs vs)
    (canonical : ∀ x ∈ xs,Canonical x.1)
    (capWidths : ∀ x ∈ xs,x.2.length ≤ W)
    (amountWidths : ∀ v ∈ vs,(max (c u v) (c v u)).size ≤ W)
    (initial : BitState 76) (bound : initial.Bounded H A) (hp : initial.pc=14) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : StoredRow (eraseState initial).heap (eraseState initial).registers.a xs) :
    ∃ charge out, Run program (steps xs+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d
        (vs.map (fun v => decide (f.amount u v < (c u v : ℤ)))) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=15 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 76 H A (instructionBound vs.length W) := by
  let old := eraseState initial
  obtain ⟨ext,root,hrep,hbody⟩ := natural_row input canonical old.source
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] old.source 15
  have trace : NaturalRun program (steps xs+1) old [] final := by
    rw [at_entry old hp empty hn]
    exact hbody
  have halt : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bound trace halt
  refine ⟨charge,out,hr,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout,← row_matches f u xs vs values]
    exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have width (x : Entry) (hx : x ∈ xs) : x.1.magnitude.length ≤ W ∧ x.2.length ≤ W := by
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hx
      have hindex : j < vs.length := by rwa [← values.length_eq]
      have rel := values.get hj hindex
      have hv : vs[j] ∈ vs := List.getElem_mem hindex
      exact ⟨(ResidualCapacityProgram.amount_width f u vs[j] xs[j].1 rel.1 (canonical _ hx)).trans
        (amountWidths _ hv),capWidths _ hx⟩
    have k := steps_le xs W width
    rw [values.length_eq] at k
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.ResidualRowProgram
