import DirectedFlowCutGap.ResidualTableUpdateProgram

/-!
# Fixed initialization of the zero-flow table

The program shares one stored canonical zero amount across the input
capacity cells. It preserves the capacity word addresses and returns
the table required by the maximum-flow loop.
-/

namespace DirectedFlowCutGap.ResidualZeroTableProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor IntegralNetworkFlow
open PathCostMaterialization (WordList list_extend)
open ResidualRowProgram (Entry StoredEntry StoredRow row_extend)
open ResidualMatrixProgram (StoredTable ValueTable)
open ResidualCapacityProgram (Stored)
open BinarySigned (Signed Canonical)

inductive CapacityRows (heap : NaturalHeap) : ℕ → List (List Bits) → Prop
  | nil {p} : heap[p]?=some .nil → CapacityRows heap p []
  | cons {p head tail cols rows} : heap[p]?=some (.pair head tail) →
      WordList heap head cols → CapacityRows heap tail rows → CapacityRows heap p (cols::rows)

def zero : Signed := ⟨false,[]⟩
def row (cs : List Bits) : List Entry := cs.map (fun cap => (zero,cap))
def table (cs : List (List Bits)) : List (List Entry) := cs.map row

def program : Program 32 := fun pc =>
  match pc.val with
  | 0 => .make .r2 .nil 1
  | 1 => .make .r1 (.flag false) 2
  | 2 => .make .r1 (.pair .r2 .r1) 3
  | 3 => .call 8 4 .r3
  | 8 => .branch .r0 9 4 4 12
  | 9 => .make .r3 .nil 10
  | 10 => .ret .r3
  | 12 => .field .r2 .r0 false 13
  | 13 => .field .r0 .r0 true 14
  | 14 => .call 8 15 .r0
  | 15 => .call 19 16 .r3
  | 16 => .make .r3 (.pair .r3 .r0) 10
  | 19 => .move .r0 .r2 20
  | 20 => .call 24 21 .r3
  | 21 => .ret .r3
  | 24 => .branch .r0 9 4 4 25
  | 25 => .field .r2 .r0 false 26
  | 26 => .field .r0 .r0 true 27
  | 27 => .call 24 28 .r0
  | 28 => .make .r3 (.pair .r1 .r2) 29
  | 29 => .make .r3 (.pair .r3 .r0) 10
  | _ => .halt

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 32))
    (tape : Bits) (pc : Fin 32) : NaturalState 32 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def rowSteps (cs : List Bits) : ℕ := 7*cs.length+3

def tableSteps : List (List Bits) → ℕ
  | [] => 3
  | cs::rest => tableSteps rest+rowSteps cs+10

private theorem join {s u v : NaturalState 32} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem zero_extend {heap : NaturalHeap} {ptr : ℕ} (h : Stored heap ptr zero) (extra : NaturalHeap) :
    Stored (heap++extra) ptr zero := by
  obtain ⟨mag,sign,hp,hm,hs⟩ := h
  exact ⟨mag,sign,lookup_extend hp extra,boolList_extend hm extra,lookup_extend hs extra⟩

private theorem empty_row {heap : NaturalHeap} {r : Registers ℕ}
    (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,(heap++ext)[root]?=some .nil ∧
      NaturalRun program 2 (state heap r (caller::stack) tape 9) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let ext : NaturalHeap := [.nil]
  let root := heap.length
  let next := state (heap++ext) (r.set .r3 root) (caller::stack) tape 10
  have build : tickNatural program (state heap r (caller::stack) tape 9)=some ⟨next,[],0⟩ := by
    simp [ext,root,next,state,program,tickNatural,allocateNatural,Recipe.cell]
  have ret : tickNatural program next=
      some ⟨state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
    simp [next,state,program,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,by simp [ext,root],.step build (.step ret (.done _))⟩

theorem row_return {heap : NaturalHeap} {r : Registers ℕ} {cs : List Bits}
    (input : WordList heap r.a cs) (z : Stored heap r.b zero)
    (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,StoredRow (heap++ext) root (row cs) ∧
      NaturalRun program (rowSteps cs) (state heap r (caller::stack) tape 24) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction cs generalizing heap r caller stack with
  | nil =>
    cases input with
    | nil hp =>
      have select : tickNatural program (state heap r (caller::stack) tape 24)=
          some ⟨state heap r (caller::stack) tape 9,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      obtain ⟨ext,root,hnil,rest⟩ := empty_row caller stack tape
      exact ⟨ext,root,.nil hnil,.step select rest⟩
  | cons cap cs ih =>
    cases input with
    | @cons _ address tail _ _ hp hw ht =>
      let saved := caller::stack
      let first := r.set .r2 address
      let args := first.set .r0 tail
      let frame : Frame ℕ 32 := ⟨28,.r0,args⟩
      have select : tickNatural program (state heap r saved tape 24)=some ⟨state heap r saved tape 25,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      have getWord : tickNatural program (state heap r saved tape 25)=
          some ⟨state heap first saved tape 26,[],0⟩ := by
        simp [first,state,program,tickNatural,Registers.get,hp]
      have getTail : tickNatural program (state heap first saved tape 26)=
          some ⟨state heap args saved tape 27,[],0⟩ := by
        simp [first,args,state,program,tickNatural,Registers.get,Registers.set,hp]
      have call : tickNatural program (state heap args saved tape 27)=
          some ⟨state heap args (frame::saved) tape 24,[],0⟩ := rfl
      obtain ⟨ext,rest,hrest,body⟩ := ih (r:=args) ht z frame saved
      let mid := heap++ext
      let returned := args.set .r0 rest
      let entry : Cell ℕ := .pair r.b address
      let fresh := mid.length
      let cell : Cell ℕ := .pair fresh rest
      let afterEntry := returned.set .r3 fresh
      let out := mid++[entry,cell]
      let before := state out (afterEntry.set .r3 (fresh+1)) saved tape 10
      have makeEntry : tickNatural program (state mid returned saved tape 28)=
          some ⟨state (mid++[entry]) afterEntry saved tape 29,[],0⟩ := by
        simp [mid,returned,args,first,entry,fresh,afterEntry,state,program,tickNatural,Registers.get,
          Registers.set,allocateNatural,Recipe.cell,Nat.add_assoc]
      have makePair : tickNatural program (state (mid++[entry]) afterEntry saved tape 29)=some ⟨before,[],0⟩ := by
        simp [afterEntry,returned,entry,fresh,cell,out,before,state,program,tickNatural,Registers.get,
          Registers.set,allocateNatural,Recipe.cell,Nat.add_assoc]
      have ret : tickNatural program before=some ⟨state out (caller.saved.set caller.destination (fresh+1))
          stack tape caller.continuation,[],0⟩ := by
        simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
      have built : StoredEntry out fresh (zero,cap) :=
        ⟨r.b,address,by simp [out,fresh,entry],zero_extend (zero_extend z ext) _,boolList_extend (boolList_extend hw ext) _⟩
      have rowRep : StoredRow out (fresh+1) (row (cap::cs)) :=
        .cons (by simp [out,fresh,cell]) built (row_extend hrest [entry,cell])
      refine ⟨ext++[entry,cell],fresh+1,?_,?_⟩
      · simpa only [out,mid,List.append_assoc] using rowRep
      · have finish := NaturalRun.step makeEntry (.step makePair (.step ret (.done _)))
        have trace := NaturalRun.step select (.step getWord (.step getTail (.step call (join body finish))))
        simp only [rowSteps,List.length_cons,Nat.mul_add,Nat.mul_one] at trace ⊢
        convert trace using 1 <;> first | rfl | omega | simp only [out,mid,List.append_assoc]

theorem capacityRows_extend {heap : NaturalHeap} {p : ℕ} {rows : List (List Bits)}
    (input : CapacityRows heap p rows) (extra : NaturalHeap) : CapacityRows (heap++extra) p rows := by
  induction input with
  | nil hp => exact .nil (lookup_extend hp extra)
  | cons hp hw _ ih => exact .cons (lookup_extend hp extra) (list_extend hw extra) ih

private theorem head_return {heap : NaturalHeap} {r : Registers ℕ} {cs : List Bits}
    (input : WordList heap r.c cs) (z : Stored heap r.b zero)
    (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,StoredRow (heap++ext) root (row cs) ∧
      NaturalRun program (rowSteps cs+3) (state heap r (caller::stack) tape 19) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let saved := caller::stack
  let args := r.set .r0 r.c
  let frame : Frame ℕ 32 := ⟨21,.r3,args⟩
  have move : tickNatural program (state heap r saved tape 19)=some ⟨state heap args saved tape 20,[],0⟩ := rfl
  have call : tickNatural program (state heap args saved tape 20)=
      some ⟨state heap args (frame::saved) tape 24,[],0⟩ := rfl
  obtain ⟨ext,root,rep,body⟩ := row_return (r:=args) input z frame saved tape
  have ret : tickNatural program (state (heap++ext) (args.set .r3 root) saved tape 21)=
      some ⟨state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
    simp [saved,state,program,tickNatural,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step move (.step call (join body (.step ret (.done _))))⟩

theorem table_return {heap : NaturalHeap} {r : Registers ℕ} {cs : List (List Bits)}
    (input : CapacityRows heap r.a cs) (z : Stored heap r.b zero)
    (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,StoredTable (heap++ext) root (table cs) ∧
      NaturalRun program (tableSteps cs) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction cs generalizing heap r caller stack with
  | nil =>
    cases input with
    | nil hp =>
      have select : tickNatural program (state heap r (caller::stack) tape 8)=
          some ⟨state heap r (caller::stack) tape 9,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      obtain ⟨ext,root,hnil,rest⟩ := empty_row caller stack tape
      exact ⟨ext,root,.nil hnil,.step select rest⟩
  | cons cols cs ih =>
    cases input with
    | @cons _ address tail _ _ hp hw ht =>
      let saved := caller::stack
      let first := r.set .r2 address
      let args := first.set .r0 tail
      let frame : Frame ℕ 32 := ⟨15,.r0,args⟩
      have select : tickNatural program (state heap r saved tape 8)=some ⟨state heap r saved tape 12,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      have getRow : tickNatural program (state heap r saved tape 12)=
          some ⟨state heap first saved tape 13,[],0⟩ := by
        simp [first,state,program,tickNatural,Registers.get,hp]
      have getTail : tickNatural program (state heap first saved tape 13)=
          some ⟨state heap args saved tape 14,[],0⟩ := by
        simp [first,args,state,program,tickNatural,Registers.get,Registers.set,hp]
      have call : tickNatural program (state heap args saved tape 14)=
          some ⟨state heap args (frame::saved) tape 8,[],0⟩ := rfl
      obtain ⟨ext,rest,hrest,body⟩ := ih (r:=args) ht z frame saved
      let mid := heap++ext
      let returned := args.set .r0 rest
      let rowFrame : Frame ℕ 32 := ⟨16,.r3,returned⟩
      have callRow : tickNatural program (state mid returned saved tape 15)=
          some ⟨state mid returned (rowFrame::saved) tape 19,[],0⟩ := rfl
      obtain ⟨more,head,hhead,headTrace⟩ := head_return (r:=returned) (list_extend hw ext) (zero_extend z ext)
        rowFrame saved tape
      let grown := mid++more
      let fresh := grown.length
      let cell : Cell ℕ := .pair head rest
      let out := grown++[cell]
      let afterHead := returned.set .r3 head
      let before := state out (afterHead.set .r3 fresh) saved tape 10
      have makePair : tickNatural program (state grown afterHead saved tape 16)=some ⟨before,[],0⟩ := by
        simp [afterHead,returned,cell,out,fresh,before,state,program,tickNatural,Registers.get,
          Registers.set,allocateNatural,Recipe.cell]
      have ret : tickNatural program before=some ⟨state out (caller.saved.set caller.destination fresh)
          stack tape caller.continuation,[],0⟩ := by
        simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
      have result : StoredTable out fresh (table (cols::cs)) :=
        .cons (by simp [out,fresh,cell]) (row_extend hhead [cell])
          (ResidualTableUpdateProgram.table_extend (ResidualTableUpdateProgram.table_extend hrest more) [cell])
      refine ⟨ext++more++[cell],fresh,?_,?_⟩
      · simpa only [out,grown,mid,List.append_assoc] using result
      · have finish := NaturalRun.step callRow (join headTrace (.step makePair (.step ret (.done _))))
        have trace := NaturalRun.step select (.step getRow (.step getTail (.step call (join body finish))))
        simp only [tableSteps]
        convert trace using 1 <;> first | rfl | omega | simp only [out,grown,mid,List.append_assoc]

theorem natural_zero {heap : NaturalHeap} {r : Registers ℕ} {cs : List (List Bits)}
    (input : CapacityRows heap r.a cs) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),StoredTable (heap++ext) root (table cs) ∧
      NaturalRun program (tableSteps cs+4) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 4) := by
  let p := heap.length
  let sign : Cell ℕ := .flag false
  let packed : Cell ℕ := .pair p (p+1)
  let first := r.set .r2 p
  let second := first.set .r1 (p+1)
  let args := second.set .r1 (p+2)
  let mid := heap++[.nil,sign,packed]
  let frame : Frame ℕ 32 := ⟨4,.r3,args⟩
  have makeNil : tickNatural program (state heap r [] tape 0)=
      some ⟨state (heap++[.nil]) first [] tape 1,[],0⟩ := by
    simp [first,p,state,program,tickNatural,allocateNatural,Recipe.cell]
  have makeSign : tickNatural program (state (heap++[.nil]) first [] tape 1)=
      some ⟨state (heap++[.nil,sign]) second [] tape 2,[],0⟩ := by
    simp [second,p,sign,state,program,tickNatural,allocateNatural,Recipe.cell]
  have makeZero : tickNatural program (state (heap++[.nil,sign]) second [] tape 2)=
      some ⟨state mid args [] tape 3,[],0⟩ := by
    simp [args,second,first,p,packed,mid,state,program,tickNatural,Registers.get,
      Registers.set,allocateNatural,Recipe.cell]
  have zeroRep : Stored mid args.b zero := ⟨p,p+1,by simp [mid,args,packed,p,Registers.set],
    .nil (by simp [mid,p]),by simp [mid,p,sign,zero]⟩
  have inputRep : CapacityRows mid args.a cs := capacityRows_extend input _
  have call : tickNatural program (state mid args [] tape 3)=some ⟨state mid args [frame] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,rep,body⟩ := table_return inputRep zeroRep frame [] tape
  refine ⟨[.nil,sign,packed]++ext,args,root,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · have trace := NaturalRun.step makeNil (.step makeSign (.step makeZero (.step call body)))
    simpa only [frame,mid,List.append_assoc,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using trace

variable {V : Type} [Fintype V] {s t : V}

def CapacityValues (c : Capacity V) (cs : List (List Bits)) (us vs : List V) : Prop :=
  List.Forall₂ (fun cols u => List.Forall₂ (fun word v => value word=c u v) cols vs) cs us

theorem zero_values (c : Capacity V) (cs : List (List Bits)) (us vs : List V)
    (values : CapacityValues c cs us vs) : ValueTable (Flow.zero c s t) (table cs) us vs := by
  have rowValues (u : V) (cols : List Bits) (ls : List V)
      (h : List.Forall₂ (fun word v => value word=c u v) cols ls) :
      List.Forall₂ (fun (e : Entry) v => BinarySigned.decode e.1=(Flow.zero c s t).amount u v ∧
        value e.2=c u v) (row cols) ls := by
    induction h with
    | nil => exact .nil
    | cons first _ ih => exact .cons ⟨rfl,first⟩ ih
  induction values with
  | nil => exact .nil
  | @cons cols u cs us h _ ih => exact .cons (rowValues u cols vs h) ih

theorem zero_fields (cs : List (List Bits)) (B : ℕ) (widths : ∀ xs ∈ cs,∀ w ∈ xs,w.length≤B) :
    ∀ row ∈ table cs,∀ x ∈ row,Canonical x.1 ∧ x.2.length≤B := by
  intro ys hy x hx
  obtain ⟨cols,hcols,rfl⟩ := List.mem_map.mp hy
  obtain ⟨cap,hcap,rfl⟩ := List.mem_map.mp hx
  exact ⟨by simp [Canonical,zero,value],widths cols hcols cap hcap⟩

def instructionBound (m n : ℕ) : ℕ := m*(7*n+13)+7

theorem steps_le (cs : List (List Bits)) (n : ℕ) (same : ∀ xs ∈ cs,xs.length=n) :
    tableSteps cs+4 ≤ instructionBound cs.length n := by
  induction cs with
  | nil => simp [tableSteps,instructionBound]
  | cons cols cs ih =>
    have first := same cols List.mem_cons_self
    have later := ih (fun xs hx => same xs (List.mem_cons_of_mem _ hx))
    simp only [tableSteps,rowSteps,instructionBound,List.length_cons,Nat.add_mul,Nat.one_mul,first] at later ⊢
    omega

private theorem at_entry (s : NaturalState 32) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_zero {H A B : ℕ} (c : Capacity V) (cs : List (List Bits)) (us vs : List V)
    (values : CapacityValues c cs us vs) (widths : ∀ xs ∈ cs,∀ w ∈ xs,w.length≤B)
    (initial : BitState 32) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : CapacityRows (eraseState initial).heap (eraseState initial).registers.a cs) :
    ∃ charge out,Run program (tableSteps cs+4) charge initial [] out ∧
      StoredTable (eraseState out).heap (eraseState out).registers.d (table cs) ∧
      ValueTable (Flow.zero c s t) (table cs) us vs ∧
      (∀ row ∈ table cs,∀ e ∈ row,Canonical e.1 ∧ e.2.length≤B) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=4 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 32 H A (instructionBound us.length vs.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,rep,body⟩ := natural_zero input old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 4
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program (tableSteps cs+4) old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  refine ⟨charge,out,hr,?_,zero_values c cs us vs values,zero_fields cs B widths,htape,?_,?_,⟨ext,?_⟩,
    hstop,hcharge.trans ?_⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have same (xs : List Bits) (hx : xs ∈ cs) : xs.length=vs.length := by
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hx
      have hu : i < us.length := by rwa [← values.length_eq]
      exact (values.get hi hu).length_eq
    have stepBudget := steps_le cs vs.length same
    rw [values.length_eq] at stepBudget
    exact SupportSearchEncoding.complete_mono _ _ _ _ _ stepBudget

end DirectedFlowCutGap.ResidualZeroTableProgram
