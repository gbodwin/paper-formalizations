import DirectedFlowCutGap.RetainedDemandEraseProgram
import DirectedFlowCutGap.RetainedMassTableProgram

/-!
# Flattening the retained demand matrix for the mass scan

Rows are traversed in order. The program copies each pair cell once
and reuses its stored Boolean reference. The result is aligned with the
source-then-target order of the mass table.
-/

namespace DirectedFlowCutGap.FlattenDemandMaskProgram

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open BinaryArithmetic PackedBooleanConstructor RetainedGridState
open BinaryPointerListRead (PointerList)
open RetainedDemandEraseProgram (RowsAt)

def program : Program 18 := fun pc =>
  match pc.val with
  | 0 => .call 1 8 .r3
  | 1 => .branch .r0 2 17 17 3
  | 2 => .ret .r0
  | 3 => .field .r1 .r0 false 4
  | 4 => .field .r0 .r0 true 5
  | 5 => .call 1 6 .r0
  | 6 => .call 10 7 .r0
  | 7 => .ret .r0
  | 10 => .branch .r1 16 17 17 11
  | 11 => .field .r2 .r1 false 12
  | 12 => .field .r1 .r1 true 13
  | 13 => .call 10 14 .r0
  | 14 => .make .r0 (.pair .r2 .r0) 16
  | 16 => .ret .r0
  | _ => .halt

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 18))
    (tape : Bits) (pc : Fin 18) : NaturalState 18 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

private theorem join {a b c : NaturalState 18} {m n : ℕ} {es fs : List Event}
    (h : NaturalRun program m a es b) (hg : NaturalRun program n b fs c) :
    NaturalRun program (m+n) a (es++fs) c := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem append_subroutine {heap : NaturalHeap} {row tail : ℕ} {xs ys : Bits}
    (hx : BoolList heap row xs) (hy : BoolList heap tail ys) (c d : ℕ)
    (caller : Frame ℕ 18) (stack : List (Frame ℕ 18)) (tape : Bits) :
    ∃ ext root, ext.length = xs.length ∧ BoolList (heap++ext) root (xs++ys) ∧
      NaturalRun program (6*xs.length+2) (state heap ⟨tail,row,c,d⟩ (caller::stack) tape 10) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction hx generalizing c d caller stack with
  | @nil row hp =>
    let regs : Registers ℕ := ⟨tail,row,c,d⟩
    let s10 := state heap regs (caller::stack) tape 10
    let s16 := state heap regs (caller::stack) tape 16
    let final := state heap (caller.saved.set caller.destination tail) stack tape caller.continuation
    have h10 : tickNatural program s10 = some ⟨s16,[],0⟩ := by
      simp [s10,s16,regs,state,tickNatural,program,Registers.get,tagBranch,hp]
    have h16 : tickNatural program s16 = some ⟨final,[],0⟩ := by
      simp [s16,final,regs,state,tickNatural,program,Registers.get]
    exact ⟨[],tail,rfl,by simpa using hy,by simpa [s10,final] using NaturalRun.step h10 (.step h16 (.done final))⟩
  | @cons row head rest b bs hp hb _ ih =>
    let saved := caller :: stack
    let reps : Registers ℕ := ⟨tail,row,c,d⟩
    let s10 := state heap reps saved tape 10
    let s11 := state heap reps saved tape 11
    let s12 := state heap ⟨tail,row,head,d⟩ saved tape 12
    let args : Registers ℕ := ⟨tail,rest,head,d⟩
    let s13 := state heap args saved tape 13
    let frame : Frame ℕ 18 := ⟨14,.r0,args⟩
    have h10 : tickNatural program s10 = some ⟨s11,[],0⟩ := by
      simp [s10,s11,reps,state,tickNatural,program,Registers.get,tagBranch,hp]
    have h11 : tickNatural program s11 = some ⟨s12,[],0⟩ := by
      simp [s11,s12,reps,state,tickNatural,program,Registers.get,Registers.set,hp]
    have h12 : tickNatural program s12 = some ⟨s13,[],0⟩ := by
      simp [s12,s13,args,state,tickNatural,program,Registers.get,Registers.set,hp]
    have h13 : tickNatural program s13 = some ⟨state heap args (frame::saved) tape 10,[],0⟩ := rfl
    obtain ⟨ext, joined, hlen, hrep, hrun⟩ := ih head d frame saved
    let grown := heap++ext
    let s14 := state grown ⟨joined,rest,head,d⟩ saved tape 14
    change NaturalRun program (6*bs.length+2) (state heap args (frame::saved) tape 10) [] s14 at hrun
    let cell : Cell ℕ := .pair head joined
    let fresh := grown.length
    let updated := grown++[cell]
    let s16 := state updated ⟨fresh,rest,head,d⟩ saved tape 16
    let final := state updated (caller.saved.set caller.destination fresh) stack tape caller.continuation
    have h14 : tickNatural program s14 = some ⟨s16,[],0⟩ := by
      simp [s14,s16,fresh,cell,updated,state,tickNatural,program,Registers.get,Registers.set,allocateNatural,Recipe.cell]
    have h16 : tickNatural program s16 = some ⟨final,[],0⟩ := by
      simp [s16,final,saved,state,tickNatural,program,Registers.get]
    have hfinish : NaturalRun program 2 s14 [] final := by
      simpa using NaturalRun.step h14 (.step h16 (.done final))
    have hrun := NaturalRun.step h10 (.step h11 (.step h12 (.step h13 (join hrun hfinish))))
    have he : 6*bs.length+2+2+1+1+1+1 = 6*(b::bs).length+2 := by simp only [List.length_cons]; omega
    change NaturalRun program (6*bs.length+2+2+1+1+1+1) s10 [] final at hrun
    rw [he] at hrun
    have hlist : BoolList updated fresh (b :: (bs++ys)) :=
      .cons (by simp [fresh,updated,cell]) (lookup_extend (lookup_extend hb ext) [cell])
        (boolList_extend hrep [cell])
    refine ⟨ext++[cell],fresh,by simp [hlen],?_,?_⟩
    · simpa only [updated,grown,List.append_assoc,List.cons_append] using hlist
    · simpa only [s10,reps,saved,final,updated,grown,List.append_assoc] using hrun

private theorem flatten_subroutine {n : ℕ} {heap : NaturalHeap} {a : ℕ} {refs : List ℕ}
    {rows : List (Flags n)} (ht : PointerList heap a refs)
    (hr : List.Forall₂ (fun ptr (x : Flags n) => BoolList heap ptr x.toList) refs rows)
    (b c d : ℕ) (caller : Frame ℕ 18) (stack : List (Frame ℕ 18)) (tape : Bits) :
    ∃ ext root, ext.length = n*rows.length ∧ BoolList (heap++ext) root (rows.map Vector.toList).flatten ∧
      NaturalRun program ((6*n+8)*rows.length+2) (state heap ⟨a,b,c,d⟩ (caller::stack) tape 1) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction hr generalizing a b c d caller stack with
  | nil =>
    cases ht with
    | nil hp =>
      let r : Registers ℕ := ⟨a,b,c,d⟩
      let s1 := state heap r (caller::stack) tape 1
      let s2 := state heap r (caller::stack) tape 2
      let final := state heap (caller.saved.set caller.destination a) stack tape caller.continuation
      have h1 : tickNatural program s1 = some ⟨s2,[],0⟩ := by
        simp [s1,s2,r,state,tickNatural,program,Registers.get,tagBranch,hp]
      have h2 : tickNatural program s2 = some ⟨final,[],0⟩ := by
        simp [s2,final,r,state,tickNatural,program,Registers.get]
      exact ⟨[],a,by simp,by simpa using BoolList.nil hp,
        by simpa [s1,final] using NaturalRun.step h1 (.step h2 (.done final))⟩
  | @cons head x refs rows hrow _ ih =>
    cases ht with
    | @cons a head tail refs hp htail =>
      let saved := caller :: stack
      let s1 := state heap ⟨a,b,c,d⟩ saved tape 1
      let s3 := state heap ⟨a,b,c,d⟩ saved tape 3
      let s4 := state heap ⟨a,head,c,d⟩ saved tape 4
      let args : Registers ℕ := ⟨tail,head,c,d⟩
      let s5 := state heap args saved tape 5
      let frame : Frame ℕ 18 := ⟨6,.r0,args⟩
      have h1 : tickNatural program s1 = some ⟨s3,[],0⟩ := by
        simp [s1,s3,state,tickNatural,program,Registers.get,tagBranch,hp]
      have h3 : tickNatural program s3 = some ⟨s4,[],0⟩ := by
        simp [s3,s4,state,tickNatural,program,Registers.get,Registers.set,hp]
      have h4 : tickNatural program s4 = some ⟨s5,[],0⟩ := by
        simp [s4,s5,args,state,tickNatural,program,Registers.get,Registers.set,hp]
      have h5 : tickNatural program s5 = some ⟨state heap args (frame::saved) tape 1,[],0⟩ := rfl
      obtain ⟨ext, flat, hlen, hbits, hrun⟩ := ih htail head c d frame saved
      let grown := heap++ext
      let appendArgs : Registers ℕ := ⟨flat,head,c,d⟩
      let s6 := state grown appendArgs saved tape 6
      let appendCaller : Frame ℕ 18 := ⟨7,.r0,appendArgs⟩
      change NaturalRun program ((6*n+8)*rows.length+2) (state heap args (frame::saved) tape 1) [] s6 at hrun
      have h6 : tickNatural program s6 = some ⟨state grown appendArgs (appendCaller::saved) tape 10,[],0⟩ := rfl
      obtain ⟨more, root, hmore, hjoined, happend⟩ :=
        append_subroutine (boolList_extend hrow ext) hbits c d appendCaller saved tape
      let updated := grown++more
      let s7 := state updated ⟨root,head,c,d⟩ saved tape 7
      let final := state updated (caller.saved.set caller.destination root) stack tape caller.continuation
      rw [Vector.length_toList] at happend
      change NaturalRun program (6*n+2) (state grown appendArgs (appendCaller::saved) tape 10) [] s7 at happend
      have h7 : tickNatural program s7 = some ⟨final,[],0⟩ := by
        simp [s7,final,saved,state,tickNatural,program,Registers.get]
      have suffix := NaturalRun.step h6 (join happend (.step h7 (.done final)))
      have full := NaturalRun.step h1 (.step h3 (.step h4 (.step h5 (join hrun suffix))))
      let k := (6*n+8)*rows.length+2 + (6*n+2+(0+1)+1)+1+1+1+1
      change NaturalRun program k s1 [] final at full
      have hcount : k = (6*n+8)*(x::rows).length+2 := by
        simp only [k,List.length_cons,Nat.mul_add,Nat.mul_one]
        omega
      rw [hcount] at full
      have hext : (ext++more).length = n*(x::rows).length := by
        simp only [List.length_append,hlen,hmore,Vector.length_toList,List.length_cons,Nat.mul_add,Nat.mul_one]
      refine ⟨ext++more,root,hext,?_,?_⟩
      · simpa only [List.map_cons,List.flatten_cons,grown,List.append_assoc] using hjoined
      · simpa only [s1,saved,final,updated,grown,List.append_assoc] using full

private theorem vector_toList_ofFn {α : Type} {n : ℕ} (v : Vector α n) :
    v.toList = List.ofFn (fun i : Fin n => v[i.val]) := by
  rw [← Vector.toList_ofFn, Vector.ofFn_getElem]

theorem flatten_value {n : ℕ} (a : PairFlags n) :
    (a.toList.map Vector.toList).flatten = (RetainedMassTableProgram.pairOrder n).map (flag a) := by
  unfold RetainedMassTableProgram.pairOrder List.product
  simp only [List.map_flatMap,List.flatten_eq_flatMap,Function.comp_def,
    List.finRange,List.map_ofFn,flag,vector_toList_ofFn]
  have h (f : Fin n → List Bool) : List.ofFn f = (List.ofFn (fun i : Fin n => i)).map f := by
    simp only [List.map_ofFn, Function.comp_def]
  rw [h (fun i => List.ofFn (fun j : Fin n => a[i.val][j.val])), List.flatMap_map]
  rfl

theorem natural_trace {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {mask : PairFlags n}
    (h : RowsAt heap r.a mask) (tape : Bits) :
    ∃ ext root, ext.length = n*n ∧
      BoolList (heap++ext) root ((RetainedMassTableProgram.pairOrder n).map (flag mask)) ∧
      NaturalRun program ((6*n+8)*n+3) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r3 root) [] tape 8) := by
  obtain ⟨refs,hptr,hrows⟩ := h
  let caller : Frame ℕ 18 := ⟨8,.r3,r⟩
  obtain ⟨ext,root,hlen,hbool,hrun⟩ := flatten_subroutine hptr hrows r.b r.c r.d caller [] tape
  rw [flatten_value] at hbool
  have hcall : tickNatural program (state heap r [] tape 0) =
    some ⟨state heap r [caller] tape 1,[],0⟩ := rfl
  refine ⟨ext,root,by simpa only [Vector.length_toList] using hlen,hbool,?_⟩
  simpa [caller,Nat.add_assoc] using NaturalRun.step hcall hrun

end DirectedFlowCutGap.FlattenDemandMaskProgram
