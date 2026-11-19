import DirectedFlowCutGap.BinarySigned
import DirectedFlowCutGap.BinaryComparisonProgram
import DirectedFlowCutGap.IntegralNetworkFlow

/-!
# Residual edge test over stored integral flow

The fixed program checks whether the signed skew flow amount is strictly
less than the nonnegative capacity. A negative amount gives a residual
edge. Otherwise the tester compares the two stored magnitudes. Zero flow
uses the canonical nonnegative sign.
-/

namespace DirectedFlowCutGap.ResidualCapacityProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open BinarySigned (Signed Canonical decode)

def Stored (heap : NaturalHeap) (root : ℕ) (x : Signed) : Prop :=
  ∃ mag sign, heap[root]?=some (.pair mag sign) ∧
    BoolList heap mag x.magnitude ∧ heap[sign]?=some (.flag x.negative)

def comparisonLabel (pc : Fin 48) : Fin 60 := ⟨12+pc.val,by omega⟩

def program : Program 60 := fun pc =>
  if pc.val < 12 then
    match pc.val with
    | 0 => .field .r2 .r0 true 1
    | 1 => .branch .r2 10 2 8 10
    | 2 => .move .r2 .r1 3
    | 3 => .field .r1 .r0 false 4
    | 4 => .move .r0 .r2 5
    | 5 => .call (comparisonLabel 30) 6 .r3
    | 6 => .branch .r3 10 8 9 10
    | 8 => .make .r3 (.flag true) 10
    | 9 => .make .r3 (.flag false) 10
    | _ => .halt
  else if pc.val=58 then .ret .r3
  else ReferenceProgramLabels.instruction comparisonLabel
    (BinaryComparisonProgram.program ⟨pc.val-12,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 60)) (tape : Bits)
    (pc : Fin 60) : NaturalState 60 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def instructions (z : Signed) (cap : Bits) : ℕ :=
  if z.negative then 3 else BinaryComparisonProgram.steps cap z.magnitude+12

def residual (z : Signed) (cap : Bits) : Bool :=
  decide (decode z < (value cap : ℤ))

theorem residual_negative {z : Signed} (canonical : Canonical z) (sign : z.negative=true) (cap : Bits) :
    residual z cap=true := by
  have hn : value z.magnitude ≠ 0 := fun h => Bool.noConfusion (sign.symm.trans (canonical.2 h))
  simp only [residual,decode,sign,ite_true,decide_eq_true_eq]
  have hp : 0<value z.magnitude := Nat.pos_of_ne_zero hn
  omega

theorem residual_nonnegative {z : Signed} (sign : z.negative=false) (cap : Bits) :
    residual z cap = !(lessEqual cap z.magnitude).1 := by
  apply Bool.eq_iff_iff.mpr
  simp only [residual,decode,sign,Bool.false_eq_true,ite_false,decide_eq_true_eq,Int.ofNat_lt]
  rw [Bool.not_eq_true',← Bool.not_eq_true,(lessEqual_spec _ _).1]
  omega

open IntegralNetworkFlow

theorem residual_matches_flow {V : Type} [Fintype V] {c : Capacity V} {s t : V}
    (f : Flow c s t) (u v : V) (z : Signed) (cap : Bits)
    (hz : decode z=f.amount u v) (hc : value cap=c u v) :
    residual z cap = decide (f.amount u v < (c u v : ℤ)) := by
  rw [residual,hz,hc]

/-- Skew-symmetry bounds the magnitude by the larger directed capacity. -/
theorem amount_width {V : Type} [Fintype V] {c : Capacity V} {s t : V}
    (f : Flow c s t) (u v : V) (z : Signed) (hz : decode z=f.amount u v) (hn : Canonical z) :
    z.magnitude.length ≤ (max (c u v) (c v u)).size := by
  rw [BinarySigned.canonical_length z hn,hz]
  apply Nat.size_le_size
  by_cases h : 0 ≤ f.amount u v
  · have hcap : (f.amount u v).natAbs ≤ c u v := by
      rw [← Int.ofNat_le,Int.natAbs_of_nonneg h]
      exact f.upper u v
    exact hcap.trans (le_max_left _ _)
  · have hn : 0 ≤ -(f.amount u v) := by omega
    have hcap : (-(f.amount u v)).natAbs ≤ c v u := by
      rw [← Int.ofNat_le,Int.natAbs_of_nonneg hn]
      have lower := f.lower u v
      omega
    rw [Int.natAbs_neg] at hcap
    exact hcap.trans (le_max_right _ _)

private theorem comparison_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (comparisonLabel pc) = ReferenceProgramLabels.instruction comparisonLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=46
  · have eq : pc=46 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,comparisonLabel,show ¬12+pc.val<12 by omega,show 12+pc.val≠58 by omega]

private theorem join {s u v : NaturalState 60} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem compare_return {heap : NaturalHeap} {r : Registers ℕ} {left right : Bits}
    (hl : BoolList heap r.a left) (hr : BoolList heap r.b right)
    (caller : Frame ℕ 60) (tape : Bits) :
    ∃ ext flag, (heap++ext)[flag]?=some (.flag (lessEqual left right).1) ∧
      NaturalRun program (BinaryComparisonProgram.steps left right+4)
        (state heap r [caller] tape (comparisonLabel 30)) []
        (state (heap++ext) (caller.saved.set caller.destination flag) [] tape caller.continuation) := by
  let initial := BinaryComparisonProgram.state heap heap.length r.a r.b r.c r.d [] tape 30
  obtain ⟨out,run,flag,_,_,ha,hb,hc,hstack,htape,hpc,hn,⟨ext,he,_⟩,_⟩ :=
    BinaryComparisonProgram.compare_high initial rfl rfl hl hr rfl
  have shape : out = BinaryComparisonProgram.state (heap++ext) (heap++ext).length
      r.a r.b r.c out.registers.d [] tape 46 := by
    cases out with
    | mk oh on rs s pc src =>
      cases rs
      simp_all [initial,BinaryComparisonProgram.state]
  have lift := ReferenceProgramLabels.run comparisonLabel BinaryComparisonProgram.program program comparison_slots run
  have lift := ReferenceProgramStack.run program [caller] lift
  rw [shape] at lift
  let before := state (heap++ext) ⟨r.a,r.b,r.c,out.registers.d⟩ [caller] tape (comparisonLabel 46)
  let after := state (heap++ext) (caller.saved.set caller.destination out.registers.d) [] tape caller.continuation
  have body : NaturalRun program (BinaryComparisonProgram.steps left right+3)
      (state heap r [caller] tape (comparisonLabel 30)) [] before := by
    cases r
    simpa [before,initial,state,ReferenceProgramLabels.state,ReferenceProgramStack.state,
      BinaryComparisonProgram.state] using lift
  have ret : tickNatural program before=some ⟨after,[],0⟩ := rfl
  exact ⟨ext,out.registers.d,by simpa only [he,initial,BinaryComparisonProgram.state] using flag,
    join body (.step ret (.done after))⟩

private theorem emit_flag {heap : NaturalHeap} {r : Registers ℕ} (tape : Bits) (b : Bool) :
    NaturalRun program 1 (state heap r [] tape (if b then 8 else 9)) []
      (state (heap++[.flag b]) (r.set .r3 heap.length) [] tape 10) := by
  have store : tickNatural program (state heap r [] tape (if b then 8 else 9)) =
      some ⟨state (heap++[.flag b]) (r.set .r3 heap.length) [] tape 10,[],0⟩ := by
    cases b <;> simp [state,program,tickNatural,allocateNatural,Recipe.cell]
  exact .step store (.done _)

theorem natural_residual {heap : NaturalHeap} {r : Registers ℕ} {z : Signed} {cap : Bits}
    (amount : Stored heap r.a z) (capacity : BoolList heap r.b cap) (canonical : Canonical z) (tape : Bits) :
    ∃ ext regs, (heap++ext)[regs.d]?=some (.flag (residual z cap)) ∧
      NaturalRun program (instructions z cap) (state heap r [] tape 0) []
        (state (heap++ext) regs [] tape 10) := by
  obtain ⟨mag,sign,hpair,hm,hs⟩ := amount
  let test := r.set .r2 sign
  have readSign : tickNatural program (state heap r [] tape 0)=some ⟨state heap test [] tape 1,[],0⟩ := by
    simp [test,state,program,tickNatural,Registers.get,hpair]
  cases negative : z.negative with
  | true =>
    have hbranch : tickNatural program (state heap test [] tape 1)=some ⟨state heap test [] tape 8,[],0⟩ := by
      cases r
      simp [test,state,program,tickNatural,Registers.get,Registers.set,tagBranch,hs,negative]
    let result := test.set .r3 heap.length
    refine ⟨[.flag true],result,?_,?_⟩
    · rw [residual_negative canonical negative cap]
      simp [result,Registers.set]
    · simpa only [instructions,negative,ite_true,List.nil_append,result] using NaturalRun.step readSign
        (NaturalRun.step hbranch (emit_flag (r := test) tape true))
  | false =>
    have hbranch : tickNatural program (state heap test [] tape 1)=some ⟨state heap test [] tape 2,[],0⟩ := by
      cases r
      simp [test,state,program,tickNatural,Registers.get,Registers.set,tagBranch,hs,negative]
    let keep := test.set .r2 r.b
    let pair := keep.set .r1 mag
    let args : Registers ℕ := ⟨r.b,mag,r.b,r.d⟩
    let frame : Frame ℕ 60 := ⟨6,.r3,args⟩
    have saveCap : tickNatural program (state heap test [] tape 2)=some ⟨state heap keep [] tape 3,[],0⟩ := by
      cases r
      rfl
    have readMag : tickNatural program (state heap keep [] tape 3)=some ⟨state heap pair [] tape 4,[],0⟩ := by
      cases r
      simp [test,keep,pair,state,program,tickNatural,Registers.get,Registers.set,hpair]
    have move : tickNatural program (state heap pair [] tape 4)=some ⟨state heap args [] tape 5,[],0⟩ := by
      cases r
      rfl
    have call : tickNatural program (state heap args [] tape 5)=
        some ⟨state heap args [frame] tape (comparisonLabel 30),[],0⟩ := rfl
    obtain ⟨ext,flag,hflag,hcmp⟩ := compare_return capacity hm frame tape (r := args)
    let mid := heap++ext
    let compared := args.set .r3 flag
    let answer := !(lessEqual cap z.magnitude).1
    let result := compared.set .r3 mid.length
    let endPc : Fin 60 := if answer then 8 else 9
    have branch : tickNatural program (state mid compared [] tape 6)=some ⟨state mid compared [] tape endPc,[],0⟩ := by
      cases h : (lessEqual cap z.magnitude).1 <;>
        simp [mid,compared,args,answer,endPc,state,program,tickNatural,Registers.get,Registers.set,tagBranch,hflag,h]
    refine ⟨ext++[.flag answer],result,?_,?_⟩
    · rw [residual_nonnegative negative cap,← List.append_assoc]
      simp [result,mid,compared,args,Registers.set,answer]
    · have trace := NaturalRun.step readSign (.step hbranch (.step saveCap (.step readMag (.step move
        (.step call (join hcmp (.step branch (emit_flag tape answer))))))))
      simp only [instructions,negative,Bool.false_eq_true,ite_false]
      convert trace using 1 <;> first | rfl | omega | simp only [mid,result,List.append_assoc]

private theorem at_entry (s : NaturalState 60) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem residual_edge {H A W : ℕ} {z : Signed} {cap : Bits} (initial : BitState 60)
    (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (amount : Stored (eraseState initial).heap (eraseState initial).registers.a z)
    (capacity : BoolList (eraseState initial).heap (eraseState initial).registers.b cap)
    (canonical : Canonical z) (hz : z.magnitude.length ≤ W) (hw : cap.length ≤ W) :
    ∃ charge out, Run program (instructions z cap) charge initial [] out ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag (decide (decode z < (value cap : ℤ)))) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=10 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 60 H A (16*(2*W+1)+12) := by
  let old := eraseState initial
  obtain ⟨ext,regs,hflag,hbody⟩ := natural_residual amount capacity canonical old.source
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) regs [] old.source 10
  have trace : NaturalRun program (instructions z cap) old [] final := by
    rw [at_entry old hp empty hn]
    exact hbody
  have halt : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace halt
  refine ⟨charge,out,hr,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout]; exact hflag
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have cmp := BinaryComparisonProgram.steps_bound cap z.magnitude
    have k : instructions z cap ≤ 16*(2*W+1)+12 := by
      unfold instructions
      split <;> omega
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.ResidualCapacityProgram
