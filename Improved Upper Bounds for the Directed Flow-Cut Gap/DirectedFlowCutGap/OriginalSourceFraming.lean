import DirectedFlowCutGap.RawSourceFraming
import DirectedFlowCutGap.SourceFrameCompletion
import DirectedFlowCutGap.ReferenceSourcePadding
import DirectedFlowCutGap.BinaryCounters

/-! Execute the three raw source-table calls on the literal input. The
driver records actual requests, including attempts past the end, so the
reference machine's default false bit cannot make a truncated wire valid. -/
namespace DirectedFlowCutGap.OriginalSourceFraming

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open RawSourceFraming ReferenceSourcePadding
open PackingSourceInput (encode initial)
open WordPairTableRead (Table)

private structure Finished where
  state : BitState 64
  paid : ℕ
  read : ℕ

private def execute : ℕ → BitState 64 → ℕ → ℕ → Option Finished
  | 0, _, _, _ => none
  | fuel+1, s, paid, read =>
      let step := attempt program s
      match step.result with
      | none => some ⟨s,paid+step.operations,read⟩
      | some r => execute fuel r.state (paid+step.operations) (read+requests r.events)

private theorem execute_eq {t paid : ℕ} {s u : BitState 64} {events : List Event}
    (ran : Run program t paid s events u) (halt : (attempt program u).result = none)
    (fuel accrued read : ℕ) (enough : t < fuel) :
    execute fuel s accrued read = some ⟨u,accrued+paid+(attempt program u).operations,read+requests events⟩ := by
  induction ran generalizing fuel accrued read with
  | done s =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [execute,halt,requests]
  | @step s mid r t paid events step tail ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have first := (attempt_result program s).trans step
          simp only [execute,first,success_cost first,requests_append]
          simpa only [Nat.add_assoc] using ih halt fuel (accrued+r.cost)
            (read+requests r.events) (by omega)

/-- Run the framing interpreter with fuel based only on the supplied wire.
The second result is the charge in the physical bit model through the halt. -/
def read (source : Bits) : Option (BitState 64) × ℕ :=
  match execute (8*(source.length+6)+1) (initial source) 0 0 with
  | none => (none,0)
  | some r => (if r.read≤source.length then some r.state else none,r.paid)

private theorem short_prefix {source used suffix pad : Bits} (wire : source++pad=used++suffix)
    (size : used.length≤source.length) : source=used++source.drop used.length := by
  have taken := congrArg (List.take used.length) wire
  rw [List.take_append_of_le_length size,List.take_left] at taken
  calc
    source = source.take used.length ++ source.drop used.length := (List.take_append_drop ..).symm
    _ = used ++ source.drop used.length := congrArg (· ++ source.drop used.length) taken

private theorem overflow_rejected {source suffix : Bits} {k : ℕ}
    {c m d : List (Bits × Bits)} (wire : source++List.replicate k false=encode c m d++suffix)
    (overflow : ¬ (encode c m d).length≤source.length) :
    ¬ ∃ costs matrix demands tail, source=encode costs matrix demands++tail := by
  rintro ⟨costs,matrix,demands,tail,plain⟩
  have padded : source++List.replicate k false=encode costs matrix demands++(tail++List.replicate k false) := by
    rw [plain,List.append_assoc]
  obtain ⟨rfl,rfl,rfl,_⟩ := SourceFrameCompletion.unique (wire.symm.trans padded)
  exact overflow (by rw [plain,List.length_append]; omega)

private theorem observe (source : Bits) : ∃ r c m d,
    execute (8*(source.length+6)+1) (initial source) 0 0 = some r ∧
    r.read = (encode c m d).length ∧
    r.state.source=source.drop r.read ∧
    Table (eraseState r.state).heap (eraseState r.state).registers.a c ∧
    Table (eraseState r.state).heap (eraseState r.state).registers.b m ∧
    Table (eraseState r.state).heap (eraseState r.state).registers.d d ∧
    r.state.pc=51 ∧ r.state.stack=[] ∧ value r.state.next=r.state.heap.length ∧
    r.state.Bounded (1+8*(source.length+6)) (8*(source.length+6)) ∧
    (if r.read≤source.length then source=encode c m d++r.state.source
      else ¬ ∃ costs matrix demands tail, source=encode costs matrix demands++tail) ∧
    r.paid≤539136*(source.length+7)^3+80 := by
  obtain ⟨k,hk,c,m,d,suffix,wire⟩ := SourceFrameCompletion.all source
  obtain ⟨paid,out,ran,hc,hm,hd,pc,_,stack,dense,bounded,bound⟩ := read_framed c m d suffix
  have tape : (initial (encode c m d++suffix)).source=source++List.replicate k false := wire.symm
  have low := trim ran source k tape
  simp only [requests_literal] at low
  let taken := (encode c m d).length
  let final := withSource out (source.drop taken)
  have halted : (attempt program final).result=none := by simp [attempt,final,withSource,program,pc,stopped]
  have charge : (attempt program final).operations=80 := by
    simp [attempt,final,withSource,program,pc,stopped,controlCost]
  have total : (encode c m d++suffix).length=source.length+k := by
    rw [← wire,List.length_append,List.length_replicate]
  have room : framingSteps c m d < 8*(source.length+6)+1 := by
    have steps := instructions_bound c m d
    simp only [List.length_append] at total
    omega
  have execution : execute (8*(source.length+6)+1) (initial source) 0 0 = some ⟨final,paid+80,taken⟩ := by
    have h := execute_eq low halted (8*(source.length+6)+1) 0 0 room
    change execute (8*(source.length+6)+1) (initial source) 0 0 =
      some ⟨final,0+paid+(attempt program final).operations,0+requests ((encode c m d).map Event.request)⟩ at h
    simpa only [Nat.zero_add,requests_literal,charge] using h
  have within : framingSteps c m d≤8*(source.length+6) := by omega
  refine ⟨⟨final,paid+80,taken⟩,c,m,d,execution,rfl,rfl,?_,?_,?_,pc,stack,dense,?_,?_,?_⟩
  · simpa only [final,withSource,eraseState,State.map] using hc
  · simpa only [final,withSource,eraseState,State.map] using hm
  · simpa only [final,withSource,eraseState,State.map] using hd
  · exact bounded.mono (Nat.add_le_add_left within 1) within
  · by_cases fits : taken≤source.length
    · simp only [fits,ite_true]
      change source=encode c m d++source.drop taken
      exact short_prefix wire fits
    · simpa only [fits,ite_false] using overflow_rejected wire fits
  · rw [total] at bound
    have cap : source.length+k+1≤source.length+7 := by omega
    exact Nat.add_le_add_right (bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cap 3))) 80

theorem read_paid (source : Bits) : (read source).2≤539136*(source.length+7)^3+80 := by
  obtain ⟨r,c,m,d,executed,_,_,_,_,_,_,_,_,_,_,paid⟩ := observe source
  simpa only [read,executed] using paid

theorem read_bounded {source : Bits} {out : BitState 64} (accepted : (read source).1=some out) :
    out.Bounded (1+8*(source.length+6)) (8*(source.length+6)) := by
  obtain ⟨r,c,m,d,executed,_,_,_,_,_,_,_,_,bounded,_,_⟩ := observe source
  simp only [read,executed] at accepted
  split at accepted
  · obtain rfl := Option.some.inj accepted
    exact bounded
  · contradiction

theorem read_none (source : Bits) :
    (read source).1=none ↔ ¬ ∃ costs matrix demands tail, source=encode costs matrix demands++tail := by
  obtain ⟨r,c,m,d,executed,_,_,_,_,_,_,_,_,_,semantics,_⟩ := observe source
  by_cases fits : r.read≤source.length
  · simp only [fits,ite_true] at semantics
    have frames : ∃ costs matrix demands tail, source=encode costs matrix demands++tail :=
      ⟨c,m,d,r.state.source,semantics⟩
    simp only [read,executed,fits,ite_true,Option.some_ne_none,frames,not_true_eq_false]
  · simp only [fits,ite_false] at semantics
    simp [read,executed,fits,semantics]

/-- The same executable framing entry retains the original ordered, padded
fields and exact unused source. Payload validation can use these roots. -/
theorem read_correct {source : Bits} {c m d : List (Bits × Bits)} {suffix : Bits}
    (parsed : source=encode c m d++suffix) :
    ∃ out, (read source).1=some out ∧ out.source=suffix ∧
      Table (eraseState out).heap (eraseState out).registers.a c ∧
      Table (eraseState out).heap (eraseState out).registers.b m ∧
      Table (eraseState out).heap (eraseState out).registers.d d ∧
      out.pc=51 ∧ out.stack=[] ∧ value out.next=out.heap.length := by
  obtain ⟨r,a,b,f,executed,_,_,hc,hm,hd,pc,stack,dense,_,semantics,_⟩ := observe source
  by_cases fits : r.read≤source.length
  · simp only [fits,ite_true] at semantics
    obtain ⟨rfl,rfl,rfl,same⟩ := SourceFrameCompletion.unique (semantics.symm.trans parsed)
    exact ⟨r.state,by simp only [read,executed,fits,ite_true],same,hc,hm,hd,pc,stack,dense⟩
  · simp only [fits,ite_false] at semantics
    exact (semantics ⟨c,m,d,suffix,parsed⟩).elim

private def requested : List Event → Bool
  | .request _ :: _ => true
  | _ => false

private theorem request_digit {s : BitState 64} {r : Result Bits 64}
    (step : (attempt program s).result=some r) : requests r.events=(requested r.events).toNat := by
  rw [attempt_result] at step
  cases instruction : program s.pc <;> simp only [tick,instruction] at step
  all_goals try contradiction
  all_goals try (injection step with equal; subst r; rfl)
  all_goals
    split at step
    all_goals first | contradiction | (injection step with equal; subst r; rfl)

/-- Record constructors reached by the physical heap append and call stack.
A returned or borrowed list tail reuses its existing cells. The copied bit
fields and source reads already have separate charges in `attempt`. -/
private def attemptRecords {C : ℕ} (p : Program C) (s : BitState C) (completed : Bool) : ℕ :=
  match p s.pc with
  | .make _ _ _ => s.heap.length+1
  | .request _ _ => s.heap.length+2
  | .call _ _ _ => 2
  | .emit _ _ => completed.toNat
  | _ => 0

private theorem append_record_cost {heap out : Heap} {cell : Cell Bits} {cost : ℕ}
    (h : AppendCellExec heap cell out cost) : 2*(heap.length+1) ≤ cost := by
  induction h with
  | nil record => simp
  | cons record rest ih => simp only [List.length_cons]; omega

private theorem attempt_records_paid {C : ℕ} (p : Program C) (s : BitState C) :
    attemptRecords p s (attempt p s).result.isSome ≤ (attempt p s).operations := by
  have append (cell : Cell Bits) := append_record_cost (appendCell_exec s.heap cell)
  cases code : p s.pc with
  | make dst recipe next =>
      have copied := append (recipe.cell s.registers)
      simp only [attemptRecords,attempt,code,success,allocate]
      omega
  | request dst next =>
      let bit := s.source.headD false
      have copied := append (.flag bit)
      simp only [attemptRecords,attempt,code,success,allocate]
      change s.heap.length+2 ≤ (appendCell s.heap (.flag bit)).2+(increment true s.next).2+
        (EncodedSequenceAccess.copyBits s.next).2+controlCost C
      omega
  | call entry cont dst => simp only [attemptRecords,attempt,code,success,controlCost]; omega
  | emit src next =>
      simp only [attemptRecords,attempt,code]
      rcases read : (lookup (EncodedSequenceAccess.copyBits (s.registers.get src)).1 s.heap).1 with _ | cell
      · simp only [Option.isSome_none,Bool.toNat_false,stopped,Nat.zero_le]
      · cases cell <;> simp only [Option.isSome_some,Option.isSome_none,Bool.toNat_true,Bool.toNat_false,stopped,success,controlCost] <;> omega
  | halt | move _ _ _ | branch _ _ _ _ _ | field _ _ _ _ | ret _ =>
      rw [attemptRecords,code]
      exact Nat.zero_le _

private structure BinaryResult where
  state : BitState 64
  reads : Bits

/-- Fuel and request counting use actual binary arithmetic. The natural
measure in the termination proof is erased. -/
private def binaryExecute (fuel : Bits) (s : BitState 64) (reads : Bits) : (Option BinaryResult × ℕ) × ℕ :=
  let zero := isZero fuel
  if empty : zero.1 = true then ((none,zero.2+8),0)
  else
    let step := attempt program s
    let records := attemptRecords program s step.result.isSome
    match step.result with
    | none => ((some ⟨s,reads⟩,zero.2+step.operations+16),records)
    | some r =>
        let next := predCore fuel
        let count := increment (requested r.events) reads
        let tail := binaryExecute next.1 r.state count.1
        ((tail.1.1,tail.1.2+step.operations+zero.2+next.2+count.2+16),tail.2+records)
termination_by value fuel
decreasing_by
  have positive : 0<value fuel := Nat.pos_of_ne_zero (fun h => empty ((isZero_spec fuel).1.mpr h))
  have fewer := (predCore_spec fuel).1 positive
  change value (predCore fuel).1 < value fuel
  omega

private def previousBinaryExecute (fuel : Bits) (s : BitState 64) (reads : Bits) : Option BinaryResult × ℕ :=
  let zero := isZero fuel
  if empty : zero.1 = true then (none,zero.2+8)
  else
    let step := attempt program s
    match step.result with
    | none => (some ⟨s,reads⟩,zero.2+step.operations+16)
    | some r =>
        let next := predCore fuel
        let count := increment (requested r.events) reads
        let tail := previousBinaryExecute next.1 r.state count.1
        (tail.1,tail.2+step.operations+zero.2+next.2+count.2+16)
termination_by value fuel
decreasing_by
  have positive : 0<value fuel := Nat.pos_of_ne_zero (fun h => empty ((isZero_spec fuel).1.mpr h))
  have fewer := (predCore_spec fuel).1 positive
  change value (predCore fuel).1 < value fuel
  omega

private theorem binaryExecute_reference (fuel : Bits) (s : BitState 64) (reads : Bits) :
    (binaryExecute fuel s reads).1=previousBinaryExecute fuel s reads := by
  induction count : value fuel using Nat.strong_induction_on generalizing fuel s reads with
  | h k ih =>
    rw [binaryExecute,previousBinaryExecute]
    by_cases stopped : (isZero fuel).1=true
    · simp only [stopped,dite_true]
    · simp only [stopped,Bool.false_eq_true,dite_false]
      cases step : (attempt program s).result with
      | none => rfl
      | some result =>
          have positive := Nat.pos_of_ne_zero (fun h => stopped ((isZero_spec fuel).1.mpr h))
          have reduced := (predCore_spec fuel).1 positive
          have fewer : value (predCore fuel).1 < k := by omega
          have tail := ih _ fewer (predCore fuel).1 result.state
            (increment (requested result.events) reads).1 rfl
          dsimp only
          rw [tail]

private theorem binaryExecute_records (fuel : Bits) (s : BitState 64) (reads : Bits) :
    (binaryExecute fuel s reads).2 ≤ (binaryExecute fuel s reads).1.2 := by
  induction count : value fuel using Nat.strong_induction_on generalizing fuel s reads with
  | h k ih =>
    have cost := attempt_records_paid program s
    rw [binaryExecute]
    split
    · exact Nat.zero_le _
    · rename_i active
      cases step : (attempt program s).result with
      | none =>
        simp only [step,Option.isSome_none]
        simpa only [step,Option.isSome_none] using cost.trans (by omega)
      | some result =>
        have positive := Nat.pos_of_ne_zero (fun h => active ((isZero_spec fuel).1.mpr h))
        have reduced := (predCore_spec fuel).1 positive
        have fewer : value (predCore fuel).1 < k := by omega
        have tail := ih _ fewer (predCore fuel).1 result.state
          (increment (requested result.events) reads).1 rfl
        simp only [step,Option.isSome_some] at cost ⊢
        omega

private def controls (fuelWidth readWidth rounds : ℕ) : ℕ :=
  (rounds+1)*(64*(fuelWidth+readWidth+rounds+2))

private theorem binaryExecute_ok (fuel : Bits) (s : BitState 64) (reads : Bits) (prior : ℕ)
    {r : Finished} (ran : execute (value fuel) s prior (value reads)=some r) :
    ∃ out, (binaryExecute fuel s reads).1.1=some out ∧ out.state=r.state ∧ value out.reads=r.read ∧
      out.reads.length≤reads.length+value fuel ∧
      (binaryExecute fuel s reads).1.2+prior≤r.paid+controls fuel.length reads.length (value fuel) := by
  induction hfuel : value fuel using Nat.strong_induction_on generalizing fuel s reads prior r with
  | h amount ih =>
    rw [← hfuel]
    have zero := isZero_spec fuel
    by_cases empty : (isZero fuel).1=true
    · rw [zero.1.mp empty] at ran
      cases ran
    have pos : 0<value fuel := Nat.pos_of_ne_zero (fun h => empty (zero.1.mpr h))
    have dec : value fuel=value fuel-1+1 := by omega
    rw [dec,execute] at ran
    rw [binaryExecute]
    simp only [empty]
    cases performed : (attempt program s).result with
    | none =>
        simp only [performed,Option.some.injEq] at ran
        subst r
        refine ⟨⟨s,reads⟩,rfl,rfl,rfl,Nat.le_add_right _ _,?_⟩
        have localCost : (isZero fuel).2+16≤64*(fuel.length+reads.length+value fuel+2) := by omega
        have bound : (isZero fuel).2+16≤controls fuel.length reads.length (value fuel) := localCost.trans (by
          unfold controls
          exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
        change (isZero fuel).2+(attempt program s).operations+16+prior≤
          prior+(attempt program s).operations+controls fuel.length reads.length (value fuel)
        omega
    | some step =>
        simp only [performed] at ran
        let next := predCore fuel
        let read := increment (requested step.events) reads
        obtain ⟨fewer,fw,fc⟩ := predCore_spec fuel
        obtain ⟨valueRead,rw,rc⟩ := increment_spec (requested step.events) reads
        have nextVal : value next.1=value fuel-1 := by have h := fewer pos; dsimp only [next]; omega
        have readVal : value read.1=value reads+requests step.events := by
          rw [request_digit performed]
          exact valueRead
        have nextRun : execute (value next.1) step.state (prior+(attempt program s).operations)
            (value read.1)=some r := by rwa [nextVal,readVal]
        obtain ⟨out,oh,os,ov,ow,oc⟩ := ih (value next.1) (by omega) next.1 step.state read.1
          (prior+(attempt program s).operations) nextRun rfl
        have remaining : out.reads.length≤reads.length+value fuel := by
          change read.1.length≤reads.length+1 at rw
          omega
        have sub : next.1.length+read.1.length+value next.1+2 ≤ fuel.length+reads.length+value fuel+2 := by
          change next.1.length≤fuel.length at fw
          change read.1.length≤reads.length+1 at rw
          omega
        have limit : controls next.1.length read.1.length (value next.1) ≤
            value fuel*(64*(fuel.length+reads.length+value fuel+2)) := by
          unfold controls
          rw [show value next.1+1=value fuel by omega]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ sub)
        have localCost : (isZero fuel).2+next.2+read.2+16≤64*(fuel.length+reads.length+value fuel+2) := by
          change next.2≤8*(fuel.length+1) at fc
          change read.2≤8*(reads.length+1) at rc
          omega
        refine ⟨out,oh,os,ov,remaining,?_⟩
        unfold controls
        rw [Nat.add_mul,Nat.one_mul]
        change (binaryExecute next.1 step.state read.1).1.2+(attempt program s).operations+
          (isZero fuel).2+next.2+read.2+16+prior≤_
        omega

private def fuelBits (length : Bits) : Bits × ℕ := addCanonical (false::false::false::length) (49 : ℕ).bits

private theorem fuel_value (length : Bits) : value (fuelBits length).1=8*(value length+6)+1 := by
  have h := (canonical_values (false::false::false::length) (49 : ℕ).bits).1
  simp only [value,Bool.toNat_false,Nat.zero_add,value_bits] at h
  unfold fuelBits
  omega

/-- A literal binary length, fuel, and request count guard the same fixed
framing program. All counts here are charges of the reference bit model. -/
def readBinaryWithRecords (source : Bits) : (Option (BitState 64) × ℕ) × ℕ :=
  let len := BinaryCounters.lengthBits source
  let fuel := fuelBits len.1
  let run := binaryExecute fuel.1 (initial source) []
  let setup := len.2+fuel.2+run.1.2+24
  let framed := match run.1.1 with
    | none => (none,setup)
    | some r =>
        let within := lessEqual r.reads len.1
        (if within.1 then some r.state else none,setup+within.2)
  (framed,run.2)

def readBinary (source : Bits) : Option (BitState 64) × ℕ := (readBinaryWithRecords source).1

def readBinaryReference (source : Bits) : Option (BitState 64) × ℕ :=
  let len := BinaryCounters.lengthBits source
  let fuel := fuelBits len.1
  let run := previousBinaryExecute fuel.1 (initial source) []
  let setup := len.2+fuel.2+run.2+24
  match run.1 with
  | none => (none,setup)
  | some r =>
      let within := lessEqual r.reads len.1
      (if within.1 then some r.state else none,setup+within.2)

theorem readBinary_reference (source : Bits) : (readBinaryWithRecords source).1=readBinaryReference source := by
  simp only [readBinaryWithRecords,readBinaryReference,binaryExecute_reference]

theorem readBinary_records_paid (source : Bits) : (readBinaryWithRecords source).2 ≤ (readBinary source).2 := by
  let len := BinaryCounters.lengthBits source
  let fuel := fuelBits len.1
  let run := binaryExecute fuel.1 (initial source) []
  have work := binaryExecute_records fuel.1 (initial source) []
  change run.2 ≤ run.1.2 at work
  change run.2 ≤ (match run.1.1 with
    | none => (none,len.2+fuel.2+run.1.2+24)
    | some r => (if (lessEqual r.reads len.1).1 then some r.state else none,
        len.2+fuel.2+run.1.2+24+(lessEqual r.reads len.1).2)).2
  cases run.1.1 <;> dsimp only <;> omega

theorem readBinary_checked (source : Bits) :
    let n := source.length
    let fuel := 8*(n+6)+1
    (readBinary source).1=(read source).1 ∧
      (readBinary source).2≤539136*(n+7)^3+80+
        (fuel+1)*(64*(2*fuel+3))+16*(n+1)^2+32*(n+10)+17*(fuel+1)+24 := by
  let n := source.length
  let len := BinaryCounters.lengthBits source
  let fuel := fuelBits len.1
  let steps := 8*(n+6)+1
  let run := binaryExecute fuel.1 (initial source) []
  obtain ⟨lenValue,lenWidth,lenPaid⟩ := BinaryCounters.lengthBits_spec source
  change value len.1=n at lenValue
  change len.1.length≤n+1 at lenWidth
  change len.2≤16*(n+1)^2 at lenPaid
  have fv : value fuel.1=steps := (fuel_value len.1).trans (by rw [lenValue])
  have fw : fuel.1.length≤steps+1 := by
    have exactWidth := (canonical_values (false::false::false::len.1) (49 : ℕ).bits).2.2.1
    change fuel.1.length=Nat.size (value (false::false::false::len.1)+value (49 : ℕ).bits) at exactWidth
    rw [← (canonical_values (false::false::false::len.1) (49 : ℕ).bits).1] at exactWidth
    change fuel.1.length=Nat.size (value fuel.1) at exactWidth
    rw [exactWidth,fv]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_succ _)
  have fuelPaid : fuel.2≤32*(n+10) := by
    have shifted : (false::false::false::len.1).length≤n+8 := by
      simp only [List.length_cons]
      omega
    have constant : (49 : ℕ).bits.length≤n+8 := (by decide : (49 : ℕ).bits.length≤8).trans (by omega)
    exact (canonical_charges shifted constant).1
  obtain ⟨ref,c,m,d,executed,_,_,_,_,_,_,_,_,_,_,paid⟩ := observe source
  have ready : execute (value fuel.1) (initial source) 0 (value [])=some ref := by rwa [fv]
  obtain ⟨out,result,state,count,width,work⟩ := binaryExecute_ok fuel.1 (initial source) [] 0 ready
  have cost : run.1.2≤ref.paid+(steps+1)*(64*(2*steps+3)) := by
    have paid : run.1.2≤ref.paid+controls fuel.1.length ([] : Bits).length (value fuel.1) := by
      simpa only [run,Nat.add_zero] using work
    apply paid.trans
    rw [fv]
    unfold controls
    simp only [List.length_nil,Nat.add_zero]
    have larger : fuel.1.length+steps+2≤2*steps+3 := by omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ larger)) _
  have within := lessEqual_spec out.reads len.1
  have guard : (lessEqual out.reads len.1).1=true ↔ ref.read≤n := by
    simpa only [count,lenValue] using within.1
  have readWidth : max out.reads.length len.1.length≤steps := by
    apply max_le
    · simpa only [List.length_nil,Nat.zero_add,fv] using width
    · exact lenWidth.trans (by dsimp only [steps]; omega)
  have comparePaid := within.2.trans (Nat.mul_le_mul_left 17 (Nat.add_le_add_right readWidth 1))
  have performed : readBinary source =
      (if (lessEqual out.reads len.1).1 then some out.state else none,
        len.2+fuel.2+run.1.2+24+(lessEqual out.reads len.1).2) := by
    unfold readBinary readBinaryWithRecords
    have found : run.1.1=some out := result
    change (match run.1.1 with
      | none => (none,len.2+fuel.2+run.1.2+24)
      | some r => (if (lessEqual r.reads len.1).1 then some r.state else none,
          len.2+fuel.2+run.1.2+24+(lessEqual r.reads len.1).2)) = _
    rw [found]
  rw [performed]
  refine ⟨?_,?_⟩
  · simp only [read,executed,guard,state,n]
  · change len.2+fuel.2+run.1.2+24+(lessEqual out.reads len.1).2≤539136*(n+7)^3+80+
      (steps+1)*(64*(2*steps+3))+16*(n+1)^2+32*(n+10)+17*(steps+1)+24
    change ref.paid≤539136*(n+7)^3+80 at paid
    omega

end DirectedFlowCutGap.OriginalSourceFraming
