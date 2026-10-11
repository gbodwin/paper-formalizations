import DirectedFlowCutGap.RationalComparisonProgram
import DirectedFlowCutGap.SourceRowAcceptanceProgram

/-! A single source-driven rational comparator. The real row decoder and
all-denominator validator run first; acceptance continues to real cross-product
arithmetic, while rejection stops before comparison. Source framing and the
specified two-row input shape are explicit. -/
namespace DirectedFlowCutGap.InputRationalComparisonProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def cmpLabel (pc : Fin 158) : Fin 221 := ⟨pc.val,by omega⟩
def readLabel (pc : Fin 60) : Fin 221 := ⟨pc.val+158,by omega⟩
def program : Program 221 := fun pc =>
  if h : pc.val<158 then
    ReferenceProgramLabels.instruction cmpLabel (RationalComparisonProgram.program ⟨pc.val,h⟩)
  else if pc.val=216 then .move .r2 .r0 218
  else if pc.val=218 then .field .r0 .r2 false 219
  else if pc.val=219 then .field .r1 .r2 true 220
  else if pc.val=220 then .field .r1 .r1 false 144
  else if h : pc.val<218 then
    ReferenceProgramLabels.instruction readLabel (SourceRowAcceptanceProgram.program ⟨pc.val-158,by omega⟩)
  else .halt

def rows (x y : BinaryRational.Fraction) : List (Bits × Bits) := [(x.num,x.den),(y.num,y.den)]
def initial (source : Bits) : BitState 221 :=
  ⟨[],[],⟨[],[],[],[]⟩,[],214,source⟩
def instructions (x y : BinaryRational.Fraction) : ℕ :=
  SourceRowAcceptanceProgram.instructions (rows x y)+4+RationalComparisonProgram.instructions x y

def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 221) : NaturalState 221 :=
  ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩

theorem read_slots (pc : Fin 60) (h : SourceRowAcceptanceProgram.program pc≠.halt) :
    program (readLabel pc)=ReferenceProgramLabels.instruction readLabel (SourceRowAcceptanceProgram.program pc) := by
  by_cases hp : pc.val=58
  · have he : pc=58 := Fin.ext hp
    subst pc;simp [SourceRowAcceptanceProgram.program] at h
  · simp [program,readLabel,show ¬pc.val+158<158 by omega,show ¬pc.val+158=216 by omega,
      show ¬pc.val+158=218 by omega,show ¬pc.val+158=219 by omega,
      show ¬pc.val+158=220 by omega,show pc.val+158<218 by omega]

theorem cmp_slots (pc : Fin 158) :
    program (cmpLabel pc)=ReferenceProgramLabels.instruction cmpLabel (RationalComparisonProgram.program pc) := by
  simp [program,cmpLabel,pc.isLt]

theorem run_append {s u v : NaturalState 221} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem rows_accepted (x y : BinaryRational.Fraction) :
    RowTableValidationProgram.reject (rows x y)=false := by
  apply (RowTableValidationProgram.accepted_iff _).mpr
  simp [rows,x.den_pos,y.den_pos]

/-- The input parser constructs the actual two records, validates both stored
denominators, and passes their actual field roots into the arithmetic caller. -/
theorem run_high (x y : BinaryRational.Fraction) (suffix : Bits) :
    ∃ final a b, NaturalRun program (instructions x y)
        (eraseState (initial (SourceRowTableProgram.encode (rows x y)++suffix)))
        ((SourceRowTableProgram.encode (rows x y)).map Event.request) final ∧
      final.heap[final.registers.d]?=some (.flag (BinaryRational.le x y).1) ∧
      RationalComparisonProgram.Stored final.heap a x ∧ RationalComparisonProgram.Stored final.heap b y ∧
      final.source=suffix ∧ final.stack=[] ∧ final.pc=157 ∧
      final.heap.length=SourceRowTableProgram.cells (rows x y)+
        (RowTableValidationProgram.flags (rows x y)).length+RationalComparisonProgram.cells x y ∧
      final.next=final.heap.length ∧ tickNatural program final=none := by
  obtain ⟨u,read,table,_,pc,src,frames,len,dense,_⟩ := SourceRowAcceptanceProgram.accept_high (rows x y) suffix
  have pc' : u.pc=58 := by simpa [rows_accepted] using pc
  change WordPairTableRead.Table u.heap u.registers.a [(x.num,x.den),(y.num,y.den)] at table
  cases table with
  | @cons _ xa tail1 xn xd _ _ _ ht hx hn hd tailRep =>
    cases tailRep with
    | @cons _ ya tail2 yn yd _ _ _ htt hy hyn hyd endRep =>
      let cmpInitial := RationalComparisonProgram.state u.heap u.next xa ya u.registers.a u.registers.d [] suffix 144
      have left : RationalComparisonProgram.Stored u.heap xa x := ⟨xn,xd,hx,hn,hd⟩
      have right : RationalComparisonProgram.Stored u.heap ya y := ⟨yn,yd,hy,hyn,hyd⟩
      obtain ⟨v,cmp,flag,lword,rword,source,stack,pcv,densev,ext,halt⟩ :=
        RationalComparisonProgram.run_high x y cmpInitial rfl dense left right rfl
      have liftedRead := ReferenceProgramLabels.run readLabel SourceRowAcceptanceProgram.program program read_slots read
      have liftedCmp := ReferenceProgramLabels.run cmpLabel RationalComparisonProgram.program program (fun pc _ => cmp_slots pc) cmp
      have shapedRead : NaturalRun program (SourceRowAcceptanceProgram.instructions (rows x y))
          (eraseState (initial (SourceRowTableProgram.encode (rows x y)++suffix)))
          ((SourceRowTableProgram.encode (rows x y)).map Event.request)
          (state u.heap u.next u.registers.a u.registers.b u.registers.c u.registers.d suffix 216) := by
        simpa [initial,ReferenceProgramLabels.state,ReferenceProgramLabels.frame,SourceRowAcceptanceProgram.initial,
          readLabel,eraseState,State.map,state,pc',src,frames] using liftedRead
      have t216 : tickNatural program
          (state u.heap u.next u.registers.a u.registers.b u.registers.c u.registers.d suffix 216)=
          some ⟨state u.heap u.next u.registers.a u.registers.b u.registers.a u.registers.d suffix 218,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t218 : tickNatural program
          (state u.heap u.next u.registers.a u.registers.b u.registers.a u.registers.d suffix 218)=
          some ⟨state u.heap u.next xa u.registers.b u.registers.a u.registers.d suffix 219,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,ht]
      have t219 : tickNatural program
          (state u.heap u.next xa u.registers.b u.registers.a u.registers.d suffix 219)=
          some ⟨state u.heap u.next xa tail1 u.registers.a u.registers.d suffix 220,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,ht]
      have t220 : tickNatural program
          (state u.heap u.next xa tail1 u.registers.a u.registers.d suffix 220)=
          some ⟨state u.heap u.next xa ya u.registers.a u.registers.d suffix 144,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,htt]
      let final := ReferenceProgramLabels.state cmpLabel v
      have cmp' : NaturalRun program (RationalComparisonProgram.instructions x y)
          (state u.heap u.next xa ya u.registers.a u.registers.d suffix 144) [] final := by
        simpa [cmpInitial,RationalComparisonProgram.state,ReferenceProgramLabels.state,
          ReferenceProgramLabels.frame,cmpLabel,state,final] using liftedCmp
      refine ⟨final,xa,ya,?_,flag,lword,rword,source,?_,?_,?_,densev,?_⟩
      · have all := run_append shapedRead (.step t216 (.step t218 (.step t219 (.step t220 cmp'))))
        convert all using 1 <;> simp [instructions,Nat.add_assoc];omega
      · simp [final,ReferenceProgramLabels.state,stack]
      · simp [final,ReferenceProgramLabels.state,pcv,cmpLabel]
      · obtain ⟨ext,he,le⟩ := ext
        change v.heap.length=_
        rw [he,List.length_append,le]
        change u.heap.length+RationalComparisonProgram.cells x y=_
        rw [len]
      · simp [tickNatural,program,final,ReferenceProgramLabels.state,pcv,cmpLabel,
          RationalComparisonProgram.program,ReferenceProgramLabels.instruction]

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

theorem instructions_bound (x y : BinaryRational.Fraction) :
    instructions x y ≤ 512*(RationalComparisonProgram.inputSize x y)^2 := by
  have h := RationalComparisonProgram.instructions_bound x y
  have hs := SourceRowAcceptanceProgram.instructions_bound (rows x y)
  have hz : 1 ≤ RationalComparisonProgram.inputSize x y := by
    simp only [RationalComparisonProgram.inputSize];omega
  simp only [rows,SourceRowTableProgram.bits,List.length_cons,List.length_nil] at hs
  dsimp [instructions,rows,RationalComparisonProgram.inputSize] at *
  nlinarith

/-- Actual source reads, complete denominator checks and cross-products all
occur in one lower run from an empty heap. The result is the existing exact
rational comparison, with both original padded records still present. -/
theorem compare_from_source (x y : BinaryRational.Fraction) (suffix : Bits) :
    ∃ charge out a b, Run program (instructions x y) charge
        (initial (SourceRowTableProgram.encode (rows x y)++suffix))
        ((SourceRowTableProgram.encode (rows x y)).map Event.request) out ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag (BinaryRational.le x y).1) ∧
      RationalComparisonProgram.Stored (eraseState out).heap a x ∧
      RationalComparisonProgram.Stored (eraseState out).heap b y ∧
      out.source=suffix ∧ out.stack=[] ∧ out.pc=157 ∧
      out.heap.length=SourceRowTableProgram.cells (rows x y)+
        (RowTableValidationProgram.flags (rows x y)).length+RationalComparisonProgram.cells x y ∧
      value out.next=out.heap.length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 221 1 0 (instructions x y) := by
  obtain ⟨final,a,b,high,flag,lword,rword,src,frames,pc,len,dense,halt⟩ := run_high x y suffix
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation (initial_bounded _) high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,a,b,run,?_,?_,?_,source.trans src,?_,?_,?_,?_,stop,
    (terminal_accounting run (initial_bounded _) stop).2⟩
  · rw [erase];exact flag
  · rw [erase];exact lword
  · rw [erase];exact rword
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · exact (congrArg State.pc erase).trans pc
  · simpa only [eraseState,State.map,List.length_map] using
      (congrArg (fun s : NaturalState 221 => s.heap.length) erase).trans len
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];exact dense
    simpa [eraseState,State.map] using h

/-- A stored-length bound for the complete accepted-input execution, including
source acquisition, address arithmetic, all calls and the final halt. -/
theorem total_bound (x y : BinaryRational.Fraction) :
    completeBound 221 1 0 (instructions x y) ≤
      1000000000000*(RationalComparisonProgram.inputSize x y)^6 := by
  let z := RationalComparisonProgram.inputSize x y
  have hz : 1 ≤ z := by dsimp [z,RationalComparisonProgram.inputSize];omega
  have hz2 : 1 ≤ z^2 := by nlinarith
  have ht : instructions x y ≤ 512*z^2 := instructions_bound x y
  have hs : 2*instructions x y+2 ≤ 1026*z^2 := by omega
  have hr : instructions x y+2 ≤ 514*z^2 := by omega
  have hb : instructions x y+1 ≤ 513*z^2 := by omega
  unfold completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 470*(512*z^2)*(1026*z^2)^2+470*(514*z^2)*(513*z^2) := by gcongr <;> omega
    _ ≤ 1000000000000*z^6 := by
      have hz46 : z^4 ≤ z^6 := Nat.pow_le_pow_right hz (by omega)
      nlinarith

/-- Invalid denominators take the actual rejection halt before any arithmetic.
This branch requires no positive-denominator certificate or represented heap. -/
theorem reject_from_source (inputRows : List (Bits × Bits)) (suffix : Bits)
    (bad : RowTableValidationProgram.reject inputRows=true) :
    ∃ charge out, Run program (SourceRowAcceptanceProgram.instructions inputRows) charge
        (initial (SourceRowTableProgram.encode inputRows++suffix))
        ((SourceRowTableProgram.encode inputRows).map Event.request) out ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState out).registers.a inputRows ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag true) ∧
      out.source=suffix ∧ out.stack=[] ∧ out.pc=217 ∧
      out.heap.length=SourceRowTableProgram.cells inputRows+(RowTableValidationProgram.flags inputRows).length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤
        completeBound 221 1 0 (SourceRowAcceptanceProgram.instructions inputRows) := by
  obtain ⟨u,high,table,flag,pc,src,frames,len,_,_⟩ := SourceRowAcceptanceProgram.accept_high inputRows suffix
  have pc' : u.pc=59 := by simpa [bad] using pc
  let final := ReferenceProgramLabels.state readLabel u
  have lifted := ReferenceProgramLabels.run readLabel SourceRowAcceptanceProgram.program program read_slots high
  have high' : NaturalRun program (SourceRowAcceptanceProgram.instructions inputRows)
      (eraseState (initial (SourceRowTableProgram.encode inputRows++suffix)))
      ((SourceRowTableProgram.encode inputRows).map Event.request) final := by
    simpa [initial,SourceRowAcceptanceProgram.initial,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,readLabel,eraseState,State.map,final] using lifted
  have halt : tickNatural program final=none := by
    simp [tickNatural,program,final,ReferenceProgramLabels.state,pc',readLabel,
      SourceRowAcceptanceProgram.program,ReferenceProgramLabels.instruction]
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation (initial_bounded _) high'
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,source.trans src,?_,?_,?_,stop,
    (terminal_accounting run (initial_bounded _) stop).2⟩
  · rw [erase];exact table
  · rw [erase];simpa only [final,ReferenceProgramLabels.state,bad] using flag
  · have h : (eraseState out).stack=[] := by rw [erase];simp [final,ReferenceProgramLabels.state,frames]
    simpa [eraseState,State.map] using h
  · have h := congrArg State.pc erase
    simpa [final,ReferenceProgramLabels.state,pc',readLabel] using h
  · simpa only [eraseState,State.map,List.length_map] using
      (congrArg (fun s : NaturalState 221 => s.heap.length) erase).trans len

end DirectedFlowCutGap.InputRationalComparisonProgram
