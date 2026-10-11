import DirectedFlowCutGap.RowTableValidationProgram

/-! Actual source construction followed by complete denominator validation.
The source table is built once, retained through every zero test, and the real
terminal branch distinguishes acceptance from rejection. Valid row framing is
explicit; no index or denominator-positivity certificate is supplied. -/
namespace DirectedFlowCutGap.SourceRowAcceptanceProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def scanLabel (pc : Fin 26) : Fin 60 := ⟨pc.val,by omega⟩
def rowLabel (pc : Fin 32) : Fin 60 := ⟨pc.val+26,by omega⟩
def program : Program 60 := fun pc =>
  if pc.val=57 then .move .r0 .r3 14
  else if pc.val=15 then .branch .r3 59 58 59 59
  else if h : pc.val < 26 then
    ReferenceProgramLabels.instruction scanLabel (RowTableValidationProgram.program ⟨pc.val,h⟩)
  else if h : pc.val < 58 then
    ReferenceProgramLabels.instruction rowLabel (SourceRowTableProgram.program ⟨pc.val-26,by omega⟩)
  else .halt

def initial (source : Bits) : BitState 60 := ⟨[],[],⟨[],[],[],[]⟩,[],56,source⟩
def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 60) : NaturalState 60 :=
  ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩
def instructions (rows : List (Bits × Bits)) : ℕ :=
  SourceRowTableProgram.steps rows+RowTableValidationProgram.steps rows+4

theorem row_slots (pc : Fin 32) (h : SourceRowTableProgram.program pc ≠ .halt) :
    program (rowLabel pc)=ReferenceProgramLabels.instruction rowLabel (SourceRowTableProgram.program pc) := by
  have hn : pc.val ≠ 31 := by
    intro he
    have eq : pc=31 := Fin.ext he
    subst pc
    exact h rfl
  simp [program,rowLabel,show pc.val+26 ≠ 57 by omega,show pc.val+26 ≠ 15 by omega,
    show ¬pc.val+26<26 by omega,show pc.val+26<58 by omega]

theorem scan_slots (pc : Fin 26) (h : RowTableValidationProgram.program pc ≠ .halt) :
    program (scanLabel pc)=ReferenceProgramLabels.instruction scanLabel (RowTableValidationProgram.program pc) := by
  have hn : pc.val ≠ 15 := by
    intro he
    have eq : pc=15 := Fin.ext he
    subst pc
    exact h rfl
  simp [program,scanLabel,hn,pc.isLt,show pc.val ≠ 57 by omega]

theorem run_append {s u v : NaturalState 60} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- Every input marker/data request, zero-test call and actual decision branch
belongs to this one run from an empty heap and stack. Rejection preserves the
same full table too; it never silently drops or repairs an invalid row. -/
theorem accept_high (rows : List (Bits × Bits)) (suffix : Bits) :
    ∃ final, NaturalRun program (instructions rows)
        (eraseState (initial (SourceRowTableProgram.encode rows++suffix)))
        ((SourceRowTableProgram.encode rows).map Event.request) final ∧
      WordPairTableRead.Table final.heap final.registers.a rows ∧
      final.heap[final.registers.d]?=some (.flag (RowTableValidationProgram.reject rows)) ∧
      final.pc=(if RowTableValidationProgram.reject rows then 59 else 58) ∧
      final.source=suffix ∧ final.stack=[] ∧
      final.heap.length=SourceRowTableProgram.cells rows+(RowTableValidationProgram.flags rows).length ∧
      final.next=final.heap.length ∧ tickNatural program final=none := by
  obtain ⟨ext,root,len,body,table⟩ := SourceRowTableProgram.read_return rows suffix [] 0 0 0 0 0 rfl ⟨0,0,0,0⟩ 31 []
  have start : tickNatural SourceRowTableProgram.program
      (eraseState (SourceRowTableProgram.initial (SourceRowTableProgram.encode rows++suffix)))=
      some ⟨SourceRowTableProgram.state [] 0 0 0 0 0 [⟨31,.r3,⟨0,0,0,0⟩⟩]
        (SourceRowTableProgram.encode rows++suffix) 0,[],0⟩ := by
    simp [tickNatural,SourceRowTableProgram.program,SourceRowTableProgram.initial,eraseState,State.map,
      SourceRowTableProgram.state,value,Registers.map]
  have readRun : NaturalRun SourceRowTableProgram.program (SourceRowTableProgram.steps rows+1)
      (eraseState (SourceRowTableProgram.initial (SourceRowTableProgram.encode rows++suffix)))
      ((SourceRowTableProgram.encode rows).map Event.request)
      (SourceRowTableProgram.state ext (SourceRowTableProgram.cells rows) 0 0 0 root [] suffix 31) := by
    simpa [SourceRowTableProgram.state,Nat.add_assoc] using NaturalRun.step start body
  let s := RowTableValidationProgram.state ext (SourceRowTableProgram.cells rows) root 0 0 root [] suffix 14
  have rep : WordPairTableRead.Table ext root rows := by simpa using table
  obtain ⟨u,scanRun,heap,dense,a,tab,flag,frames,src,pc,halt⟩ :=
    RowTableValidationProgram.validate_high s rfl (by simp [s,RowTableValidationProgram.state,len]) rep rfl
  let mapped := ReferenceProgramLabels.state scanLabel u
  let final : NaturalState 60 := {mapped with pc := if RowTableValidationProgram.reject rows then 59 else 58}
  have first : NaturalRun program (SourceRowTableProgram.steps rows+1)
      (eraseState (initial (SourceRowTableProgram.encode rows++suffix)))
      ((SourceRowTableProgram.encode rows).map Event.request)
      (state ext (SourceRowTableProgram.cells rows) 0 0 0 root suffix 57) := by
    have h := ReferenceProgramLabels.run rowLabel SourceRowTableProgram.program program row_slots readRun
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,rowLabel,SourceRowTableProgram.initial,
      SourceRowTableProgram.state,initial,eraseState,State.map,state] using h
  have t57 : tickNatural program (state ext (SourceRowTableProgram.cells rows) 0 0 0 root suffix 57)=
      some ⟨ReferenceProgramLabels.state scanLabel s,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ReferenceProgramLabels.state,
      scanLabel,s,RowTableValidationProgram.state]
  have decision : tickNatural program mapped=some ⟨final,[],0⟩ := by
    simp [tickNatural,program,mapped,ReferenceProgramLabels.state,scanLabel,pc,flag,Registers.get,
      final,tagBranch]
    cases RowTableValidationProgram.reject rows <;> rfl
  have scanRun' := ReferenceProgramLabels.run scanLabel RowTableValidationProgram.program program scan_slots scanRun
  refine ⟨final,?_,tab,flag,rfl,src,?_,?_,dense,?_⟩
  · have full := run_append first (.step t57 (run_append scanRun' (.step decision (.done _))))
    convert full using 1 <;> simp [instructions,Nat.add_assoc,List.append_nil]
    omega
  · simp [final,mapped,ReferenceProgramLabels.state,frames]
  · change u.heap.length=_
    rw [heap]
    simp [s,RowTableValidationProgram.state,len]
  · cases hz : RowTableValidationProgram.reject rows <;> simp [tickNatural,program,final,hz]

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

/-- The lower interpreter reaches the accepting instruction exactly for rows
with positive denominators. Its complete operation charge includes the single
halt reached on the same acceptance or rejection execution. -/
theorem accept_from_source (rows : List (Bits × Bits)) (suffix : Bits) :
    ∃ charge out, Run program (instructions rows) charge
        (initial (SourceRowTableProgram.encode rows++suffix))
        ((SourceRowTableProgram.encode rows).map Event.request) out ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState out).registers.a rows ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag (RowTableValidationProgram.reject rows)) ∧
      (out.pc=58 ↔ ∀ p ∈ rows, 0 < value p.2) ∧
      out.pc=(if RowTableValidationProgram.reject rows then 59 else 58) ∧
      out.source=suffix ∧ out.stack=[] ∧
      out.heap.length=SourceRowTableProgram.cells rows+(RowTableValidationProgram.flags rows).length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 60 1 0 (instructions rows) := by
  obtain ⟨final,high,table,flag,pc,src,frames,len,_,halt⟩ := accept_high rows suffix
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation (initial_bounded _) high
  have opc : out.pc=(if RowTableValidationProgram.reject rows then 59 else 58) :=
    (congrArg State.pc erase).trans pc
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,?_,opc,source.trans src,?_,?_,stop,
    (terminal_accounting run (initial_bounded _) stop).2⟩
  · rw [erase];exact table
  · rw [erase];exact flag
  · rw [opc,← RowTableValidationProgram.accepted_iff]
    cases RowTableValidationProgram.reject rows <;> decide
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).heap.length=SourceRowTableProgram.cells rows+(RowTableValidationProgram.flags rows).length := by rw [erase];exact len
    simpa [eraseState,State.map] using h

theorem instructions_bound (rows : List (Bits × Bits)) :
    instructions rows ≤ 33*(SourceRowTableProgram.bits rows+rows.length+1) := by
  have h := RowTableValidationProgram.steps_bound rows
  dsimp [instructions,SourceRowTableProgram.steps]
  omega

theorem total_bound (rows : List (Bits × Bits)) :
    completeBound 60 1 0 (instructions rows) ≤
      40000000*(SourceRowTableProgram.bits rows+rows.length+1)^3 := by
  let z := SourceRowTableProgram.bits rows+rows.length+1
  have hz : 1 ≤ z := by dsimp [z];omega
  have ht : instructions rows ≤ 33*z := instructions_bound rows
  have hs : 2*instructions rows+2 ≤ 68*z := by omega
  have hr : instructions rows+2 ≤ 35*z := by omega
  unfold completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 204*(33*z)*(68*z)^2+204*(35*z)*(35*z) := by gcongr <;> omega
    _ ≤ 40000000*z^3 := by
      have hz2 : z^2 ≤ z^3 := by nlinarith
      nlinarith

end DirectedFlowCutGap.SourceRowAcceptanceProgram
