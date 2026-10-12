import DirectedFlowCutGap.CostedCandidateMaterialization
import DirectedFlowCutGap.RetainedGraphArgmin

/-! The actual candidate constructor feeds its newly allocated record list to
stable selection. The complete run retains original payloads and occurrence
addresses, and pays a single final halt. -/
namespace DirectedFlowCutGap.RetainedArgminProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem run_high_terminal (xs : List Item) (initial : NaturalState 194)
    (pc0 : initial.pc=178) (hn : initial.next=initial.heap.length)
    (input : ItemList initial.heap initial.registers.a xs) (empty : initial.stack=[]) :
    ∃ out, NaturalRun program (steps xs) initial [] out ∧
      Selected out.heap out.registers.d (select xs) ∧
      ItemList out.heap initial.registers.a xs ∧ out.source=initial.source ∧ out.stack=[] ∧
      out.next=out.heap.length ∧
      (∃ ext,out.heap=initial.heap++ext ∧ ext.length=cells xs) ∧
      program out.pc=.halt := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn input empty
      subst pc;subst stack
      cases xs with
      | nil =>
        cases input with
        | nil hnil =>
          have t178 : tickNatural program (state heap next a b c d [] source 178)=
              some ⟨state heap next a b c d [] source 174,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
          have t174 : tickNatural program (state heap next a b c d [] source 174)=
              some ⟨state (heap++[.nil]) (next+1) a b c next [] source 175,[],0⟩ := by
            simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
          refine ⟨state (heap++[.nil]) (next+1) a b c next [] source 175,
            .step t178 (.step t174 (.done _)),?_,?_,rfl,rfl,?_,⟨[.nil],rfl,rfl⟩,rfl⟩
          · simp [Selected,select,state,hn]
          · exact list_extend (.nil hnil) _
          · simp [state,hn]
      | cons x xs =>
        cases input with
        | @cons a item tail x xs hp hi ht =>
          have t178 : tickNatural program (state heap next a b c d [] source 178)=
              some ⟨state heap next a b c d [] source 179,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hp,tagBranch]
          have t179 : tickNatural program (state heap next a b c d [] source 179)=
              some ⟨state heap next a tail c d [] source 180,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hp]
          have t180 : tickNatural program (state heap next a tail c d [] source 180)=
              some ⟨state heap next item tail c d [] source 160,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hp]
          obtain ⟨ext,out,len,run,he,hnext,selected,src,frames,hpc,_⟩ := scan_high xs x hi ht next c d hn source
          refine ⟨out,?_,selected,?_,src,frames,?_,⟨ext,he,len⟩,by rw [hpc];rfl⟩
          · simpa [steps,state,Nat.add_assoc] using NaturalRun.step t178 (.step t179 (.step t180 run))
          · rw [he];exact list_extend (.cons hp hi ht) ext
          · rw [hnext,he];simp [hn]

end DirectedFlowCutGap.RetainedArgminProgram

namespace DirectedFlowCutGap.CostedCandidateSelection
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open CostedCandidateMaterialization

def materializeLabel (pc : Fin 307) : Fin 501 := ⟨pc.val,by omega⟩
def selectLabel (pc : Fin 194) : Fin 501 := ⟨pc.val+307,by omega⟩
def program : Program 501 := fun pc =>
  if pc.val=306 then .move .r0 .r3 485
  else if h : pc.val<307 then
    ReferenceProgramLabels.instruction materializeLabel (CostedCandidateMaterialization.program ⟨pc.val,h⟩)
  else ReferenceProgramLabels.instruction selectLabel
    (RetainedArgminProgram.program ⟨pc.val-307,by omega⟩)

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 501)) (source : Bits) (pc : Fin 501) : NaturalState 501 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def steps (rows : List Fraction) (next : ℕ) (xs : List Candidate) : ℕ :=
  CostedCandidateMaterialization.steps rows xs+2+RetainedArgminProgram.steps (items rows next xs)

def cells (rows : List Fraction) (next : ℕ) (xs : List Candidate) : ℕ :=
  CostedCandidateMaterialization.cells rows xs+RetainedArgminProgram.cells (items rows next xs)

theorem materialize_slots (pc : Fin 307) (h : CostedCandidateMaterialization.program pc≠.halt) :
    program (materializeLabel pc)=ReferenceProgramLabels.instruction materializeLabel
      (CostedCandidateMaterialization.program pc) := by
  by_cases hp : pc.val=306
  · have he : pc=306 := Fin.ext hp
    subst pc;simp [CostedCandidateMaterialization.program] at h
  · simp [program,materializeLabel,pc.isLt,hp]

theorem select_slots (pc : Fin 194) :
    program (selectLabel pc)=ReferenceProgramLabels.instruction selectLabel
      (RetainedArgminProgram.program pc) := by
  simp [program,selectLabel,show ¬pc.val+307=306 by omega,show ¬pc.val+307<307 by omega]

theorem run_append {s u v : NaturalState 501} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The score list is the literal output of the cost-materialization run. -/
theorem select_high {xs : List Candidate} {rows : List Fraction} (initial : NaturalState 501)
    (pc0 : initial.pc=305) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : CandidateList initial.heap initial.registers.a xs)
    (table : WordPairTableRead.Table initial.heap initial.registers.b (IndexedRationalRead.fields rows))
    (valid : ∀ x∈xs,∀ w∈x.words,value w<rows.length) :
    ∃ out, NaturalRun program (steps rows initial.next xs) initial [] out ∧
      RetainedArgminProgram.Selected out.heap out.registers.d
        (RetainedArgminProgram.select (items rows initial.next xs)) ∧
      CandidateList out.heap initial.registers.a xs ∧
      (∃ itemRoot,RetainedArgminProgram.ItemList out.heap itemRoot (items rows initial.next xs)) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.next=out.heap.length ∧
      (∃ ext,out.heap=initial.heap++ext ∧ ext.length=cells rows initial.next xs) ∧
      program out.pc=.halt := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input table
      subst pc;subst stack
      obtain ⟨em,rm,lm,mrun,mrep⟩ := materialize_high
        (CostedCandidateMaterialization.state heap next a b c d [] source 305) rfl hn rfl input table valid
      let h1 := heap++em
      let n1 := next+em.length
      have dense1 : n1=h1.length := by simp [n1,h1,hn]
      obtain ⟨u,srun,sel,retained,src,stk,dense,⟨es,he,ls⟩,halt⟩ :=
        RetainedArgminProgram.run_high_terminal (items rows next xs)
          (RetainedArgminProgram.state h1 n1 rm b c rm [] source 178) rfl dense1 mrep rfl
      have mlift := ReferenceProgramLabels.run materializeLabel CostedCandidateMaterialization.program
        program materialize_slots mrun
      have mbody : NaturalRun program (CostedCandidateMaterialization.steps rows xs+1)
          (state heap next a b c d [] source 305) [] (state h1 n1 a b c rm [] source 306) := by
        simpa [ReferenceProgramLabels.state,CostedCandidateMaterialization.state,materializeLabel,state] using mlift
      have slift := ReferenceProgramLabels.run selectLabel RetainedArgminProgram.program program
        (fun pc _ => select_slots pc) srun
      have sbody : NaturalRun program (RetainedArgminProgram.steps (items rows next xs))
          (state h1 n1 rm b c rm [] source 485) [] (ReferenceProgramLabels.state selectLabel u) := by
        simpa [ReferenceProgramLabels.state,RetainedArgminProgram.state,selectLabel,state] using slift
      have move : tickNatural program (state h1 n1 a b c rm [] source 306)=
          some ⟨state h1 n1 rm b c rm [] source 485,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      refine ⟨ReferenceProgramLabels.state selectLabel u,?_,sel,?_,⟨rm,retained⟩,src,?_,dense,?_,?_⟩
      · have all := run_append mbody (NaturalRun.step move sbody)
        have count : CostedCandidateMaterialization.steps rows xs+1+
            (RetainedArgminProgram.steps (items rows next xs)+1)=steps rows next xs := by
          unfold steps
          omega
        simpa only [count,List.nil_append,state] using all
      · change CandidateList u.heap a xs
        rw [he]
        exact CostedCandidateMaterialization.list_extend (CostedCandidateMaterialization.list_extend input em) es
      · simp [ReferenceProgramLabels.state,stk]
      · refine ⟨em++es,?_,?_⟩
        · simpa [ReferenceProgramLabels.state,h1,RetainedArgminProgram.state,List.append_assoc] using he
        · simp [cells,lm,ls]
      · change program (selectLabel u.pc)=.halt
        rw [select_slots,halt];rfl

/-- One same-run lower interpretation covers collection, actual arithmetic,
selection and the reached final halt. No costed-list input is assumed. -/
theorem select_bit {xs : List Candidate} {rows : List Fraction} {H A : ℕ} (initial : BitState 501)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=305)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : CandidateList (eraseState initial).heap (eraseState initial).registers.a xs)
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.b
      (IndexedRationalRead.fields rows)) (valid : ∀ x∈xs,∀ w∈x.words,value w<rows.length) :
    ∃ charge out, Run program (steps rows (value initial.next) xs) charge initial [] out ∧
      RetainedArgminProgram.Selected (eraseState out).heap (eraseState out).registers.d
        (RetainedArgminProgram.select (items rows (value initial.next) xs)) ∧
      CandidateList (eraseState out).heap (eraseState initial).registers.a xs ∧
      (∃ itemRoot,RetainedArgminProgram.ItemList (eraseState out).heap itemRoot (items rows (value initial.next) xs)) ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells rows (value initial.next) xs) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 501 H A (steps rows (value initial.next) xs) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,selected,retained,itemsRep,source,stack,_,ext,halt⟩ :=
    select_high (eraseState initial) pc0 hn' empty' input table valid
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have ht : tickNatural program final=none := by simp [tickNatural,halt]
    rw [ht] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,?_,src.trans source,?_,?_,stop,(terminal_accounting run bounded stop).2⟩
  · rw [erase];exact selected
  · rw [erase];exact retained
  · rw [erase];exact itemsRep
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · rw [erase];exact ext

end DirectedFlowCutGap.CostedCandidateSelection
