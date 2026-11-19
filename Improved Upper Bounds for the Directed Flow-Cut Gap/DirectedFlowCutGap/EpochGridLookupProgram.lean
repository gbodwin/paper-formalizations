import DirectedFlowCutGap.EpochGridTableProgram
import DirectedFlowCutGap.EpochPairEqualityProgram
import DirectedFlowCutGap.PhysicalEpochInputProgram

/-! Read the cell assigned to a demand by comparing both original labels. -/

namespace DirectedFlowCutGap.EpochGridLookupProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open GraphWalkExtension (Edge EdgeList edge_extend)
open BinaryPointerListRead (PointerList)
open RetainedGridState
open EpochActiveFromMaskProgram (labelPair Payloads)

def Entry {n : ℕ} (heap : NaturalHeap) (root : ℕ) (p : Pair n) (word : Bits) : Prop :=
  ∃ key,EpochGridTableProgram.Entry heap root key word ∧ Edge heap key (labelPair p)

inductive Table {n : ℕ} (heap : NaturalHeap) : ℕ→List (Pair n×Bits)→Prop
  | nil {root} : heap[root]?=some .nil → Table heap root []
  | cons {root head tail p word rest} : heap[root]?=some (.pair head tail) →
      Entry heap head p word → Table heap tail rest → Table heap root ((p,word)::rest)

theorem table_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {rows : List (Pair n×Bits)}
    (stored : Table heap root rows) (ext : NaturalHeap) : Table (heap++ext) root rows := by
  induction stored with
  | nil read => exact .nil (lookup_extend read ext)
  | cons read entry _ ih =>
    obtain ⟨ptr,rep,edge⟩ := entry
    exact .cons (lookup_extend read ext) ⟨ptr,EpochGridTableProgram.entry_extend rep ext,edge_extend edge ext⟩ ih

theorem table_zip {n : ℕ} {heap : NaturalHeap} {root : ℕ} {refs : List ℕ} {labels : List (Pair n)}
    {words : List Bits} (payloads : Payloads heap refs labels)
    (stored : EpochGridTableProgram.Table heap root (refs.zip words)) : Table heap root (labels.zip words) := by
  induction payloads generalizing words root with
  | nil =>
    cases stored with
    | nil h => exact .nil h
  | cons rep _ ih =>
    cases words with
    | nil =>
      cases stored with
      | nil h => exact .nil h
    | cons w ws =>
      cases stored with
      | cons pair word tail => exact .cons pair ⟨_,word,rep⟩ (ih tail)

def word {n : ℕ} (p : Pair n) : List (Pair n×Bits)→Bits
  | [] => []
  | (q,bits)::rest => if p=q then bits else word p rest

private theorem word_at {n i : ℕ} (labels : List (Pair n)) (words : List Bits)
    (unique : labels.Nodup) (hi : i<labels.length) (hw : i<words.length) :
    word labels[i] (labels.zip words)=words[i] := by
  induction labels generalizing words i with
  | nil => simp at hi
  | cons q qs ih =>
    cases words with
    | nil => simp at hw
    | cons w ws =>
      cases i with
      | zero => simp [word]
      | succ i =>
        have iq : i<qs.length := by simpa using hi
        have iw : i<ws.length := by simpa using hw
        have ne : qs[i]≠q := by
          intro eq
          exact (List.nodup_cons.mp unique).1 (eq ▸ List.getElem_mem iq)
        simpa only [List.zip_cons_cons,List.getElem_cons_succ,word,ite_eq_right ne] using
          ih ws (List.nodup_cons.mp unique).2 iq iw

private theorem word_absent {n : ℕ} (p : Pair n) (labels : List (Pair n)) (words : List Bits)
    (absent : p∉labels) : word p (labels.zip words)=[] := by
  induction labels generalizing words with
  | nil => rfl
  | cons q qs ih =>
    cases words with
    | nil => rfl
    | cons w ws =>
      have ne : p≠q := fun eq => absent (List.mem_cons.mpr (Or.inl eq))
      have gone : p∉qs := fun mem => absent (List.mem_cons_of_mem _ mem)
      simpa only [List.zip_cons_cons,word,ite_eq_right ne] using ih ws gone

/-- The actual table order assigns each sampled word to its original pair label. -/
theorem word_value {n L : ℕ} (a : PairFlags n) (positive : 0<L) (t : RetainedTapeInput.Tape L a)
    (words : List Bits) (samples : words.map value=PhysicalEpochDraws.cellValues L (Fintype.card ↥(remainingSet a)) t.2)
    (p : Pair n) :
    value (word p ((RetainedTapeInput.activeList a).zip words))=((RetainedTapeInput.materialize positive a t).cell p).val := by
  by_cases active : p∈remainingSet a
  · let i := (RetainedTapeInput.activeEnum a).symm ⟨p,active⟩
    have index : i.val<(RetainedTapeInput.activeList a).length := by
      rw [RetainedTapeInput.activeList_length]
      exact i.isLt
    have cellIndex : i.val<(PhysicalEpochDraws.cellValues L (Fintype.card ↥(remainingSet a)) t.2).length := by
      rw [PhysicalEpochInputData.cell_values_length]
      exact i.isLt
    have len := congrArg List.length samples
    rw [List.length_map] at len
    have within : i.val<words.length := len.symm ▸ cellIndex
    have label : (RetainedTapeInput.activeList a)[i.val]=p := by
      rw [← PhysicalEpochInputData.active_at a i]
      exact congrArg Subtype.val (Equiv.apply_symm_apply (RetainedTapeInput.activeEnum a) ⟨p,active⟩)
    have read : (words.map value)[i.val]?=some (value words[i.val]) := by
      simp [List.getElem?_eq_getElem within]
    rw [samples,List.getElem?_eq_getElem cellIndex] at read
    have stored := word_at (RetainedTapeInput.activeList a) words (RetainedTapeInput.activeList_nodup a) index within
    rw [label] at stored
    rw [stored,← Option.some.inj read]
    have exactCell := PhysicalEpochInputData.materialized_cells a positive t i
    rw [PhysicalEpochInputData.active_at a i,label] at exactCell
    exact exactCell
  · rw [word_absent p _ _ (fun mem => active ((RetainedTapeInput.mem_activeList a p).mp mem))]
    have missing : flag a p≠true := fun h => active ((mem_remainingSet a p).mpr h)
    simp [RetainedTapeInput.materialize,IntegerAdaptiveExecution.Input.cell,missing,value]

private theorem edges_of_payloads {n : ℕ} {heap : NaturalHeap} {root : ℕ} {refs : List ℕ}
    {pairs : List (Pair n)} (payloads : Payloads heap refs pairs) (spine : PointerList heap root refs) :
    EdgeList heap root (pairs.map labelPair) := by
  induction payloads generalizing root with
  | nil =>
    cases spine with
    | nil read => exact .nil read
  | cons edge _ ih =>
    cases spine with
    | cons read rest => exact .cons read edge (ih rest)

/-- Open the actual output of the fair-tape epoch preparation without rebuilding it. -/
theorem stored_epoch {n L : ℕ} {heap : NaturalHeap} {root : ℕ} {a : PairFlags n} {positive : 0<L}
    {t : RetainedTapeInput.Tape L a} {grid : List PhysicalBoundedDrawProgram.Outcome}
    (h : PhysicalEpochInputProgram.Output heap root a positive t grid) :
    let input := RetainedTapeInput.materialize positive a t
    let rows := (RetainedTapeInput.activeList a).zip (grid.map PhysicalBoundedDrawProgram.Outcome.index)
    ∃ perm cells,heap[root]?=some (.pair perm cells) ∧ EdgeList heap perm (input.order.map labelPair) ∧
      Table heap cells rows ∧ ∀ p,value (word p rows)=(input.cell p).val := by
  obtain ⟨original,order,labels,permuted,⟨perm,cells,atRoot,spine,stored⟩,values⟩ := h
  exact ⟨perm,cells,atRoot,edges_of_payloads permuted spine,table_zip labels stored,
    word_value a positive t _ (by simpa only [List.map_map,EpochPermutationProgram.indices,Function.comp_def] using values)⟩

def eqLabel (pc : Fin 72) : Fin 104 := ⟨32+pc.val,by omega⟩

def program : Program 104 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .branch .r1 9 31 31 10
    | 9 => .make .r3 .nil 14
    | 10 => .call 24 11 .r3
    | 11 => .branch .r3 31 12 20 31
    | 12 => .field .r1 .r1 true 8
    | 14 => .ret .r3
    | 20 => .field .r3 .r1 false 21
    | 21 => .field .r3 .r3 true 14
    | 24 => .field .r1 .r1 false 25
    | 25 => .field .r1 .r1 false (eqLabel 0)
    | _ => .halt
  else if pc.val=39 then .ret .r3
  else ReferenceProgramLabels.instruction eqLabel
    (EpochPairEqualityProgram.program ⟨pc.val-32,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 104))
    (tape : Bits) (pc : Fin 104) : NaturalState 104 := ⟨heap,heap.length,r,stack,pc,tape⟩

def bodySteps {n : ℕ} (p : Pair n) : List (Pair n×Bits)→ℕ
  | [] => 3
  | (q,_)::rest => EpochPairEqualityProgram.steps (labelPair p) (labelPair q)+
      if p=q then 9 else bodySteps p rest+7

def steps {n : ℕ} (p : Pair n) (rows : List (Pair n×Bits)) : ℕ := bodySteps p rows+1

def instructionBound (n rows : ℕ) : ℕ := rows*(64*n.size+54)+4

theorem steps_le {n : ℕ} (p : Pair n) (rows : List (Pair n×Bits)) :
    steps p rows ≤ instructionBound n rows.length := by
  have width (v : Fin n) : v.val.bits.length≤n.size := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size v.isLt.le
  have bound : bodySteps p rows ≤ rows.length*(64*n.size+54)+3 := by
    induction rows with
    | nil => simp [bodySteps]
    | cons row rest ih =>
      rcases row with ⟨q,w⟩
      have k := EpochPairEqualityProgram.steps_le (labelPair p) (labelPair q) n.size
        (width p.1) (width p.2) (width q.1) (width q.2)
      rw [bodySteps,List.length_cons,Nat.succ_mul]
      split <;> omega
  exact Nat.add_le_add_right bound 1

private theorem slots (pc : Fin 72) (h : EpochPairEqualityProgram.program pc≠.halt) :
    program (eqLabel pc)=ReferenceProgramLabels.instruction eqLabel (EpochPairEqualityProgram.program pc) := by
  by_cases hp : pc.val=7
  · have eq : pc=7 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,eqLabel,show ¬32+pc.val<32 by omega,show 32+pc.val≠39 by omega]

private theorem compare_call {n : ℕ} {p q : Pair n} {heap : NaturalHeap} {r : Registers ℕ}
    {entry next key valueRoot : ℕ}
    (wanted : Edge heap r.a (labelPair p)) (other : Edge heap key (labelPair q))
    (cell : heap[r.b]?=some (.pair entry next)) (pair : heap[entry]?=some (.pair key valueRoot))
    (stack : List (Frame ℕ 104)) (tape : Bits) :
    ∃ ext root,(heap++ext)[root]?=some (.flag (decide (p=q))) ∧
      NaturalRun program (EpochPairEqualityProgram.steps (labelPair p) (labelPair q)+4)
        (state heap r stack tape 10) [] (state (heap++ext) (r.set .r3 root) stack tape 11) := by
  let args := r.set .r1 key
  let frame : Frame ℕ 104 := ⟨11,.r3,r⟩
  have setup : NaturalRun program 3 (state heap r stack tape 10) [] (state heap args (frame::stack) tape (eqLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,frame,cell,pair]
  obtain ⟨ext,root,rep,body⟩ := EpochPairEqualityProgram.natural_equality (r:=args) wanted other tape
  let stop := state (heap++ext) (args.set .r3 root) (frame::stack) tape (eqLabel 7)
  have lifted := ReferenceProgramLabels.run eqLabel EpochPairEqualityProgram.program program slots body
  have lifted := ReferenceProgramStack.run program (frame::stack) lifted
  let work := EpochPairEqualityProgram.steps (labelPair p) (labelPair q)
  have run : NaturalRun program work (state heap args (frame::stack) tape (eqLabel 0)) [] stop := by
    simpa [state,stop,work,EpochPairEqualityProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) stack tape 11,[],0⟩ := by
    simp [state,stop,program,eqLabel,tickNatural,frame,Registers.get,Registers.set]
  rw [EpochPairEqualityProgram.result_label] at rep
  refine ⟨ext,root,rep,?_⟩
  have count : 3+(work+1)=work+4 := by omega
  change NaturalRun program (work+4) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

set_option maxHeartbeats 1600000 in
private theorem lookup_return {n : ℕ} {p : Pair n} {heap : NaturalHeap} {r : Registers ℕ}
    {rows : List (Pair n×Bits)} (key : Edge heap r.a (labelPair p)) (table : Table heap r.b rows)
    (caller : Frame ℕ 104) (stack : List (Frame ℕ 104)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (word p rows) ∧
      NaturalRun program (bodySteps p rows) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction rows generalizing heap r caller stack with
  | nil =>
    cases table with
    | nil empty =>
      refine ⟨[.nil],heap.length,.nil (by simp),?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,empty,
        allocateNatural,Recipe.cell,bodySteps]
  | cons head rest ih =>
    rcases head with ⟨q,bits⟩
    cases table with
    | @cons _ entry tail _ _ _ read packed remain =>
      obtain ⟨other,⟨ptr,pair,cell⟩,occurrence⟩ := packed
      let saved := caller::stack
      have event : tickNatural program (state heap r saved tape 8)=some ⟨state heap r saved tape 10,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,read]
      obtain ⟨ec,test,answer,compare⟩ := compare_call key occurrence read pair saved tape
      let mid := heap++ec
      let ready := r.set .r3 test
      have row : mid[r.b]?=some (.pair entry tail) := lookup_extend read ec
      have info : mid[entry]?=some (.pair other ptr) := lookup_extend pair ec
      have flag : mid[test]?=some (.flag (decide (p=q))) := answer
      let k := EpochPairEqualityProgram.steps (labelPair p) (labelPair q)
      by_cases same : p=q
      · have found : NaturalRun program 4 (state mid ready saved tape 11) []
          (state mid (caller.saved.set caller.destination ptr) stack tape caller.continuation) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,ready,
              flag,row,info,same,saved]
        refine ⟨ec,ptr,by simpa only [word,ite_eq_left same] using boolList_extend cell ec,?_⟩
        simp only [bodySteps,ite_eq_left same]
        change NaturalRun program (k+9) _ [] _
        have count : k+4+4+1=k+9 := by omega
        rw [← count]
        exact .step event (append_run compare found)
      · let args := ready.set .r1 tail
        have advance : NaturalRun program 2 (state mid ready saved tape 11) [] (state mid args saved tape 8) := by
          apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,ready,
            flag,row,same,args]
        obtain ⟨er,root,rep,body⟩ := ih (r:=args) (edge_extend key ec) (table_extend remain ec) caller stack
        refine ⟨ec++er,root,?_,?_⟩
        · simpa only [mid,word,ite_eq_right same,List.append_assoc] using rep
        · simp only [bodySteps,ite_eq_right same]
          have count : k+4+(2+bodySteps p rest)+1=k+(bodySteps p rest+7) := by omega
          change NaturalRun program (k+(bodySteps p rest+7)) _ [] _
          rw [← count]
          simpa only [k,mid,List.append_assoc,List.nil_append] using
            NaturalRun.step event (append_run compare (append_run advance body))

theorem natural_lookup {n : ℕ} {p : Pair n} {heap : NaturalHeap} {r : Registers ℕ}
    {rows : List (Pair n×Bits)} (key : Edge heap r.a (labelPair p)) (table : Table heap r.b rows) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (word p rows) ∧
      NaturalRun program (steps p rows) (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let frame : Frame ℕ 104 := ⟨1,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,rep,body⟩ := lookup_return key table frame [] tape
  exact ⟨ext,root,rep,.step enter body⟩

private theorem at_entry (s : NaturalState 104) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_lookup {n H A : ℕ} (p : Pair n) (rows : List (Pair n×Bits)) (initial : BitState 104)
    (bound : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (key : Edge (eraseState initial).heap (eraseState initial).registers.a (labelPair p))
    (table : Table (eraseState initial).heap (eraseState initial).registers.b rows) :
    ∃ paid out,Run program (steps p rows) paid initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (word p rows) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ out.pc=1 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧ (attempt program out).result=none ∧
      paid+(attempt program out).operations ≤ completeBound 104 H A (instructionBound n rows.length) := by
  let old := eraseState initial
  obtain ⟨ext,root,rep,run⟩ := natural_lookup key table initial.source
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] initial.source 1
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have entry : old=state old.heap old.registers [] initial.source 0 := at_entry old hp empty hn
  have trace : NaturalRun program (steps p rows) old [] final := by rw [entry]; exact run
  have halt : tickNatural program final=none := rfl
  obtain ⟨paid,out,worked,exactState,stopped,cost,tape⟩ := terminating_simulation bound trace halt
  refine ⟨paid,out,worked,?_,tape,?_,?_,⟨ext,?_⟩,stopped,cost.trans ?_⟩
  · rw [exactState]; exact rep
  · rw [exactState]; rfl
  · exact congrArg (fun s : NaturalState 104 => s.pc) exactState
  · rw [exactState]; rfl
  · exact SupportSearchEncoding.complete_mono _ _ _ _ _ (steps_le p rows)

end DirectedFlowCutGap.EpochGridLookupProgram
