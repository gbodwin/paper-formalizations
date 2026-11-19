import DirectedFlowCutGap.EpochPrefixSelectionProgram

/-! Apply the actual permutation draws and retain the unconsumed grid draws. -/

namespace DirectedFlowCutGap.EpochPermutationProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open BinaryPointerListRead (PointerList pointerList_extend)
open PhysicalBoundedDrawProgram (Outcome)
open PhysicalDrawSequenceProgram (StoredBatch batch_extend)
open EpochPermutationData (Valid reorder suffix)

def selectLabel (pc : Fin 65) : Fin 97 := ⟨32+pc.val,by omega⟩

def program : Program 97 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .branch .r0 9 31 31 12
    | 9 => .make .r3 .nil 10
    | 10 => .make .r3 (.pair .r3 .r1) 11
    | 11 => .ret .r3
    | 12 => .call 20 13 .r3
    | 13 => .field .r2 .r3 false 14
    | 14 => .field .r0 .r3 true 15
    | 15 => .field .r1 .r1 true 16
    | 16 => .call 8 17 .r3
    | 17 => .field .r0 .r3 false 18
    | 18 => .make .r0 (.pair .r2 .r0) 19
    | 19 => .field .r1 .r3 true 23
    | 20 => .field .r1 .r1 false 21
    | 21 => .field .r1 .r1 false (selectLabel 0)
    | 23 => .make .r3 (.pair .r0 .r1) 11
    | _ => .halt
  else if pc.val=39 then .ret .r3
  else ReferenceProgramLabels.instruction selectLabel
    (EpochPrefixSelectionProgram.program ⟨pc.val-32,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 97))
    (tape : Bits) (pc : Fin 97) : NaturalState 97 := ⟨heap,heap.length,r,stack,pc,tape⟩

def indices (draws : List Outcome) : List ℕ := draws.map fun d => value d.index

def Output (heap : NaturalHeap) (root : ℕ) (order : List ℕ) (remaining : List Outcome) : Prop :=
  ∃ elements draws,heap[root]?=some (.pair elements draws) ∧ PointerList heap elements order ∧
    StoredBatch heap draws remaining

def bodySteps : List Outcome→ℕ
  | [] => 4
  | d::ds => EpochPrefixSelectionProgram.steps d.index+bodySteps ds+14

def steps (draws : List Outcome) : ℕ := bodySteps draws+1

def instructionBound (n W : ℕ) : ℕ := n*(13*n+10*W+33)+5

theorem steps_le (pre : List Outcome) {n W : ℕ} (valid : Valid (indices pre) n)
    (widths : ∀ d ∈ pre,d.index.length≤W) : steps pre ≤ instructionBound n W := by
  have costs (ds : List Outcome) (bounds : ∀ d ∈ ds,value d.index≤n ∧ d.index.length≤W) :
      bodySteps ds≤ds.length*(13*n+10*W+33)+4 := by
    induction ds with
    | nil => simp [bodySteps]
    | cons d ds ih =>
      have ⟨v,w⟩ := bounds d (by simp)
      have sub := ih (fun x hx => bounds x (List.mem_cons_of_mem _ hx))
      have used := EpochPrefixSelectionProgram.steps_le d.index
      rw [bodySteps,List.length_cons,Nat.succ_mul]
      omega
  have len : pre.length=n := by simpa [indices] using EpochPermutationData.valid_length valid
  have bound := costs pre (fun d mem => ⟨
    (EpochPermutationData.valid_bound valid (List.mem_map.mpr ⟨d,mem,rfl⟩)).le,widths d mem⟩)
  rw [len] at bound
  exact Nat.add_le_add_right bound 1

private theorem select_slots (pc : Fin 65) (h : EpochPrefixSelectionProgram.program pc≠.halt) :
    program (selectLabel pc)=ReferenceProgramLabels.instruction selectLabel (EpochPrefixSelectionProgram.program pc) := by
  by_cases hp : pc.val=7
  · have eq : pc=7 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,selectLabel,show ¬32+pc.val<32 by omega,show 32+pc.val≠39 by omega]

private theorem select_call {heap : NaturalHeap} {r : Registers ℕ} {head : ℕ} {tail : List ℕ}
    {first : Outcome} {draw more : ℕ}
    (input : PointerList heap r.a (head::tail))
    (listPair : heap[r.b]?=some (.pair draw more)) (result : PhysicalBoundedDrawProgram.ResultAt heap draw first)
    (bound : value first.index<(head::tail).length) (stack : List (Frame ℕ 97)) (tape : Bits) :
    ∃ ext root,EpochPrefixSelectionProgram.Stored (heap++ext) root (head::tail)[value first.index]
        (suffix head tail (value first.index)) ∧
      NaturalRun program (EpochPrefixSelectionProgram.steps first.index+4) (state heap r stack tape 12) []
        (state (heap++ext) (r.set .r3 root) stack tape 13) := by
  obtain ⟨index,tag,pair,word,_⟩ := result
  let args := r.set .r1 index
  let frame : Frame ℕ 97 := ⟨13,.r3,r⟩
  have setup : NaturalRun program 3 (state heap r stack tape 12) []
      (state heap args (frame::stack) tape (selectLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,frame,listPair,pair]
  obtain ⟨ext,regs,root,rep,body⟩ := EpochPrefixSelectionProgram.natural_select (r:=args) input word bound tape
  let stop := state (heap++ext) (regs.set .r3 root) (frame::stack) tape (selectLabel 7)
  have lifted := ReferenceProgramLabels.run selectLabel EpochPrefixSelectionProgram.program program select_slots body
  have lifted := ReferenceProgramStack.run program (frame::stack) lifted
  let work := EpochPrefixSelectionProgram.steps first.index
  have run : NaturalRun program work (state heap args (frame::stack) tape (selectLabel 0)) [] stop := by
    simpa [state,stop,work,EpochPrefixSelectionProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) stack tape 13,[],0⟩ := by
    simp [state,stop,program,selectLabel,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,rep,?_⟩
  have count : 3+(work+1)=work+4 := by omega
  change NaturalRun program (work+4) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

set_option maxHeartbeats 1600000 in
private theorem permute_return {heap : NaturalHeap} {r : Registers ℕ} {xs : List ℕ} {pre post : List Outcome}
    (items : PointerList heap r.a xs) (batch : StoredBatch heap r.b (pre++post))
    (valid : Valid (indices pre) xs.length) (caller : Frame ℕ 97) (stack : List (Frame ℕ 97)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ) (order : List ℕ),
      reorder (indices pre) xs=some order ∧ Output (heap++ext) root order post ∧
      NaturalRun program (bodySteps pre) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction pre generalizing heap r xs caller stack with
  | nil =>
    cases xs with
    | cons head tail => cases valid
    | nil =>
      cases items with
      | nil empty =>
        let i := heap.length
        let cell : Cell ℕ := .pair i r.b
        let ext : NaturalHeap := [.nil,cell]
        have link : (heap++ext)[i+1]?=some cell := by
          rw [List.getElem?_append_right (show heap.length ≤ i+1 by omega)]
          rw [show i+1-heap.length=1 by simp [i]]
          rfl
        refine ⟨ext,i+1,[],rfl,⟨i,r.b,link,.nil (by simp [i,ext]),batch_extend batch ext⟩,?_⟩
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,bodySteps,tagBranch,empty,
          i,ext,cell,allocateNatural,Recipe.cell,List.append_assoc]
  | cons first pre ih =>
    cases xs with
    | nil => cases valid
    | cons head tail =>
      simp only [indices,List.map_cons,List.length_cons] at valid
      cases valid with
      | cons inside remaining =>
        simp only [List.cons_append] at batch
        cases batch with
        | @cons _ draw more _ _ pair result resid =>
          have row : ∃ p,heap[r.a]?=some (.pair head p) := by
            cases items with | cons hp _ => exact ⟨_,hp⟩
          obtain ⟨tailRoot,cell⟩ := row
          let saved := caller::stack
          have enter : tickNatural program (state heap r saved tape 8)=some ⟨state heap r saved tape 12,[],0⟩ := by
            simp [state,program,tickNatural,Registers.get,tagBranch,cell]
          have bound : value first.index<(head::tail).length := inside
          obtain ⟨es,selected,⟨rest,selection,available⟩,pick⟩ := select_call items pair result bound saved tape
          let mid := heap++es
          let start := r.set .r3 selected
          let item := (head::tail)[value first.index]
          let args := ((start.set .r2 item).set .r0 rest).set .r1 more
          let frame : Frame ℕ 97 := ⟨17,.r3,args⟩
          have chosen : mid[selected]?=some (.pair item rest) := selection
          have later : mid[r.b]?=some (.pair draw more) := lookup_extend pair es
          have prep : NaturalRun program 4 (state mid start saved tape 13) [] (state mid args (frame::saved) tape 8) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,start,args,frame,chosen,later]
          have correct : Valid (indices pre) (suffix head tail (value first.index)).length := by
            simpa only [EpochPermutationData.suffix_length,indices] using remaining
          obtain ⟨ep,suffixRoot,order,valueEq,⟨perm,draws,returned,permRep,gridRep⟩,run⟩ :=
            ih (r:=args) available (batch_extend resid es) correct frame saved
          let grown := mid++ep
          let i := grown.length
          let a : Cell ℕ := .pair item perm
          let b : Cell ℕ := .pair i draws
          let ext : NaturalHeap := [a,b]
          have suffixIn : grown[suffixRoot]?=some (.pair perm draws) := returned
          have suffixLater : (grown++[a])[suffixRoot]?=some (.pair perm draws) := lookup_extend suffixIn [a]
          have finish : NaturalRun program 5 (state grown (args.set .r3 suffixRoot) saved tape 17) []
              (state (grown++ext) (caller.saved.set caller.destination (i+1)) stack tape caller.continuation) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,suffixIn,suffixLater,
              args,item,i,a,b,ext,allocateNatural,Recipe.cell,List.append_assoc,saved]
          have output : Output (grown++ext) (i+1) (item::order) post := by
            have link : (grown++ext)[i+1]?=some b := by
              rw [List.getElem?_append_right (show grown.length ≤ i+1 by omega)]
              rw [show i+1-grown.length=1 by simp [i]]
              rfl
            exact ⟨i,draws,link,.cons (by simp [i,ext,a]) (pointerList_extend permRep ext),batch_extend gridRep ext⟩
          refine ⟨es++ep++ext,i+1,item::order,?_,?_,?_⟩
          · simp only [indices,List.map_cons,reorder,List.getElem?_eq_getElem bound]
            change (do let tail ← reorder (indices pre) (suffix head tail (value first.index)); pure (item::tail))=_
            rw [valueEq]
            rfl
          · simpa only [grown,mid,List.append_assoc] using output
          · let k := EpochPrefixSelectionProgram.steps first.index
            have count : k+4+(4+(bodySteps pre+5))+1=k+bodySteps pre+14 := by omega
            simp only [bodySteps]
            rw [← count]
            simpa only [grown,mid,k,List.append_assoc,List.nil_append] using NaturalRun.step enter
              (append_run pick (append_run prep (append_run run finish)))

theorem natural_permutation {heap : NaturalHeap} {r : Registers ℕ} {xs : List ℕ} {pre post : List Outcome}
    (items : PointerList heap r.a xs) (batch : StoredBatch heap r.b (pre++post)) (valid : Valid (indices pre) xs.length)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ) (order : List ℕ),
      reorder (indices pre) xs=some order ∧ Output (heap++ext) root order post ∧
      NaturalRun program (steps pre) (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let caller : Frame ℕ 97 := ⟨1,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [caller] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,order,eq,rep,body⟩ := permute_return items batch valid caller [] tape
  exact ⟨ext,root,order,eq,rep,.step enter body⟩

theorem natural_tape_permutation {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {xs : List ℕ} {pre post : List Outcome}
    (items : PointerList heap r.a xs) (batch : StoredBatch heap r.b (pre++post))
    (len : xs.length=n) (draws : FinitePermutationSampler.Tape n)
    (values : indices pre=PhysicalEpochDraws.permutationValues n draws) (tape : Bits) :
    let order := (FinitePermutationSampler.run n draws).order.map (fun i => xs[i.val]'(len ▸ i.isLt))
    ∃ ext root,Output (heap++ext) root order post ∧
      NaturalRun program (steps pre) (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  have valid : Valid (indices pre) xs.length := by
    rw [len,values]
    exact EpochPermutationData.values_valid n draws
  obtain ⟨ext,root,order,eq,rep,body⟩ := natural_permutation items batch valid tape
  rw [values,EpochPermutationData.reorder_tape n draws xs len] at eq
  cases eq
  exact ⟨ext,root,rep,body⟩

end DirectedFlowCutGap.EpochPermutationProgram
