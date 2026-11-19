import DirectedFlowCutGap.CandidateNumeratorCellProgram
import DirectedFlowCutGap.CandidateMaskNumeratorData
import DirectedFlowCutGap.PathCostMaterialization

/-!
# Decode the core numerator list in vertex order

Each step consumes two blocks of the previous step's mask suffix. It
returns the actual numerator word and retains the same grid and block
length. No port or artificial-terminal block is needed for the output.
-/

namespace DirectedFlowCutGap.CandidateNumeratorScanProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open PathCostMaterialization (WordList list_extend)

def cellLabel (pc : Fin 112) : Fin 144 := ⟨32+pc.val,by omega⟩

def program : Program 144 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .branch .r1 9 31 31 12
    | 9 => .make .r3 .nil 10
    | 10 => .ret .r3
    | 12 => .call 20 13 .r3
    | 13 => .field .r0 .r3 false 14
    | 14 => .field .r3 .r3 true 15
    | 15 => .field .r1 .r1 true 16
    | 16 => .call 8 17 .r0
    | 17 => .make .r3 (.pair .r3 .r0) 10
    | 20 => .field .r3 .r1 false 21
    | 21 => .field .r1 .r2 false 22
    | 22 => .make .r3 (.pair .r3 .r1) 23
    | 23 => .field .r1 .r2 true 24
    | 24 => .move .r2 .r3 (cellLabel 0)
    | _ => .halt
  else if pc.val=46 then .ret .r3
  else ReferenceProgramLabels.instruction cellLabel
    (CandidateNumeratorCellProgram.program ⟨pc.val-32,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 144))
    (tape : Bits) (pc : Fin 144) : NaturalState 144 := ⟨heap,heap.length,r,stack,pc,tape⟩

def Context (heap : NaturalHeap) (root k : ℕ) (grid : Bits) : Prop :=
  ∃ word limit,heap[root]?=some (.pair word limit) ∧ BoolList heap word grid ∧ IndexSpine heap limit k

theorem context_extend {heap : NaturalHeap} {root k : ℕ} {grid : Bits}
    (context : Context heap root k grid) (ext : NaturalHeap) : Context (heap++ext) root k grid := by
  obtain ⟨word,limit,pair,scale,unary⟩ := context
  exact ⟨word,limit,lookup_extend pair ext,boolList_extend scale ext,indexSpine_extend unary ext⟩

def scan (k : ℕ) (grid flags : Bits) : Bits→List Bits
  | [] => []
  | removed::rest => CandidateNumeratorCellProgram.word k flags grid removed::scan k grid (flags.drop (k+k)) rest

@[simp] theorem scan_length (k : ℕ) (grid flags removed : Bits) : (scan k grid flags removed).length=removed.length := by
  induction removed generalizing flags with
  | nil => rfl
  | cons b bs ih => simp [scan,ih]

theorem scan_get (k : ℕ) (grid flags removed : Bits) (i : ℕ) (hi : i<removed.length) :
    (scan k grid flags removed)[i]'(by simpa using hi)=
      CandidateNumeratorCellProgram.word k (flags.drop (i*(k+k))) grid removed[i] := by
  induction removed generalizing flags i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [scan]
    | succ i =>
      have bound : i < bs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      have shifted := ih (flags.drop (k+k)) i bound
      simpa [scan,List.drop_drop,Nat.succ_mul,Nat.add_comm] using shifted

def bodySteps (k : ℕ) (flags : Bits) : Bits→ℕ
  | [] => 3
  | removed::rest => CandidateNumeratorCellProgram.steps k flags removed+bodySteps k (flags.drop (k+k)) rest+14

def steps (k : ℕ) (flags removed : Bits) : ℕ := bodySteps k flags removed+1
def instructionBound (k n : ℕ) : ℕ := n*(CandidateNumeratorCellProgram.instructionBound k+14)+4

theorem steps_le (k : ℕ) (flags removed : Bits) : steps k flags removed ≤ instructionBound k removed.length := by
  have h (flags removed : Bits) : bodySteps k flags removed ≤
      removed.length*(CandidateNumeratorCellProgram.instructionBound k+14)+3 := by
    induction removed generalizing flags with
    | nil => simp [bodySteps]
    | cons b bs ih =>
      have cell := CandidateNumeratorCellProgram.steps_le k flags b
      have tail := ih (flags.drop (k+k))
      rw [bodySteps,List.length_cons,Nat.succ_mul bs.length (CandidateNumeratorCellProgram.instructionBound k+14)]
      omega
  exact Nat.add_le_add_right (h flags removed) 1

private theorem slots (pc : Fin 112) (h : CandidateNumeratorCellProgram.program pc≠.halt) :
    program (cellLabel pc)=ReferenceProgramLabels.instruction cellLabel (CandidateNumeratorCellProgram.program pc) := by
  by_cases hp : pc.val=14
  · have eq : pc=14 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,cellLabel,show ¬32+pc.val<32 by omega,show 32+pc.val≠46 by omega]

set_option maxHeartbeats 1000000 in
private theorem cell_call {heap : NaturalHeap} {r : Registers ℕ} {flags grid : Bits} {k head tail : ℕ} {removed : Bool}
    (mask : BoolList heap r.a flags) (context : Context heap r.c k grid) (fits : k+k≤flags.length)
    (pair : heap[r.b]?=some (.pair head tail)) (flag : heap[head]?=some (.flag removed))
    (stack : List (Frame ℕ 144)) (tape : Bits) :
    ∃ ext root,CandidateNumeratorCellProgram.Stored (heap++ext) root (flags.drop (k+k))
        (CandidateNumeratorCellProgram.word k flags grid removed) ∧
      NaturalRun program (CandidateNumeratorCellProgram.steps k flags removed+7) (state heap r stack tape 12) []
        (state (heap++ext) (r.set .r3 root) stack tape 13) := by
  obtain ⟨gridRoot,limit,ctx,gridRep,fuel⟩ := context
  let i := heap.length
  let info : Cell ℕ := .pair head gridRoot
  let mid := heap++[info]
  let args := ((r.set .r3 i).set .r1 limit).set .r2 i
  let frame : Frame ℕ 144 := ⟨13,.r3,r⟩
  have ctxIn : mid[r.c]?=some (.pair gridRoot limit) := lookup_extend ctx [info]
  have setup : NaturalRun program 6 (state heap r stack tape 12) [] (state mid args (frame::stack) tape (cellLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      i,info,mid,args,frame,pair,ctx,ctxIn]
  have mode : CandidateNumeratorCellProgram.Mode mid args.c removed grid :=
    ⟨head,gridRoot,by simp [mid,args,Registers.set,i,info],lookup_extend flag [info],boolList_extend gridRep [info]⟩
  obtain ⟨ext,regs,root,rep,body⟩ := CandidateNumeratorCellProgram.natural_cell (r:=args)
    (boolList_extend mask [info]) (indexSpine_extend fuel [info]) fits mode tape
  let stop := state (mid++ext) (regs.set .r3 root) (frame::stack) tape (cellLabel 14)
  have lift := ReferenceProgramLabels.run cellLabel CandidateNumeratorCellProgram.program program slots body
  have lift := ReferenceProgramStack.run program (frame::stack) lift
  have run : NaturalRun program (CandidateNumeratorCellProgram.steps k flags removed)
      (state mid args (frame::stack) tape (cellLabel 0)) [] stop := by
    simpa [mid,state,stop,CandidateNumeratorCellProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (mid++ext) (r.set .r3 root) stack tape 13,[],0⟩ := by
    simp [state,stop,cellLabel,program,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨[info]++ext,root,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · have full := append_run setup (append_run run (.step ret (.done _)))
    let work := CandidateNumeratorCellProgram.steps k flags removed
    have same : 6+(work+1)=work+7 := by omega
    change NaturalRun program (work+7) _ [] _
    rw [← same]
    simpa only [mid,List.append_assoc,List.nil_append] using full

private theorem scan_return {heap : NaturalHeap} {r : Registers ℕ} {flags grid removed : Bits} {k : ℕ}
    (mask : BoolList heap r.a flags) (removal : BoolList heap r.b removed) (context : Context heap r.c k grid)
    (fits : (k+k)*removed.length≤flags.length) (caller : Frame ℕ 144) (stack : List (Frame ℕ 144)) (tape : Bits) :
    ∃ ext root,WordList (heap++ext) root (scan k grid flags removed) ∧
      NaturalRun program (bodySteps k flags removed) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction removed generalizing heap r flags caller stack with
  | nil =>
    cases removal with
    | nil hp =>
      refine ⟨[.nil],heap.length,.nil (by simp),?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,bodySteps,tickNatural,Registers.get,Registers.set,
        allocateNatural,Recipe.cell,tagBranch,hp]
  | cons b bs ih =>
    cases removal with
    | @cons _ flag tail _ _ pair active remain =>
      let saved := caller::stack
      simp only [List.length_cons,Nat.mul_succ] at fits
      have entry : tickNatural program (state heap r saved tape 8)=some ⟨state heap r saved tape 12,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,pair]
      obtain ⟨ec,cell,⟨next,height,outPair,midMask,headWord⟩,compute⟩ := cell_call mask context (by omega) pair active saved tape
      let mid := heap++ec
      let returned := r.set .r3 cell
      let args := (((returned.set .r0 next).set .r3 height).set .r1 tail)
      let frame : Frame ℕ 144 := ⟨17,.r0,args⟩
      have prepare : NaturalRun program 4 (state mid returned saved tape 13) [] (state mid args (frame::saved) tape 8) := by
        have old : mid[r.b]?=some (.pair flag tail) := lookup_extend pair ec
        have new : mid[cell]?=some (.pair next height) := outPair
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,returned,frame,old,new]
      have enough : (k+k)*bs.length≤(flags.drop (k+k)).length := by simp only [List.length_drop]; omega
      obtain ⟨er,rest,rep,run⟩ := ih (r:=args) midMask (boolList_extend remain ec) (context_extend context ec) enough frame saved
      let grown := mid++er
      let node : Cell ℕ := .pair height rest
      let root := grown.length
      have finish : NaturalRun program 2 (state grown (args.set .r0 rest) saved tape 17) []
          (state (grown++[node]) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
          root,node,args,saved]
      have output : WordList (grown++[node]) root (scan k grid flags (b::bs)) := .cons
        (by simp [root,node]) (boolList_extend (boolList_extend headWord er) [node]) (list_extend rep [node])
      refine ⟨ec++er++[node],root,?_,?_⟩
      · simpa only [mid,grown,List.append_assoc] using output
      · have full := NaturalRun.step entry (append_run compute (append_run prepare (append_run run finish)))
        simp only [bodySteps]
        convert full using 1 <;> first | rfl | omega | simp only [mid,grown,List.append_assoc]

theorem natural_scan {heap : NaturalHeap} {r : Registers ℕ} {flags grid removed : Bits} {k : ℕ}
    (mask : BoolList heap r.a flags) (removal : BoolList heap r.b removed) (context : Context heap r.c k grid)
    (fits : (k+k)*removed.length≤flags.length) (tape : Bits) :
    ∃ ext root,WordList (heap++ext) root (scan k grid flags removed) ∧
      NaturalRun program (steps k flags removed) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let frame : Frame ℕ 144 := ⟨1,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,rep,body⟩ := scan_return mask removal context fits frame [] tape
  exact ⟨ext,root,rep,.step enter body⟩

open EncodedCandidateCapacity (Input)
open CandidateNumeratorCellProgram (firstCount secondCount)
open CandidateMaskNumeratorData (block numerator)

private theorem first_block {n : ℕ} (L : ℕ) (flags : Bits) (v : Fin n) :
    firstCount (L+1) (flags.drop (v.val*((L+1)+(L+1)))) =
      (block L flags (TerminalPorts.core v,false)).count true := by
  have offset : v.val*((L+1)+(L+1))=2*v.val*(L+1) := by ring
  simp only [firstCount,block,CandidateEnumeration.pointIndex,CandidateEnumeration.portIndex,
    Bool.false_eq_true,ite_false,add_zero,offset]

private theorem second_block {n : ℕ} (L : ℕ) (flags : Bits) (v : Fin n) :
    secondCount (L+1) (flags.drop (v.val*((L+1)+(L+1)))) =
      (block L flags (TerminalPorts.core v,true)).count true := by
  have offset : v.val*((L+1)+(L+1))+(L+1)=(2*v.val+1)*(L+1) := by ring
  simp only [secondCount,block,List.drop_drop,CandidateEnumeration.pointIndex,CandidateEnumeration.portIndex,
    ite_true,offset]

theorem scan_values {n : ℕ} (D : Input n) (L : ℕ) (flags grid : Bits) (l : value grid=L) :
    (scan (L+1) grid flags D.removed.toList).map value =
      (List.finRange n).map (numerator D L flags) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have bound : i<n := by simpa using hj
    let v : Fin n := ⟨i,bound⟩
    have inside : i<D.removed.toList.length := by simpa using bound
    have vFlag : D.removed.toList[i]=D.removed[v.val] := by simp [v]
    simp only [List.getElem_map,List.getElem_finRange,scan_get (L+1) grid flags D.removed.toList i inside,vFlag]
    change value (CandidateNumeratorCellProgram.word (L+1) (flags.drop (v.val*((L+1)+(L+1)))) grid D.removed[v.val]) =
      numerator D L flags v
    cases status : D.removed[v.val] <;> simp [CandidateNumeratorCellProgram.word,numerator,status,l,
      first_block,second_block,value_bits]

open CandidateClosureProvider IntegralNetworkFlow
open CandidatePhysicalCut (outputMask networkSize)

theorem scan_candidate_values {n : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ)
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L)) (grid : Bits) (scale : value grid=L) :
    (scan (L+1) grid (outputMask D s t L B EN E) D.removed.toList).map (fun x => (value x : ℤ)) =
      (EncodedCandidateOutput.solve D s t L B EN E (ResidualSearch.Enumeration.fin n)).numerators.map Prod.snd := by
  let flags := outputMask D s t L B EN E
  calc
    _ = (List.finRange n).map (fun v => (numerator D L flags v : ℤ)) := by
      simpa only [List.map_map,Function.comp_def,flags] using
        congrArg (List.map (fun x : ℕ => (x : ℤ))) (scan_values D L flags grid scale)
    _ = _ := by
      simpa only [List.map_map,Function.comp_def,flags] using congrArg (List.map Prod.snd)
        (CandidateMaskNumeratorData.numerators_eq D s t L B positive feasible EN E)

theorem mask_fits {n : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L)) :
    ((L+1)+(L+1))*D.removed.toList.length≤(outputMask D s t L B EN E).length := by
  simp only [Vector.length_toList,outputMask,List.length_map,List.length_finRange,networkSize]
  nlinarith

end DirectedFlowCutGap.CandidateNumeratorScanProgram
