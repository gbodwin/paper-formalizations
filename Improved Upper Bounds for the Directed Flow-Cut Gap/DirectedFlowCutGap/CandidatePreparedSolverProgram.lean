import DirectedFlowCutGap.CandidateConfiguredCutProgram
import DirectedFlowCutGap.CandidateDecoderProgram

/-!
# Physical candidate solver with prepared capacities

On a single heap, the solver constructs the cut configuration, computes
the retained cut, and gives the returned cut pointer to the decoder.
The decoder uses the removal mask and grid word from the same input
pair used by the cut computation.
-/

namespace DirectedFlowCutGap.CandidatePreparedSolverProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor CandidateClosureProvider IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open EncodedCandidateCapacity (Input)
open CandidatePhysicalCut (networkSize capacityWidth capacities outputMask)
open ResidualZeroTableProgram (CapacityRows CapacityValues)
open PathCostMaterialization (WordList)
open CandidateNumeratorScanProgram (scan)

def cutLabel (pc : Fin 2177) : Fin 2386 := ⟨16+pc.val,by omega⟩
def decoderLabel (pc : Fin 193) : Fin 2386 := ⟨2193+pc.val,by omega⟩

def program : Program 2386 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (cutLabel 0) 1 .r0
    | 1 => .field .r1 .r2 false 2
    | 2 => .field .r2 .r2 true 3
    | 3 => .call (decoderLabel 0) 4 .r3
    | _ => .halt
  else if h : pc.val<2193 then
    if pc.val=18 then .ret .r3
    else ReferenceProgramLabels.instruction cutLabel
      (CandidateConfiguredCutProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=2196 then .ret .r3
  else ReferenceProgramLabels.instruction decoderLabel
    (CandidateDecoderProgram.program ⟨pc.val-2193,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 2386))
    (tape : Bits) (pc : Fin 2386) : NaturalState 2386 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n L vertexWidth gridWidth : ℕ) : ℕ :=
  CandidateConfiguredCutProgram.instructionBound n L vertexWidth gridWidth+
    CandidateDecoderProgram.instructionBound L n gridWidth+6

private theorem cut_slots (pc : Fin 2177) (h : CandidateConfiguredCutProgram.program pc≠.halt) :
    program (cutLabel pc)=ReferenceProgramLabels.instruction cutLabel (CandidateConfiguredCutProgram.program pc) := by
  by_cases hp : pc.val=2
  · have eq : pc=2 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,cutLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<2193 by omega,show 16+pc.val≠18 by omega]

private theorem decoder_slots (pc : Fin 193) (h : CandidateDecoderProgram.program pc≠.halt) :
    program (decoderLabel pc)=ReferenceProgramLabels.instruction decoderLabel (CandidateDecoderProgram.program pc) := by
  by_cases hp : pc.val=3
  · have eq : pc=3 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,decoderLabel,show ¬2193+pc.val<16 by omega,
      show ¬2193+pc.val<2193 by omega,show 2193+pc.val≠2196 by omega]

private theorem cut_call {heap : NaturalHeap} {r : Registers ℕ} {ext : NaturalHeap} {args : Registers ℕ}
    {root k : ℕ} {tape : Bits}
    (body : NaturalRun CandidateConfiguredCutProgram.program k
      (CandidateConfiguredCutProgram.state heap r [] tape 0) []
      (CandidateConfiguredCutProgram.state (heap++ext) (args.set .r3 root) [] tape 2)) :
    NaturalRun program (k+2) (state heap r [] tape 0) [] (state (heap++ext) (r.set .r0 root) [] tape 1) := by
  let frame : Frame ℕ 2386 := ⟨1,.r0,r⟩
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (cutLabel 2)
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape (cutLabel 0),[],0⟩ := rfl
  have lifted := ReferenceProgramLabels.run cutLabel CandidateConfiguredCutProgram.program program cut_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program k (state heap r [frame] tape (cutLabel 0)) [] stop := by
    simpa [state,stop,CandidateConfiguredCutProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r0 root) [] tape 1,[],0⟩ := by
    simp [state,stop,program,cutLabel,tickNatural,frame,Registers.get,Registers.set]
  exact .step enter (append_run run (.step ret (.done _)))

private theorem decode_call {heap : NaturalHeap} {r : Registers ℕ} {left right : ℕ} {flags grid removed : Bits}
    (cut : BoolList heap r.a flags) (input : heap[r.c]?=some (.pair left right))
    (mask : BoolList heap left removed) (word : BoolList heap right grid)
    (fits : ((value grid+1)+(value grid+1))*removed.length≤flags.length) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),WordList (heap++ext) root (scan (value grid+1) grid flags removed) ∧
      NaturalRun program (CandidateDecoderProgram.steps grid flags removed+4) (state heap r [] tape 1) []
        (state (heap++ext) (args.set .r3 root) [] tape 4) := by
  let args := (r.set .r1 left).set .r2 right
  let frame : Frame ℕ 2386 := ⟨4,.r3,args⟩
  have setup : NaturalRun program 3 (state heap r [] tape 1) [] (state heap args [frame] tape (decoderLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,frame,input]
  obtain ⟨ext,regs,root,rep,body⟩ := CandidateDecoderProgram.natural_decode (r:=args) cut mask word fits tape
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (decoderLabel 3)
  have lifted := ReferenceProgramLabels.run decoderLabel CandidateDecoderProgram.program program decoder_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program (CandidateDecoderProgram.steps grid flags removed)
      (state heap args [frame] tape (decoderLabel 0)) [] stop := by
    simpa [state,stop,CandidateDecoderProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (args.set .r3 root) [] tape 4,[],0⟩ := by
    simp [state,stop,program,decoderLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,args,root,rep,?_⟩
  let work := CandidateDecoderProgram.steps grid flags removed
  have count : 3+(work+1)=work+4 := by omega
  change NaturalRun program (work+4) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

theorem natural_prepared_solver {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {left right : ℕ}
    (D : Input n) (s t : Fin n) (L B : ℕ)
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L))
    (cs : List (List Bits)) (values : CapacityValues (capacities D s t L B) cs (List.finRange (networkSize n L))
      (List.finRange (networkSize n L)))
    (widths : ∀ row ∈ cs,∀ cap ∈ row,cap.length≤capacityWidth n L) (input : CapacityRows heap r.a cs)
    (vertices grid : Bits) (numeric : value vertices=n) (scale : value grid=L) (size : BoolList heap r.b vertices)
    (pair : heap[r.c]?=some (.pair left right)) (mask : BoolList heap left D.removed.toList)
    (word : BoolList heap right grid) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      WordList (heap++ext) root (scan (L+1) grid (outputMask D s t L B EN E) D.removed.toList) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 4) ∧
      k ≤ instructionBound n L vertices.length grid.length := by
  let flags := outputMask D s t L B EN E
  obtain ⟨ec,regs,cut,k,rep,body,bound⟩ := CandidateConfiguredCutProgram.natural_configured_cut D s t L B positive feasible
    EN E cs values widths input vertices grid numeric scale size pair mask word tape
  let mid := heap++ec
  let returned := r.set .r0 cut
  have run := cut_call body
  have fits : ((value grid+1)+(value grid+1))*D.removed.toList.length≤flags.length := by
    rw [scale]
    exact CandidateNumeratorScanProgram.mask_fits D s t L B EN E
  obtain ⟨ed,args,root,output,decode⟩ := decode_call (r:=returned) rep (lookup_extend pair ec)
    (boolList_extend mask ec) (boolList_extend word ec) fits tape
  refine ⟨ec++ed,args,root,k+CandidateDecoderProgram.steps grid flags D.removed.toList+6,?_,?_,?_⟩
  · simpa only [mid,scale,List.append_assoc] using output
  · let work := CandidateDecoderProgram.steps grid flags D.removed.toList
    have count : k+2+(work+4)=k+work+6 := by omega
    change NaturalRun program (k+work+6) _ [] _
    rw [← count]
    simpa only [mid,work,List.append_assoc,List.nil_append] using append_run run decode
  · have decodeBound := CandidateDecoderProgram.steps_le grid flags D.removed.toList
    rw [scale,Vector.length_toList] at decodeBound
    unfold instructionBound
    omega

private theorem at_entry (s : NaturalState 2386) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_prepared_solver {n H A left right : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ)
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L))
    (cs : List (List Bits)) (values : CapacityValues (capacities D s t L B) cs (List.finRange (networkSize n L))
      (List.finRange (networkSize n L)))
    (widths : ∀ row ∈ cs,∀ cap ∈ row,cap.length≤capacityWidth n L)
    (initial : BitState 2386) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : CapacityRows (eraseState initial).heap (eraseState initial).registers.a cs)
    (vertices grid : Bits) (numeric : value vertices=n) (scale : value grid=L)
    (size : BoolList (eraseState initial).heap (eraseState initial).registers.b vertices)
    (pair : (eraseState initial).heap[(eraseState initial).registers.c]?=some (.pair left right))
    (mask : BoolList (eraseState initial).heap left D.removed.toList) (word : BoolList (eraseState initial).heap right grid) :
    ∃ (charge steps : ℕ) (out : BitState 2386) (words : List Bits),Run program steps charge initial [] out ∧
      WordList (eraseState out).heap (eraseState out).registers.d words ∧
      words.map (fun x => (value x : ℤ)) =
        (EncodedCandidateOutput.solve D s t L B EN E (ResidualSearch.Enumeration.fin n)).numerators.map Prod.snd ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=4 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 2386 H A (instructionBound n L vertices.length grid.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,k,rep,body,bound⟩ := natural_prepared_solver D s t L B positive feasible EN E cs values widths
    input vertices grid numeric scale size pair mask word old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 4
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have run : NaturalRun program k old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨paid,out,execution,hout,hstop,charge,unchanged⟩ := terminating_simulation bounded run stop
  refine ⟨paid,k,out,_,execution,?_,CandidateNumeratorScanProgram.scan_candidate_values D s t L B positive feasible EN E grid scale,
    unchanged,?_,?_,⟨ext,?_⟩,hstop,charge.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ bound)⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.CandidatePreparedSolverProgram
