import DirectedFlowCutGap.IntegerLevelCutProgram
import DirectedFlowCutGap.RoundStateUpdateProgram

/-!
# Physical rounding step at the selected pair and level

This joins the actual midpoint scan to the actual mask and mass update.
The updater receives the cut root returned by the scan. The represented
optimizer output and level index are inputs. Neither routine reads the tape.
-/

namespace DirectedFlowCutGap.PhysicalSampledRoundProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open IntegerDistanceFromPhysical (encodedRow)
open RetainedMassTableProgram (TableAt DataRows)
open RoundMaskUpdateProgram (MaskPairAt)

def cutLabel (pc : Fin 1572) : Fin 1982 := ⟨8+pc.val,by omega⟩
def updateLabel (pc : Fin 402) : Fin 1982 := ⟨1580+pc.val,by omega⟩

def program : Program 1982 := fun pc =>
  if pc.val < 8 then
    match pc.val with
    | 0 => .call (cutLabel 0) 1 .r0
    | 1 => .move .r2 .r0 2
    | 2 => .field .r0 .r3 false 3
    | 3 => .field .r3 .r3 true 4
    | 4 => .field .r1 .r3 false 5
    | 5 => .field .r3 .r3 true (updateLabel 0)
    | _ => .halt
  else if pc.val = 39 then .ret .r3
  else if h : pc.val < 1580 then
    ReferenceProgramLabels.instruction cutLabel (IntegerLevelCutProgram.program ⟨pc.val-8,by omega⟩)
  else ReferenceProgramLabels.instruction updateLabel
    (RoundStateUpdateProgram.program ⟨pc.val-1580,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 1982))
    (tape : Bits) (pc : Fin 1982) : NaturalState 1982 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def UpdateContext {n : ℕ} (heap : NaturalHeap) (root : ℕ) (d : Data n) (p : Pair n)
    (words : List (List Bits)) : Prop :=
  ∃ masks rest indices weightContext si ti weights free,
    heap[root]? = some (.pair masks rest) ∧ heap[rest]? = some (.pair indices weightContext) ∧
    MaskPairAt heap masks d.remaining d.cut ∧ heap[indices]? = some (.pair si ti) ∧
    IndexSpine heap si p.1.val ∧ IndexSpine heap ti p.2.val ∧
    heap[weightContext]? = some (.pair weights free) ∧ TableAt heap weights words ∧ heap[free]? = some (.flag false)

def cut {n : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (d : Data n) (p : Pair n) (level : Bits) : Flags n :=
  (EncodedRoundingInput.cutFlags E adjacency (row d.weights p) p.1 (value level)).1

def steps {n : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (d : Data n) (p : Pair n) (sw : Bits) (label : Fin n → Bits) (level : Bits) (words : List (List Bits)) : ℕ :=
  IntegerLevelCutProgram.steps E adjacency (row d.weights p) p.1 sw label level (List.finRange n) +
    RoundStateUpdateProgram.steps d p (cut E adjacency d p level) words + 8

def instructionBound (n W S B : ℕ) : ℕ :=
  IntegerLevelCutProgram.instructionBound n W S + RoundStateUpdateProgram.instructionBudget n B + 7

private theorem cut_slots (pc : Fin 1572) (h : IntegerLevelCutProgram.program pc ≠ .halt) :
    program (cutLabel pc) = ReferenceProgramLabels.instruction cutLabel (IntegerLevelCutProgram.program pc) := by
  by_cases hp : pc.val=31
  · have eq : pc=31 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,cutLabel,show ¬8+pc.val<8 by omega,show 8+pc.val≠39 by omega,show 8+pc.val<1580 by omega]

private theorem update_slots (pc : Fin 402) :
    program (updateLabel pc) = ReferenceProgramLabels.instruction updateLabel (RoundStateUpdateProgram.program pc) := by
  simp [program,updateLabel,show ¬1580+pc.val<8 by omega,show 1580+pc.val≠39 by omega,
    show ¬1580+pc.val<1580 by omega]

private theorem join {s u v : NaturalState 1982} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem extend_masks {n : ℕ} {heap : NaturalHeap} {root : ℕ} {remaining : PairFlags n} {old : Flags n}
    (h : MaskPairAt heap root remaining old) (ext : NaturalHeap) : MaskPairAt (heap++ext) root remaining old := by
  obtain ⟨r,c,hrecord,⟨refs,hptr,hrows⟩,hcut⟩ := h
  exact ⟨r,c,lookup_extend hrecord ext,
    ⟨refs,BinaryPointerListRead.pointerList_extend hptr ext,hrows.imp (fun _ _ h => boolList_extend h ext)⟩,
    boolList_extend hcut ext⟩

private theorem extend_table {heap : NaturalHeap} {root : ℕ} {words : List (List Bits)}
    (h : TableAt heap root words) (ext : NaturalHeap) : TableAt (heap++ext) root words := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp hw _ ih => exact .cons (lookup_extend hp ext) (PathCostMaterialization.list_extend hw ext) ih

theorem natural_round {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (d : Data n) (p : Pair n) (sw : Bits) (hs : value sw=p.1.val)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (level tape : Bits) (words : List (List Bits))
    (enum : GraphDiscoveryProgram.Vertices heap r.a (E.vertices.map label))
    (targets : WordPairTableRead.Table heap r.b (IntegerLevelCutProgram.fields (row d.weights p) label (List.finRange n)))
    (context : IntegerLevelCutProgram.InputContext heap r.c (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
      (encodedRow (row d.weights p)).toList sw (label p.1) level)
    (update : UpdateContext heap r.d d p words) (hdata : DataRows d.weights words) :
    ∃ ext out, RoundStateUpdateProgram.UpdatedAt (heap++ext) out.d
        (EncodedRoundingState.roundData d p (cut E adjacency d p level)).1 ∧
      NaturalRun program (steps E adjacency d p sw label level words) (state heap r [] tape 0) []
        (state (heap++ext) out [] tape (updateLabel 5)) := by
  let y := cut E adjacency d p level
  let frame : Frame ℕ 1982 := ⟨1,.r0,r⟩
  obtain ⟨ec,root,hcut,hscan⟩ := IntegerLevelCutProgram.natural_cut E adjacency (row d.weights p)
    p.1 sw hs label hlabel level tape enum targets context
  let mid := heap++ec
  let rc := r.set .r0 root
  have call : tickNatural program (state heap r [] tape 0) = some ⟨state heap r [frame] tape (cutLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run cutLabel IntegerLevelCutProgram.program program cut_slots hscan
  have lift := ReferenceProgramStack.run program [frame] lift
  let stopCut := state mid (r.set .r3 root) [frame] tape (cutLabel 31)
  have cutBody : NaturalRun program (IntegerLevelCutProgram.steps E adjacency (row d.weights p) p.1 sw label level
      (List.finRange n)+1) (state heap r [frame] tape (cutLabel 0)) [] stopCut := by
    simpa [state,stopCut,mid,IntegerLevelCutProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have cutRet : tickNatural program stopCut = some ⟨state mid rc [] tape 1,[],0⟩ := by
    cases r
    simp [stopCut,rc,state,program,cutLabel,tickNatural,frame,Registers.get,Registers.set]
  obtain ⟨masks,rest,indices,weightContext,si,ti,weights,free,hroot,hrest,hm,hi,hsi,hti,hpoint,hw,hfree⟩ := update
  let r2 := rc.set .r2 root
  let r3 := r2.set .r0 masks
  let r4 := r3.set .r3 rest
  let r5 := r4.set .r1 indices
  let args : Registers ℕ := ⟨masks,indices,root,weightContext⟩
  have moveCut : tickNatural program (state mid rc [] tape 1) = some ⟨state mid r2 [] tape 2,[],0⟩ := by
    cases r
    rfl
  have loadMasks : tickNatural program (state mid r2 [] tape 2) = some ⟨state mid r3 [] tape 3,[],0⟩ := by
    have he := lookup_extend hroot ec
    cases r
    simp [rc,r2,r3,mid,state,program,tickNatural,Registers.get,Registers.set,he]
  have loadRest : tickNatural program (state mid r3 [] tape 3) = some ⟨state mid r4 [] tape 4,[],0⟩ := by
    have he := lookup_extend hroot ec
    cases r
    simp [rc,r2,r3,r4,mid,state,program,tickNatural,Registers.get,Registers.set,he]
  have loadIndices : tickNatural program (state mid r4 [] tape 4) = some ⟨state mid r5 [] tape 5,[],0⟩ := by
    have he := lookup_extend hrest ec
    cases r
    simp [rc,r2,r3,r4,r5,mid,state,program,tickNatural,Registers.get,Registers.set,he]
  have loadWeights : tickNatural program (state mid r5 [] tape 5) = some ⟨state mid args [] tape (updateLabel 0),[],0⟩ := by
    have he := lookup_extend hrest ec
    cases r
    simp [rc,r2,r3,r4,r5,args,mid,state,program,tickNatural,Registers.get,Registers.set,he]
  have indicesRep : ∃ b c, mid[args.b]? = some (.pair b c) ∧
      IndexSpine mid b p.1.val ∧ IndexSpine mid c p.2.val :=
    ⟨si,ti,lookup_extend hi ec,indexSpine_extend hsi ec,indexSpine_extend hti ec⟩
  have weightsRep : ∃ w f, mid[args.d]? = some (.pair w f) ∧ TableAt mid w words ∧ mid[f]? = some (.flag false) :=
    ⟨weights,free,lookup_extend hpoint ec,extend_table hw ec,lookup_extend hfree ec⟩
  obtain ⟨eu,output,rOut,hout,hrep,hupdate⟩ := RoundStateUpdateProgram.natural_trace d p y tape
    (extend_masks hm ec) indicesRep hcut weightsRep hdata (r := args)
  have lift := ReferenceProgramLabels.run updateLabel RoundStateUpdateProgram.program program (fun pc _ => update_slots pc) hupdate
  have updateBody : NaturalRun program (RoundStateUpdateProgram.steps d p y words) (state mid args [] tape (updateLabel 0)) []
      (state (mid++eu) rOut [] tape (updateLabel 5)) := by
    simpa [state,mid,RoundStateUpdateProgram.state,ReferenceProgramLabels.state,List.append_assoc,Nat.add_assoc] using lift
  refine ⟨ec++eu,rOut,?_,?_⟩
  · rw [hout,← List.append_assoc]
    exact hrep
  · have trace := NaturalRun.step call (join cutBody (NaturalRun.step cutRet
      (NaturalRun.step moveCut (NaturalRun.step loadMasks (NaturalRun.step loadRest
        (NaturalRun.step loadIndices (NaturalRun.step loadWeights updateBody)))))))
    unfold steps
    dsimp only [y] at trace
    convert trace using 1 <;> first | rfl | omega | simp only [mid,List.append_assoc]

private theorem at_entry (s : NaturalState 1982) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_round {n H A W B : ℕ} (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (d : Data n) (p : Pair n) (sw : Bits) (hs : value sw=p.1.val)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (level : Bits) (words : List (List Bits)) (hdata : DataRows d.weights words)
    (hW : 1 ≤ W) (hsw : sw.length ≤ W) (labels : ∀ i,(label i).length ≤ W)
    (hrow : ∀ i : Fin n, (row d.weights p)[i.val].bits.length ≤ W) (hj : level.length ≤ W)
    (hwidth : ∀ xs ∈ words, ∀ w ∈ xs, w.length ≤ B)
    (initial : BitState 1982) (bound : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (enum : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a (E.vertices.map label))
    (targets : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.b
      (IntegerLevelCutProgram.fields (row d.weights p) label (List.finRange n)))
    (context : IntegerLevelCutProgram.InputContext (eraseState initial).heap (eraseState initial).registers.c
      (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (encodedRow (row d.weights p)).toList sw (label p.1) level)
    (update : UpdateContext (eraseState initial).heap (eraseState initial).registers.d d p words) :
    ∃ charge out, Run program (steps E adjacency d p sw label level words) charge initial [] out ∧
      RoundStateUpdateProgram.UpdatedAt (eraseState out).heap (eraseState out).registers.d
        (EncodedRoundingState.roundData d p (cut E adjacency d p level)).1 ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=(updateLabel 5) ∧
      (∃ ext, (eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge + (attempt program out).operations ≤ completeBound 1982 H A (instructionBound n W sw.length B) := by
  let old := eraseState initial
  obtain ⟨ext,regs,hrep,hbody⟩ := natural_round E adjacency d p sw hs label hlabel level old.source
    words enum targets context update hdata
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) regs [] old.source (updateLabel 5)
  have trace : NaturalRun program (steps E adjacency d p sw label level words) old [] final := by
    rw [at_entry old hp empty hn]
    exact hbody
  have halt : tickNatural program final = none := by
    simp [final,state,tickNatural,program,updateLabel,RoundStateUpdateProgram.program,ReferenceProgramLabels.instruction]
  obtain ⟨charge,out,hactual,hout,hstop,hcharge,htape⟩ := terminating_simulation bound trace halt
  refine ⟨charge,out,hactual,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout]; exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have hscan := IntegerLevelCutProgram.steps_le E adjacency (row d.weights p) p.1 sw hs label hlabel level hW hsw labels hrow hj
    have hupdate := RoundStateUpdateProgram.steps_le d p (cut E adjacency d p level) words hdata hwidth
    have hsteps : steps E adjacency d p sw label level words ≤ instructionBound n W sw.length B := by
      unfold steps instructionBound
      omega
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.PhysicalSampledRoundProgram
