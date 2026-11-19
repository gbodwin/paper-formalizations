import DirectedFlowCutGap.RoundMaskUpdateProgram
import DirectedFlowCutGap.FlattenDemandMaskProgram

/-!
# The physical update after a sampled cut

Clear the selected demand, union the sampled cut into the old cut,
flatten the updated active flags, and recompute the integer mass of
the surviving demand rows. The program returns both updated masks and
the new mass. The retained weight table is shared.
-/

namespace DirectedFlowCutGap.RoundStateUpdateProgram

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open BinaryArithmetic PackedBooleanConstructor RetainedGridState
open RoundMaskUpdateProgram (MaskPairAt)
open RetainedMassTableProgram (pairOrder TableAt DataRows)

private def maskLabel (pc : Fin 92) : Fin 402 := ⟨18 + pc.val, by omega⟩
private def flattenLabel (pc : Fin 18) : Fin 402 := ⟨110 + pc.val, by omega⟩
private def massLabel (pc : Fin 274) : Fin 402 := ⟨128 + pc.val, by omega⟩

def program : Program 402 := fun pc =>
  if pc.val < 18 then
    match pc.val with
    | 0 => .call 10 1 .r1
    | 1 => .field .r0 .r1 false 2
    | 2 => .call (flattenLabel 0) 3 .r0
    | 3 => .call 14 4 .r0
    | 4 => .make .r3 (.pair .r1 .r0) 5
    | 10 => .field .r3 .r3 true 11
    | 11 => .call (maskLabel 0) 12 .r3
    | 12 => .ret .r3
    | 14 => .field .r2 .r1 true 15
    | 15 => .field .r1 .r3 false 16
    | 16 => .call (massLabel 0) 17 .r3
    | 17 => .ret .r3
    | _ => .halt
  else if pc.val = 24 ∨ pc.val = 118 ∨ pc.val = 151 then .ret .r3
  else if h : pc.val < 110 then
    ReferenceProgramLabels.instruction maskLabel (RoundMaskUpdateProgram.program ⟨pc.val-18,by omega⟩)
  else if h : pc.val < 128 then
    ReferenceProgramLabels.instruction flattenLabel (FlattenDemandMaskProgram.program ⟨pc.val-110,by omega⟩)
  else
    ReferenceProgramLabels.instruction massLabel (RetainedMassTableProgram.program ⟨pc.val-128,by omega⟩)

private theorem mask_slots (pc : Fin 92) (h : RoundMaskUpdateProgram.program pc ≠ .halt) :
    program (maskLabel pc) = ReferenceProgramLabels.instruction maskLabel (RoundMaskUpdateProgram.program pc) := by
  by_cases he : pc.val = 6
  · have eq : pc = 6 := Fin.ext he
    subst pc
    exact (h rfl).elim
  · simp [program,maskLabel,show ¬18+pc.val<18 by omega,show 18+pc.val<110 by omega,
      show 18+pc.val≠24 by omega,show 18+pc.val≠118 by omega,show 18+pc.val≠151 by omega]

private theorem flatten_slots (pc : Fin 18) (h : FlattenDemandMaskProgram.program pc ≠ .halt) :
    program (flattenLabel pc) =
      ReferenceProgramLabels.instruction flattenLabel (FlattenDemandMaskProgram.program pc) := by
  by_cases he : pc.val = 8
  · have eq : pc = 8 := Fin.ext he
    subst pc
    exact (h rfl).elim
  · simp [program,flattenLabel,show ¬110+pc.val<18 by omega,show ¬110+pc.val<110 by omega,
      show 110+pc.val<128 by omega,show 110+pc.val≠24 by omega,show 110+pc.val≠118 by omega,
      show 110+pc.val≠151 by omega]

private theorem mass_slots (pc : Fin 274) (h : RetainedMassTableProgram.program pc ≠ .halt) :
    program (massLabel pc) =
      ReferenceProgramLabels.instruction massLabel (RetainedMassTableProgram.program pc) := by
  by_cases he : pc.val = 23
  · have eq : pc = 23 := Fin.ext he
    subst pc
    exact (h rfl).elim
  · simp [program,massLabel,show ¬128+pc.val<18 by omega,show ¬128+pc.val<110 by omega,
      show ¬128+pc.val<128 by omega,show 128+pc.val≠24 by omega,show 128+pc.val≠118 by omega,
      show 128+pc.val≠151 by omega]

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 402))
    (tape : Bits) (pc : Fin 402) : NaturalState 402 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

private theorem join {a b c : NaturalState 402} {m n : ℕ} {es fs : List Event}
    (h : NaturalRun program m a es b) (hg : NaturalRun program n b fs c) :
    NaturalRun program (m+n) a (es++fs) c := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

def UpdatedAt {n : ℕ} (heap : NaturalHeap) (root : ℕ) (d : Data n) : Prop :=
  ∃ masks mass word, heap[root]? = some (.pair masks mass) ∧
    MaskPairAt heap masks d.remaining d.cut ∧ BoolList heap mass word ∧ value word = d.current

def steps {n : ℕ} (d : Data n) (p : Pair n) (y : Flags n) (words : List (List Bits)) : ℕ :=
  let out := (EncodedRoundingState.roundData d p y).1
  let mask := (pairOrder n).map (flag out.remaining)
  (10*p.1.val + 7*p.2.val + RetainedMaskUnionProgram.steps d.cut.toList + 32) +
    ((6*n+8)*n+3) + (RetainedMassTableProgram.steps out.cut.toList mask words + 1) + 15

def instructionBudget (n B : ℕ) : ℕ :=
  27*n+34 + ((6*n+8)*n+3) + RetainedMassTableProgram.instructionBudget (n*n) n B + 15

private theorem extend_masks {n : ℕ} {heap : NaturalHeap} {root : ℕ} {a : PairFlags n} {x : Flags n}
    (h : MaskPairAt heap root a x) (ext : NaturalHeap) : MaskPairAt (heap++ext) root a x := by
  obtain ⟨r,c,hrecord,⟨refs,hptr,hrows⟩,hcut⟩ := h
  exact ⟨r,c,lookup_extend hrecord ext,
    ⟨refs,BinaryPointerListRead.pointerList_extend hptr ext,hrows.imp (fun _ _ h => boolList_extend h ext)⟩,
    boolList_extend hcut ext⟩

private theorem extend_table {heap : NaturalHeap} {root : ℕ} {rows : List (List Bits)}
    (h : TableAt heap root rows) (ext : NaturalHeap) : TableAt (heap++ext) root rows := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp hw _ ih => exact .cons (lookup_extend hp ext) (PathCostMaterialization.list_extend hw ext) ih

theorem natural_trace {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {words : List (List Bits)}
    (d : Data n) (p : Pair n) (y : Flags n) (tape : Bits)
    (hm : MaskPairAt heap r.a d.remaining d.cut)
    (hi : ∃ b c, heap[r.b]? = some (.pair b c) ∧ IndexSpine heap b p.1.val ∧ IndexSpine heap c p.2.val)
    (hy : BoolList heap r.c y.toList)
    (hw : ∃ w f, heap[r.d]? = some (.pair w f) ∧ TableAt heap w words ∧ heap[f]? = some (.flag false))
    (hdata : DataRows d.weights words) :
    ∃ ext root regs, regs.d = root ∧ UpdatedAt (heap++ext) root (EncodedRoundingState.roundData d p y).1 ∧
      NaturalRun program (steps d p y words) (state heap r [] tape 0) []
        (state (heap++ext) regs [] tape 5) := by
  obtain ⟨weights,free,hcontext,htable,hfalse⟩ := hw
  let maskRegs : Registers ℕ := ⟨r.a,r.b,r.c,free⟩
  let maskOuter : Frame ℕ 402 := ⟨1,.r1,r⟩
  let maskFrame : Frame ℕ 402 := ⟨12,.r3,maskRegs⟩
  let s0 := state heap r [] tape 0
  let s10 := state heap r [maskOuter] tape 10
  let s11 := state heap maskRegs [maskOuter] tape 11
  let maskStart := state heap maskRegs [maskFrame,maskOuter] tape (maskLabel 0)
  have h0 : tickNatural program s0 = some ⟨s10,[],0⟩ := rfl
  have h10 : tickNatural program s10 = some ⟨s11,[],0⟩ := by
    cases r
    simp [s10,s11,maskRegs,state,tickNatural,program,Registers.get,Registers.set,hcontext]
  have h11 : tickNatural program s11 = some ⟨maskStart,[],0⟩ := rfl
  obtain ⟨maskCells,maskRoot,maskOut,_,hroot,hMask,maskTrace⟩ :=
    RoundMaskUpdateProgram.natural_trace (r := maskRegs) p tape hm hi hy hfalse
  let afterMask := heap++maskCells
  let maskStop := state afterMask maskOut [maskFrame,maskOuter] tape (maskLabel 6)
  let s12 := state afterMask ⟨r.a,r.b,r.c,maskRoot⟩ [maskOuter] tape 12
  let s1 := state afterMask ⟨r.a,maskRoot,r.c,r.d⟩ [] tape 1
  have mapped := ReferenceProgramLabels.run maskLabel RoundMaskUpdateProgram.program program mask_slots maskTrace
  have maskRun : NaturalRun program (10*p.1.val + 7*p.2.val + RetainedMaskUnionProgram.steps d.cut.toList + 32)
      maskStart [] maskStop := ReferenceProgramStack.run program [maskFrame,maskOuter] mapped
  have maskRet : tickNatural program maskStop = some ⟨s12,[],0⟩ := by
    simp [maskStop,s12,maskFrame,state,tickNatural,program,maskLabel,Registers.get,Registers.set,hroot,maskRegs]
  have h12 : tickNatural program s12 = some ⟨s1,[],0⟩ := by cases r; rfl
  let newActive := (EncodedRoundingState.erase d.remaining p).1
  let newCut := (EncodedRoundingState.union d.cut y).1
  obtain ⟨demandRoot,cutRoot,hpair,hrows,hcut⟩ := hMask
  let flattenRegs : Registers ℕ := ⟨demandRoot,maskRoot,r.c,r.d⟩
  let s2 := state afterMask flattenRegs [] tape 2
  let flattenFrame : Frame ℕ 402 := ⟨3,.r0,flattenRegs⟩
  let flattenStart := state afterMask flattenRegs [flattenFrame] tape (flattenLabel 0)
  have h1 : tickNatural program s1 = some ⟨s2,[],0⟩ := by
    have kept : afterMask[maskRoot]? = some (.pair demandRoot cutRoot) := hpair
    simp [s1,s2,flattenRegs,state,tickNatural,program,Registers.get,Registers.set,kept]
  have h2 : tickNatural program s2 = some ⟨flattenStart,[],0⟩ := rfl
  obtain ⟨flatCells,flatRoot,_,hflat,flatTrace⟩ :=
    FlattenDemandMaskProgram.natural_trace (r := flattenRegs) hrows tape
  let afterFlat := afterMask++flatCells
  let flattenStop := state afterFlat (flattenRegs.set .r3 flatRoot) [flattenFrame] tape (flattenLabel 8)
  let afterFlatRegs : Registers ℕ := ⟨flatRoot,maskRoot,r.c,r.d⟩
  let s3 := state afterFlat afterFlatRegs [] tape 3
  have mapped := ReferenceProgramLabels.run flattenLabel FlattenDemandMaskProgram.program program flatten_slots flatTrace
  have flatRun : NaturalRun program ((6*n+8)*n+3) flattenStart [] flattenStop :=
    ReferenceProgramStack.run program [flattenFrame] mapped
  have flatRet : tickNatural program flattenStop = some ⟨s3,[],0⟩ := rfl
  let massOuter : Frame ℕ 402 := ⟨4,.r0,afterFlatRegs⟩
  let massRegs : Registers ℕ := ⟨flatRoot,weights,cutRoot,r.d⟩
  let massFrame : Frame ℕ 402 := ⟨17,.r3,massRegs⟩
  let s14 := state afterFlat afterFlatRegs [massOuter] tape 14
  let s15 := state afterFlat ⟨flatRoot,maskRoot,cutRoot,r.d⟩ [massOuter] tape 15
  let s16 := state afterFlat massRegs [massOuter] tape 16
  let massStart := state afterFlat massRegs [massFrame,massOuter] tape (massLabel 0)
  have h3 : tickNatural program s3 = some ⟨s14,[],0⟩ := rfl
  have h14 : tickNatural program s14 = some ⟨s15,[],0⟩ := by
    have kept : afterFlat[maskRoot]? = some (.pair demandRoot cutRoot) := lookup_extend hpair flatCells
    simp [s14,s15,afterFlatRegs,state,tickNatural,program,Registers.get,Registers.set,kept]
  have h15 : tickNatural program s15 = some ⟨s16,[],0⟩ := by
    have kept : afterFlat[r.d]? = some (.pair weights free) := lookup_extend (lookup_extend hcontext maskCells) flatCells
    simp [s15,s16,massRegs,state,tickNatural,program,Registers.get,Registers.set,kept]
  have h16 : tickNatural program s16 = some ⟨massStart,[],0⟩ := rfl
  let flags := (pairOrder n).map (flag newActive)
  have halign : ∀ x ∈ words, x.length = newCut.toList.length := by
    simpa using RetainedMassTableProgram.data_aligned hdata
  have hlen : flags.length = words.length := by
    simp [flags, RetainedMassTableProgram.pairOrder_length, RetainedMassTableProgram.data_length hdata]
  obtain ⟨massCells,massRoot,hMass,massTrace⟩ := RetainedMassTableProgram.natural_trace (r := massRegs)
    hflat (extend_table (extend_table htable maskCells) flatCells) (boolList_extend hcut flatCells)
    hlen halign tape
  let afterMass := afterFlat++massCells
  let massStop := state afterMass (massRegs.set .r3 massRoot) [massFrame,massOuter] tape (massLabel 23)
  let s17 := state afterMass ⟨flatRoot,weights,cutRoot,massRoot⟩ [massOuter] tape 17
  let s4 := state afterMass ⟨massRoot,maskRoot,r.c,r.d⟩ [] tape 4
  let massSteps := RetainedMassTableProgram.steps newCut.toList flags words + 1
  have mapped := ReferenceProgramLabels.run massLabel RetainedMassTableProgram.program program mass_slots massTrace
  have massRun : NaturalRun program massSteps massStart [] massStop :=
    ReferenceProgramStack.run program [massFrame,massOuter] mapped
  have massRet : tickNatural program massStop = some ⟨s17,[],0⟩ := rfl
  have h17 : tickNatural program s17 = some ⟨s4,[],0⟩ := rfl
  let cell : Cell ℕ := .pair maskRoot massRoot
  let root := afterMass.length
  let finalHeap := afterMass++[cell]
  let outRegs : Registers ℕ := ⟨massRoot,maskRoot,r.c,root⟩
  let s5 := state finalHeap outRegs [] tape 5
  have h4 : tickNatural program s4 = some ⟨s5,[],0⟩ := by
    simp [s4,s5,cell,root,finalHeap,outRegs,state,tickNatural,program,Registers.get,Registers.set,
      Recipe.cell,allocateNatural]
  have hrecord : finalHeap[root]? = some (.pair maskRoot massRoot) := by simp [finalHeap,root,cell]
  have hmask' : MaskPairAt finalHeap maskRoot newActive newCut :=
    extend_masks (extend_masks (extend_masks ⟨demandRoot,cutRoot,hpair,hrows,hcut⟩ flatCells) massCells) [cell]
  have hresult : UpdatedAt finalHeap root (EncodedRoundingState.roundData d p y).1 :=
    ⟨maskRoot,massRoot,RetainedMassTableProgram.sum newCut.toList flags words,hrecord,hmask',
      boolList_extend hMass [cell],RetainedMassTableProgram.mass_value d.weights newActive newCut hdata⟩
  have massSuffix := join massRun (.step massRet (.step h17 (.step h4 (.done s5))))
  have massPrefix := NaturalRun.step h3 (.step h14 (.step h15 (.step h16 massSuffix)))
  have flattenSuffix := join flatRun (.step flatRet massPrefix)
  have flattenPrefix := NaturalRun.step h1 (.step h2 flattenSuffix)
  have maskSuffix := join maskRun (.step maskRet (.step h12 flattenPrefix))
  have full := NaturalRun.step h0 (.step h10 (.step h11 maskSuffix))
  let count := (10*p.1.val + 7*p.2.val + RetainedMaskUnionProgram.steps d.cut.toList + 32) +
    (((6*n+8)*n+3)+(massSteps+(0+1+1+1)+1+1+1+1+1)+1+1+1+1)+1+1+1
  change NaturalRun program count s0 [] s5 at full
  have he : count = steps d p y words := by
    dsimp only [count,steps,massSteps,flags,newActive,newCut,EncodedRoundingState.roundData]
    omega
  rw [he] at full
  let ext := maskCells++flatCells++massCells++[cell]
  refine ⟨ext,root,outRegs,rfl,?_,?_⟩
  · simpa only [ext,finalHeap,afterMass,afterFlat,afterMask,List.append_assoc] using hresult
  · simpa only [s0,s5,ext,finalHeap,afterMass,afterFlat,afterMask,List.append_assoc] using full

theorem steps_le {n B : ℕ} (d : Data n) (p : Pair n) (y : Flags n) (words : List (List Bits))
    (hdata : DataRows d.weights words) (hwidth : ∀ xs ∈ words, ∀ w ∈ xs, w.length ≤ B) :
    steps d p y words ≤ instructionBudget n B := by
  let result := (EncodedRoundingState.roundData d p y).1
  let cut := result.cut.toList
  let mask := (pairOrder n).map (flag result.remaining)
  have halign : ∀ x ∈ words, x.length = cut.length := by simpa [cut] using RetainedMassTableProgram.data_aligned hdata
  have hl := RetainedMassTableProgram.data_length hdata
  have hmass : RetainedMassTableProgram.steps cut mask words + 1 ≤ RetainedMassTableProgram.instructionBudget (n*n) n B := by
    simpa only [hl,cut,Vector.length_toList] using RetainedMassTableProgram.steps_le words mask cut B halign hwidth
  have hm := RetainedMaskUnionProgram.steps_le d.cut.toList
  simp only [Vector.length_toList] at hm
  have hi := p.1.isLt
  have hj := p.2.isLt
  change _ + _ + (RetainedMassTableProgram.steps cut mask words+1) + 15 ≤ _
  unfold instructionBudget
  omega

private theorem at_entry (s : NaturalState 402) (hp : s.pc=0) (hc : s.stack=[])
    (hd : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

private theorem charge_mono (C H A : ℕ) {k l : ℕ} (h : k ≤ l) :
    completeBound C H A k ≤ completeBound C H A l := by
  unfold completeBound runBound stepBound
  gcongr

theorem update_round_state {n H A B : ℕ} {initial : BitState 402} (d : Data n) (p : Pair n) (y : Flags n)
    (words : List (List Bits)) (hdata : DataRows d.weights words)
    (hwidth : ∀ xs ∈ words, ∀ w ∈ xs, w.length ≤ B)
    (hs : initial.Bounded H A) (hp : initial.pc = 0) (hc : initial.stack = [])
    (hd : (eraseState initial).next=(eraseState initial).heap.length)
    (hm : MaskPairAt (eraseState initial).heap (eraseState initial).registers.a d.remaining d.cut)
    (hi : ∃ b c, (eraseState initial).heap[(eraseState initial).registers.b]? = some (.pair b c) ∧
      IndexSpine (eraseState initial).heap b p.1.val ∧ IndexSpine (eraseState initial).heap c p.2.val)
    (hy : BoolList (eraseState initial).heap (eraseState initial).registers.c y.toList)
    (hw : ∃ w f, (eraseState initial).heap[(eraseState initial).registers.d]? = some (.pair w f) ∧
      TableAt (eraseState initial).heap w words ∧ (eraseState initial).heap[f]? = some (.flag false)) :
    ∃ q out, Run program (steps d p y words) q initial [] out ∧ (attempt program out).result = none ∧
      (eraseState out).pc=5 ∧ (eraseState out).stack=[] ∧ out.source=initial.source ∧
      UpdatedAt (eraseState out).heap (eraseState out).registers.d (EncodedRoundingState.roundData d p y).1 ∧
      (∃ ext, (eraseState out).heap=(eraseState initial).heap ++ ext) ∧
      q + (attempt program out).operations ≤ completeBound 402 H A (instructionBudget n B) := by
  let input := eraseState initial
  obtain ⟨ext,root,regs,hroot,hresult,htrace⟩ := natural_trace d p y input.source hm hi hy hw hdata
  let final := state (input.heap++ext) regs [] input.source 5
  have hnil : input.stack = [] := by simp [input,eraseState,State.map,hc]
  have he := at_entry input hp hnil hd
  have hrun : NaturalRun program (steps d p y words) input [] final := by
    rw [he]
    exact htrace
  have halt : tickNatural program final = none := rfl
  obtain ⟨q,out,hactual,hout,hstop,hpaid,htape⟩ := terminating_simulation hs hrun halt
  refine ⟨q,out,hactual,hstop,?_,?_,htape,?_,⟨ext,?_⟩,hpaid.trans ?_⟩
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]
    change UpdatedAt (input.heap++ext) regs.d (EncodedRoundingState.roundData d p y).1
    rwa [hroot]
  · rw [hout]; rfl
  · exact charge_mono _ _ _ (steps_le d p y words hdata hwidth)

end DirectedFlowCutGap.RoundStateUpdateProgram
