import DirectedFlowCutGap.EpochGridLookupProgram
import DirectedFlowCutGap.RoundWordTablesProgram

/-! Fetch the selected demand's row by computing its row-major address. -/

namespace DirectedFlowCutGap.RoundWeightRowProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open ConcreteExpressionProgram (append_run)
open EpochActiveFromMaskProgram (labelPair)
open GraphWalkExtension (Edge)
open RetainedMassTableProgram (TableAt DataRows pairOrder)
open PathCostMaterialization (WordList)
open BinaryPointerListRead (PointerList pointerList_extend)

def product {n : ℕ} (p : Pair n) : Bits := CanonicalArithmeticProgram.result true p.1.val.bits n.bits
def address {n : ℕ} (p : Pair n) : Bits := CanonicalArithmeticProgram.result false p.2.val.bits (product p)

theorem product_value {n : ℕ} (p : Pair n) : value (product p)=n*p.1.val := by
  simp [product,CanonicalArithmeticProgram.result_exact,(canonical_values _ _).2,value_bits,Nat.mul_comm]

theorem address_value {n : ℕ} (p : Pair n) : value (address p)=(finProdFinEquiv p).val := by
  simp [address,CanonicalArithmeticProgram.result_exact,(canonical_values _ _).1,product_value,value_bits,finProdFinEquiv]

def selected {n : ℕ} (p : Pair n) (rows : List (List Bits)) : List Bits :=
  rows[(finProdFinEquiv p).val]?.getD []

theorem selected_mem {n : ℕ} {d : Family n} {words : List (List Bits)}
    (stored : DataRows d words) (p : Pair n) : selected p words∈words := by
  have len : words.length=n*n := stored.length_eq.trans (RetainedMassTableProgram.pairOrder_length n)
  have index : (finProdFinEquiv p).val<words.length := len.symm ▸ (finProdFinEquiv p).isLt
  simpa only [selected,List.getElem?_eq_getElem index,Option.getD_some] using
    (List.getElem_mem index : words[(finProdFinEquiv p).val]∈words)

theorem selected_values {n : ℕ} {d : Family n} {words : List (List Bits)}
    (stored : DataRows d words) (p : Pair n) : (selected p words).map value=(row d p).toList := by
  let i := finProdFinEquiv p
  have hi : i.val<(pairOrder n).length := by rw [RetainedMassTableProgram.pairOrder_length]; exact i.isLt
  have iw : i.val<words.length := stored.length_eq.symm ▸ hi
  have key : (pairOrder n)[i.val]?=some p := by
    rw [ActiveDemandListProgram.all_pairs,RetainedTapeInput.allPairs]
    rw [List.getElem?_ofFn,dite_eq_left i.isLt]
    change some (finProdFinEquiv.symm (finProdFinEquiv p))=some p
    rw [Equiv.symm_apply_apply]
  rw [List.getElem?_eq_getElem hi] at key
  have values := stored.get iw hi
  change (words[i.val].map value)=(row d ((pairOrder n)[i.val])).toList at values
  rw [Option.some.inj key] at values
  change (words[i.val]?.getD []).map value=(row d p).toList
  rw [List.getElem?_eq_getElem iw,Option.getD_some]
  exact values

private theorem pointers {heap : NaturalHeap} {root : ℕ} {rows : List (List Bits)} (data : TableAt heap root rows) :
    ∃ refs,PointerList heap root refs ∧ List.Forall₂ (WordList heap) refs rows := by
  induction data with
  | nil read => exact ⟨[],.nil read,.nil⟩
  | cons read words _ ih =>
    obtain ⟨refs,spine,each⟩ := ih
    exact ⟨_::refs,.cons read spine,.cons words each⟩

def arithmeticLabel (pc : Fin 116) : Fin 175 := ⟨32+pc.val,by omega⟩
def readLabel (pc : Fin 27) : Fin 175 := ⟨148+pc.val,by omega⟩

def program : Program 175 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .call 24 9 .r3
    | 9 => .call 28 10 .r3
    | 10 => .move .r0 .r3 11
    | 11 => .move .r1 .r2 12
    | 12 => .call (readLabel 24) (readLabel 26) .r3
    | 24 => .field .r0 .r0 false 25
    | 25 => .call (arithmeticLabel 94) (arithmeticLabel 115) .r3
    | 28 => .field .r0 .r0 true 29
    | 29 => .move .r1 .r3 30
    | 30 => .call (arithmeticLabel 111) (arithmeticLabel 115) .r3
    | _ => .halt
  else if h : pc.val<148 then
    if pc.val=147 then .ret .r3
    else ReferenceProgramLabels.instruction arithmeticLabel (CanonicalArithmeticProgram.program ⟨pc.val-32,by omega⟩)
  else if pc.val=174 then .ret .r3
  else ReferenceProgramLabels.instruction readLabel
    (BinaryPointerListRead.program ⟨pc.val-148,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 175))
    (tape : Bits) (pc : Fin 175) : NaturalState 175 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps {n : ℕ} (p : Pair n) : ℕ :=
  CanonicalArithmeticProgram.instructions true p.1.val.bits n.bits+
    CanonicalArithmeticProgram.instructions false p.2.val.bits (product p)+
    BinaryPointerListRead.steps (address p)+12

def instructionBound (n : ℕ) : ℕ :=
  200*(2*n.size+2)^2+200*(n.size+(n*n).size+2)^2+6*(n*n)+10*(n*n).size+21

theorem steps_le {n : ℕ} (p : Pair n) : steps p ≤ instructionBound n := by
  have size (i : Fin n) : i.val.bits.length≤n.size := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size i.isLt.le
  have productWidth : (product p).length≤(n*n).size := by
    change (trim (CanonicalArithmeticProgram.raw true p.1.val.bits n.bits)).1.length≤_
    rw [trim_length,← (trim_spec _).2.1,show (trim (CanonicalArithmeticProgram.raw true p.1.val.bits n.bits)).1=product p from rfl,product_value]
    exact Nat.size_le_size (Nat.mul_le_mul_left n p.1.isLt.le)
  have addrWidth : (address p).length≤(n*n).size := by
    change (trim (CanonicalArithmeticProgram.raw false p.2.val.bits (product p))).1.length≤_
    rw [trim_length,← (trim_spec _).2.1,show (trim (CanonicalArithmeticProgram.raw false p.2.val.bits (product p))).1=address p from rfl,address_value]
    exact Nat.size_le_size (finProdFinEquiv p).isLt.le
  have mul := (CanonicalArithmeticProgram.instructions_bound true p.1.val.bits n.bits).trans
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (show p.1.val.bits.length+n.bits.length+2≤2*n.size+2 by
      have hn : n.bits.length=n.size := Nat.size_eq_bits_len n
      have := size p.1
      omega) 2))
  have add := (CanonicalArithmeticProgram.instructions_bound false p.2.val.bits (product p)).trans
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (show p.2.val.bits.length+(product p).length+2≤n.size+(n*n).size+2 by
      have := size p.2; omega) 2))
  have read := BinaryPointerListRead.steps_bound (address p)
  rw [address_value] at read
  have index := (finProdFinEquiv p).isLt
  unfold steps instructionBound
  omega

private theorem arithmetic_slots (pc : Fin 116) (h : CanonicalArithmeticProgram.program pc≠.halt) :
    program (arithmeticLabel pc)=ReferenceProgramLabels.instruction arithmeticLabel (CanonicalArithmeticProgram.program pc) := by
  by_cases stop : pc.val=115
  · have eq : pc=115 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,arithmeticLabel,show ¬32+pc.val<32 by omega,show 32+pc.val<148 by omega,show 32+pc.val≠147 by omega]

private theorem read_slots (pc : Fin 27) (h : BinaryPointerListRead.program pc≠.halt) :
    program (readLabel pc)=ReferenceProgramLabels.instruction readLabel (BinaryPointerListRead.program pc) := by
  by_cases stop : pc.val=26
  · have eq : pc=26 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,readLabel,show ¬148+pc.val<32 by omega,show ¬148+pc.val<148 by omega,show 148+pc.val≠174 by omega]

private theorem arithmetic_body {heap : NaturalHeap} {r : Registers ℕ} {u v : Bits}
    (mul : Bool) (left : BoolList heap r.a u) (right : BoolList heap r.b v)
    (stack : List (Frame ℕ 175)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (CanonicalArithmeticProgram.result mul u v) ∧
      NaturalRun program (CanonicalArithmeticProgram.rawSteps mul u v+
        BinaryTrimProgram.steps (CanonicalArithmeticProgram.raw mul u v)+3)
        (state heap r (⟨arithmeticLabel 115,.r3,r⟩::stack) tape (arithmeticLabel (CanonicalArithmeticProgram.entry mul))) []
        (state (heap++ext) (r.set .r3 root) stack tape (arithmeticLabel 115)) := by
  obtain ⟨ext,root,_,body,rep⟩ := CanonicalArithmeticProgram.canonical_return mul left right heap.length r.c r.d
    rfl r 115 [] tape
  have lift := ReferenceProgramLabels.run arithmeticLabel CanonicalArithmeticProgram.program program arithmetic_slots body
  have lift := ReferenceProgramStack.run program stack lift
  refine ⟨ext,root,rep,?_⟩
  cases r
  simpa [state,CanonicalArithmeticProgram.state,ReferenceProgramLabels.state,ReferenceProgramLabels.frame,
    ReferenceProgramStack.state,Registers.set] using lift

set_option maxHeartbeats 2100000 in
theorem natural_row {n : ℕ} {p : Pair n} {heap : NaturalHeap} {r : Registers ℕ}
    {d : Family n} {rows : List (List Bits)} (key : Edge heap r.a (labelPair p))
    (count : BoolList heap r.b n.bits) (weights : TableAt heap r.c rows)
    (data : DataRows d rows) (tape : Bits) :
    ∃ ext root,WordList (heap++ext) root (selected p rows) ∧
      NaturalRun program (steps p) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  obtain ⟨u,v,pair,sourceBits,targetBits⟩ := key
  obtain ⟨refs,table,each⟩ := pointers weights
  let outer : Frame ℕ 175 := ⟨1,.r3,r⟩
  let mulCaller : Frame ℕ 175 := ⟨9,.r3,r⟩
  let mulArgs := r.set .r0 u
  let mulInner : Frame ℕ 175 := ⟨arithmeticLabel 115,.r3,mulArgs⟩
  have mulEnter : NaturalRun program 4 (state heap r [] tape 0) []
      (state heap mulArgs [mulInner,mulCaller,outer] tape (arithmeticLabel 94)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,pair,
      outer,mulCaller,mulArgs,mulInner]
  obtain ⟨em,mulRoot,mulRep,mulBody⟩ := arithmetic_body (r:=mulArgs) true sourceBits count [mulCaller,outer] tape
  let mid := heap++em
  let mulOut := r.set .r3 mulRoot
  let mulStop := state mid (mulArgs.set .r3 mulRoot) [mulCaller,outer] tape (arithmeticLabel 115)
  have mulRet : tickNatural program mulStop=some ⟨state mid mulOut [outer] tape 9,[],0⟩ := by
    simp [mulStop,program,arithmeticLabel,state,tickNatural,Registers.get,Registers.set,mulCaller,mulOut]
  let addCaller : Frame ℕ 175 := ⟨10,.r3,mulOut⟩
  let addArgs := (mulOut.set .r0 v).set .r1 mulRoot
  let addInner : Frame ℕ 175 := ⟨arithmeticLabel 115,.r3,addArgs⟩
  have pairAt : mid[r.a]?=some (.pair u v) := lookup_extend pair em
  have addEnter : NaturalRun program 4 (state mid mulOut [outer] tape 9) []
      (state mid addArgs [addInner,addCaller,outer] tape (arithmeticLabel 111)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,pairAt,
      mulOut,addCaller,addArgs,addInner]
  obtain ⟨ea,addr,addrRep,addBody⟩ := arithmetic_body (r:=addArgs) false
    (boolList_extend targetBits em) mulRep [addCaller,outer] tape
  let grown := mid++ea
  let addOut := mulOut.set .r3 addr
  let addStop := state grown (addArgs.set .r3 addr) [addCaller,outer] tape (arithmeticLabel 115)
  have addRet : tickNatural program addStop=some ⟨state grown addOut [outer] tape 10,[],0⟩ := by
    simp [addStop,program,arithmeticLabel,state,tickNatural,Registers.get,Registers.set,addCaller,addOut]
  let readArgs := (addOut.set .r0 addr).set .r1 r.c
  let readFrame : Frame ℕ 175 := ⟨readLabel 26,.r3,readArgs⟩
  have readEnter : NaturalRun program 3 (state grown addOut [outer] tape 10) []
      (state grown readArgs [readFrame,outer] tape (readLabel 24)) := by
    apply ReferenceProgramSteps.sound
    cases r
    rfl
  let i := value (address p)
  have rowLength : rows.length=n*n := data.length_eq.trans (RetainedMassTableProgram.pairOrder_length n)
  have rowIndex : i<rows.length := by
    rw [rowLength,show i=(finProdFinEquiv p).val from address_value p]
    exact (finProdFinEquiv p).isLt
  have pointerIndex : i<refs.length := each.length_eq.symm ▸ rowIndex
  obtain ⟨er,_,readCore⟩ := BinaryPointerListRead.read_return (word:=address p) (a:=readArgs.a) (b:=readArgs.b)
    addrRep (pointerList_extend (pointerList_extend table em) ea) pointerIndex grown.length readArgs.c readArgs.d
    rfl readArgs 26 [] tape
  let result := refs[i]
  let readStop := state (grown++er) (readArgs.set .r3 result) [outer] tape (readLabel 26)
  have lift := ReferenceProgramLabels.run readLabel BinaryPointerListRead.program program read_slots readCore
  have lift := ReferenceProgramStack.run program [outer] lift
  have readBody : NaturalRun program (BinaryPointerListRead.steps (address p))
      (state grown readArgs [readFrame,outer] tape (readLabel 24)) [] readStop := by
    cases r
    simpa [state,readStop,readFrame,BinaryPointerListRead.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,Registers.set,readArgs,addOut,mulOut,
      mid,grown,result,i,Nat.add_assoc] using lift
  have readRet : tickNatural program readStop=some ⟨state (grown++er) (r.set .r3 result) [] tape 1,[],0⟩ := by
    simp [readStop,program,readLabel,state,tickNatural,Registers.get,Registers.set,outer]
  have rowRep : WordList heap result (selected p rows) := by
    have read := each.get pointerIndex rowIndex
    change WordList heap result rows[i] at read
    have index : i=(finProdFinEquiv p).val := address_value p
    simpa only [selected,← index,List.getElem?_eq_getElem rowIndex,Option.getD_some] using read
  refine ⟨em++ea++er,result,PathCostMaterialization.list_extend rowRep _,?_⟩
  let m := CanonicalArithmeticProgram.rawSteps true p.1.val.bits n.bits+
    BinaryTrimProgram.steps (CanonicalArithmeticProgram.raw true p.1.val.bits n.bits)+3
  let a := CanonicalArithmeticProgram.rawSteps false p.2.val.bits (product p)+
    BinaryTrimProgram.steps (CanonicalArithmeticProgram.raw false p.2.val.bits (product p))+3
  let k := BinaryPointerListRead.steps (address p)
  have total : 4+(m+(4+(a+(3+(k+1))+1))+1)=steps p := by
    simp only [m,a,k,steps,CanonicalArithmeticProgram.instructions]
    omega
  rw [← total]
  have full := append_run mulEnter (append_run mulBody (.step mulRet
    (append_run addEnter (append_run addBody (.step addRet
      (append_run readEnter (append_run readBody (.step readRet (.done _)))))))))
  simpa only [mid,grown,List.append_assoc,List.nil_append,labelPair,product,m,a,k,Nat.zero_add,Nat.add_assoc] using full

end DirectedFlowCutGap.RoundWeightRowProgram
