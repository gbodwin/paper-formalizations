import DirectedFlowCutGap.ObjectiveProductListBounds

/-! Both original rows feed the actual product-list constructor, then its
fresh root is handed directly to the actual canonical sum. -/
namespace DirectedFlowCutGap.ObjectiveRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def productLabel (pc : Fin 150) : Fin 312 := ⟨pc.val,by omega⟩
def sumLabel (pc : Fin 158) : Fin 312 := ⟨pc.val+150,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 312) : Instruction C → Instruction 312
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 312) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 312 := fun pc =>
  if h : pc.val<150 then callable productLabel (ObjectiveProductList.program ⟨pc.val,h⟩)
  else if h : pc.val<308 then
    callable sumLabel (CanonicalRationalSum.program ⟨pc.val-150,by omega⟩)
  else match pc.val with
  | 308 => .call 148 309 .r3
  | 309 => .move .r0 .r3 310
  | 310 => .call 306 311 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 312)) (source : Bits) (pc : Fin 312) : NaturalState 312 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem product_slots (pc : Fin 150) (h : ObjectiveProductList.program pc≠.halt) :
    program (productLabel pc)=ReferenceProgramLabels.instruction productLabel (ObjectiveProductList.program pc) := by
  simpa [program,productLabel,pc.isLt] using callable_eq productLabel (ObjectiveProductList.program pc) h

theorem sum_slots (pc : Fin 158) (h : CanonicalRationalSum.program pc≠.halt) :
    program (sumLabel pc)=ReferenceProgramLabels.instruction sumLabel (CanonicalRationalSum.program pc) := by
  simpa [program,sumLabel,show ¬pc.val+150<150 by omega,show pc.val+150<308 by omega] using
    callable_eq sumLabel (CanonicalRationalSum.program pc) h

theorem run_append {s u v : NaturalState 312} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem products_return {xs ys : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (left : StoredList heap a xs) (right : StoredList heap b ys) (aligned : xs.length=ys.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 312)
    (stack : List (Frame ℕ 312)) (source : Bits) :
    ∃ ext root,ext.length=ObjectiveProductList.cells xs ys ∧
      NaturalRun program (ObjectiveProductList.steps xs ys+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 148) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (ObjectiveProductList.products xs ys) := by
  obtain ⟨ext,root,len,core,rep⟩ := ObjectiveProductList.products_high
    (ObjectiveProductList.state heap next a b c d [] source 148) rfl hn left right aligned rfl
  have lift := ReferenceProgramLabels.run productLabel ObjectiveProductList.program program product_slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+ObjectiveProductList.steps xs ys)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 148) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 149) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      ObjectiveProductList.state,productLabel,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 149)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,ObjectiveProductList.program,callable,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append body (.step ret (.done _)) using 1 <;> simp
  omega

theorem sum_return {xs : List Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : StoredList heap a xs) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 312) (stack : List (Frame ℕ 312)) (source : Bits) :
    ∃ ext root,ext.length=CanonicalRationalSum.cells xs ∧
      NaturalRun program (CanonicalRationalSum.steps xs+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 306) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryFractionalRows.sum xs).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalRationalSum.sum_high
    (CanonicalRationalSum.state heap next a b c d [] source 156) rfl hn input rfl
  have lift := ReferenceProgramLabels.run sumLabel CanonicalRationalSum.program program sum_slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+CanonicalRationalSum.steps xs)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 306) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 307) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalRationalSum.state,sumLabel,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 307)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,CanonicalRationalSum.program,callable,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append body (.step ret (.done _)) using 1 <;> simp
  omega
end DirectedFlowCutGap.ObjectiveRow
