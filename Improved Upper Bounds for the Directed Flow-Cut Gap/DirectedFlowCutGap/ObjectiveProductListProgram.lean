import DirectedFlowCutGap.ActualRationalProduct
import DirectedFlowCutGap.CanonicalRationalSum

/-! A concrete aligned scan of the two original rational rows. Product records
are computed by the canonical multiplication table and consed into a new list;
no list of precomputed products is supplied. -/
namespace DirectedFlowCutGap.ObjectiveProductList
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def label (pc : Fin 132) : Fin 150 := ⟨pc.val,by omega⟩
def program : Program 150 := fun pc =>
  if pc.val=131 then .ret .r3
  else if h : pc.val<132 then
    ReferenceProgramLabels.instruction label (CanonicalRationalProduct.program ⟨pc.val,h⟩)
  else match pc.val with
  | 132 => .branch .r0 133 149 149 135
  | 133 => .make .r3 .nil 134
  | 134 => .ret .r3
  | 135 => .make .r2 (.pair .r0 .r1) 136
  | 136 => .field .r0 .r0 true 137
  | 137 => .field .r1 .r1 true 138
  | 138 => .call 132 139 .r3
  | 139 => .field .r0 .r2 false 140
  | 140 => .field .r1 .r2 true 141
  | 141 => .field .r0 .r0 false 142
  | 142 => .field .r1 .r1 false 143
  | 143 => .move .r2 .r3 144
  | 144 => .call 130 145 .r3
  | 145 => .make .r3 (.pair .r3 .r2) 146
  | 146 => .ret .r3
  | 148 => .call 132 149 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 150)) (source : Bits) (pc : Fin 150) : NaturalState 150 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def products (xs ys : List Fraction) : List Fraction :=
  List.zipWith (fun x y => (BinaryRational.mul x y).1) xs ys

def steps : List Fraction → List Fraction → ℕ
  | x::xs,y::ys => steps xs ys+CanonicalRationalProduct.instructions x y+15
  | _,_ => 3

def cells : List Fraction → List Fraction → ℕ
  | x::xs,y::ys => cells xs ys+CanonicalRationalProduct.cells x y+2
  | _,_ => 1

theorem slots (pc : Fin 132) (h : CanonicalRationalProduct.program pc ≠ .halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (CanonicalRationalProduct.program pc) := by
  by_cases hp : pc.val=131
  · have he : pc=131 := Fin.ext hp
    subst pc;simp [CanonicalRationalProduct.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append {s u v : NaturalState 150} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem product_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 150)
    (stack : List (Frame ℕ 150)) (source : Bits) :
    ∃ ext root, ext.length=CanonicalRationalProduct.cells x y ∧
      NaturalRun program (CanonicalRationalProduct.instructions x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 130) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.mul x y).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalRationalProduct.product_high x y
    (CanonicalRationalProduct.state heap next a b c d [] source 130) rfl hn left right rfl
  have lift := ReferenceProgramLabels.run label CanonicalRationalProduct.program program slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+CanonicalRationalProduct.instructions x y)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 130) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 131) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalRationalProduct.state,label,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 131)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append body (.step ret (.done _)) using 1 <;> simp
  omega
end DirectedFlowCutGap.ObjectiveProductList
