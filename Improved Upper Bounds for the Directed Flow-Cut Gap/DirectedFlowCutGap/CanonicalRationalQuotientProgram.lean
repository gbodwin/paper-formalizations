import DirectedFlowCutGap.ActualRationalProduct
import DirectedFlowCutGap.BinaryZeroProgram

/-! Literal padded zero test and reciprocal-record construction, followed by
the actual two-product table. No integer division or GCD instruction is used. -/
namespace DirectedFlowCutGap.CanonicalRationalQuotient
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def productLabel (pc : Fin 132) : Fin 164 := ⟨pc.val,by omega⟩
def zeroLabel (pc : Fin 9) : Fin 164 := ⟨pc.val+132,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 164) : Instruction C → Instruction 164
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 164) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 164 := fun pc =>
  if h : pc.val<132 then callable productLabel (CanonicalRationalProduct.program ⟨pc.val,h⟩)
  else if h : pc.val<141 then callable zeroLabel (BinaryZeroProgram.program ⟨pc.val-132,by omega⟩)
  else match pc.val with
  | 144 => .make .r2 (.pair .r0 .r1) 145
  | 145 => .field .r0 .r1 false 146
  | 146 => .call 139 147 .r3
  | 147 => .branch .r3 163 153 148 163
  | 148 => .make .r3 .nil 149
  | 149 => .make .r1 (.flag true) 150
  | 150 => .make .r1 (.pair .r1 .r3) 151
  | 151 => .make .r3 (.pair .r3 .r1) 152
  | 152 => .ret .r3
  | 153 => .field .r0 .r2 false 154
  | 154 => .field .r1 .r2 true 155
  | 155 => .field .r2 .r1 false 156
  | 156 => .field .r1 .r1 true 157
  | 157 => .make .r1 (.pair .r1 .r2) 158
  | 158 => .call 130 159 .r3
  | 159 => .ret .r3
  | 161 => .call 144 162 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 164)) (source : Bits) (pc : Fin 164) : NaturalState 164 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def crossSteps (x y : Fraction) : ℕ :=
  CanonicalArithmeticProgram.instructions true x.num y.den+
  CanonicalArithmeticProgram.instructions true x.den y.num+16

def crossCells (x y : Fraction) : ℕ :=
  CanonicalRationalProduct.arithmeticCells true x.num y.den+
  CanonicalRationalProduct.arithmeticCells true x.den y.num+3

def steps (x y : Fraction) : ℕ :=
  BinaryZeroProgram.steps y.num+(if (BinaryArithmetic.isZero y.num).1 then 11 else crossSteps x y+15)

def cells (x y : Fraction) : ℕ :=
  if (BinaryArithmetic.isZero y.num).1 then 6 else crossCells x y+3

def reciprocal (y : Fraction) (h : (BinaryArithmetic.isZero y.num).1=false) : Fraction :=
  ⟨y.den,y.num,Nat.pos_of_ne_zero (fun hz => by
    have := (BinaryArithmetic.isZero_spec y.num).1.mpr hz
    simp [h] at this)⟩

theorem nonzero_exact (x y : Fraction) (h : (BinaryArithmetic.isZero y.num).1=false) :
    (BinaryRational.mul x (reciprocal y h)).1=(BinaryRational.div x y).1 := by
  simp [BinaryRational.div,h,BinaryRational.mul,reciprocal]

theorem product_slots (pc : Fin 132) (h : CanonicalRationalProduct.program pc≠.halt) :
    program (productLabel pc)=ReferenceProgramLabels.instruction productLabel (CanonicalRationalProduct.program pc) := by
  simpa [program,productLabel,pc.isLt] using callable_eq productLabel (CanonicalRationalProduct.program pc) h

theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  simpa [program,zeroLabel,show ¬pc.val+132<132 by omega,show pc.val+132<141 by omega] using
    callable_eq zeroLabel (BinaryZeroProgram.program pc) h

theorem run_append {s u v : NaturalState 164} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem product_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 164)
    (stack : List (Frame ℕ 164)) (source : Bits) :
    ∃ ext root, ext.length=CanonicalRationalProduct.cells x y ∧
      NaturalRun program (CanonicalRationalProduct.instructions x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 130) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.mul x y).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalRationalProduct.product_high x y
    (CanonicalRationalProduct.state heap next a b c d [] source 130) rfl hn left right rfl
  have lift := ReferenceProgramLabels.run productLabel CanonicalRationalProduct.program program product_slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+CanonicalRationalProduct.instructions x y)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 130) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 131) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalRationalProduct.state,productLabel,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 131)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,CanonicalRationalProduct.program,callable,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append body (.step ret (.done _)) using 1 <;> simp
  omega

theorem zero_return {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 164) (stack : List (Frame ℕ 164)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps word+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 139) []
      (state (heap++[.flag (isZero word).1]) (next+1)
        saved.a saved.b saved.c next stack source pc) := by
  have z0 := BinaryZeroProgram.zero_return input next b c d hn ⟨a,b,c,d⟩ 8 [] source
  have z1 := ReferenceProgramLabels.run zeroLabel BinaryZeroProgram.program program zero_slots z0
  have z2 := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) z1
  have z : NaturalRun program (BinaryZeroProgram.steps word)
      (state heap next a b c d (⟨140,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 132) []
      (state (heap++[.flag (isZero word).1]) (next+1) a b c next
        (⟨pc,.r3,saved⟩::stack) source 140) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryZeroProgram.state,zeroLabel,state] using z2
  have t39 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 139)=
      some ⟨state heap next a b c d (⟨140,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 132,[],0⟩ := by
    simp [tickNatural,program,callable,state,ReferenceProgramLabels.instruction,zeroLabel,BinaryZeroProgram.program]
  have t40 : tickNatural program
      (state (heap++[.flag (isZero word).1]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 140)=
      some ⟨state (heap++[.flag (isZero word).1]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
    simp [tickNatural,program,BinaryZeroProgram.program,callable,state,Registers.get,Registers.set]
  simpa [Nat.add_assoc] using NaturalRun.step t39 (run_append z (.step t40 (.done _)))

end DirectedFlowCutGap.CanonicalRationalQuotient
