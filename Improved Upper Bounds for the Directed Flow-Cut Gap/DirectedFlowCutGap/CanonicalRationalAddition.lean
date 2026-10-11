import DirectedFlowCutGap.CanonicalArithmeticProgram
import DirectedFlowCutGap.RationalComparisonProgram

/-! Literal unreduced rational addition. Four actual canonical arithmetic calls
construct the exact stored numerator and denominator of BinaryRational.add.
All scratch records, calls, field reads and the final record allocation are paid. -/
namespace DirectedFlowCutGap.CanonicalRationalAddition
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def label (pc : Fin 116) : Fin 142 := ⟨pc.val,by omega⟩
def program : Program 142 := fun pc =>
  if pc.val=115 then .ret .r3
  else if h : pc.val<116 then
    ReferenceProgramLabels.instruction label (CanonicalArithmeticProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 116 => .make .r2 (.pair .r0 .r1) 117
  | 117 => .field .r0 .r0 false 118
  | 118 => .field .r1 .r1 true 119
  | 119 => .call 110 120 .r3
  | 120 => .make .r2 (.pair .r3 .r2) 121
  | 121 => .field .r1 .r2 true 122
  | 122 => .field .r0 .r1 true 123
  | 123 => .field .r0 .r0 false 124
  | 124 => .field .r1 .r1 false 125
  | 125 => .field .r1 .r1 true 126
  | 126 => .call 110 127 .r3
  | 127 => .field .r0 .r2 false 128
  | 128 => .move .r1 .r3 129
  | 129 => .call 114 130 .r3
  | 130 => .field .r0 .r2 true 131
  | 131 => .make .r2 (.pair .r3 .r0) 132
  | 132 => .field .r1 .r0 true 133
  | 133 => .field .r1 .r1 true 134
  | 134 => .field .r0 .r0 false 135
  | 135 => .field .r0 .r0 true 136
  | 136 => .call 110 137 .r3
  | 137 => .field .r0 .r2 false 138
  | 138 => .make .r3 (.pair .r0 .r3) 139
  | 139 => .ret .r3
  | 140 => .call 116 141 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 142)) (source : Bits) (pc : Fin 142) : NaturalState 142 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩
def product (xs ys : Bits) : Bits := (mulCanonical xs ys).1
def p (x y : BinaryRational.Fraction) : Bits := product x.num y.den
def q (x y : BinaryRational.Fraction) : Bits := product y.num x.den
def arithmeticCells (multiply : Bool) (xs ys : Bits) : ℕ :=
  CanonicalArithmeticProgram.rawCells multiply xs ys+
    (CanonicalArithmeticProgram.result multiply xs ys).length

def instructions (x y : BinaryRational.Fraction) : ℕ :=
  CanonicalArithmeticProgram.instructions true x.num y.den+
  CanonicalArithmeticProgram.instructions true y.num x.den+
  CanonicalArithmeticProgram.instructions false (p x y) (q x y)+
  CanonicalArithmeticProgram.instructions true x.den y.den+28

def cells (x y : BinaryRational.Fraction) : ℕ :=
  arithmeticCells true x.num y.den+arithmeticCells true y.num x.den+
  arithmeticCells false (p x y) (q x y)+arithmeticCells true x.den y.den+4

theorem slots (pc : Fin 116) (h : CanonicalArithmeticProgram.program pc ≠ .halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (CanonicalArithmeticProgram.program pc) := by
  by_cases hp : pc.val=115
  · have he : pc=115 := Fin.ext hp
    subst pc;simp [CanonicalArithmeticProgram.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append {s u v : NaturalState 142} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The actual canonical table is called with the original live caller stack. -/
theorem arithmetic_return (multiply : Bool) {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 142)
    (stack : List (Frame ℕ 142)) (source : Bits) :
    ∃ ext root, ext.length=arithmeticCells multiply xs ys ∧
      NaturalRun program (CanonicalArithmeticProgram.instructions multiply xs ys+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source
          (label (CanonicalArithmeticProgram.top multiply))) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root
        (if multiply then mulCanonical xs ys else addCanonical xs ys).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalArithmeticProgram.canonical_high multiply
    (CanonicalArithmeticProgram.state heap next a b c d [] source (CanonicalArithmeticProgram.top multiply))
    rfl hn left right rfl
  have lift := ReferenceProgramLabels.run label CanonicalArithmeticProgram.program program slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (CanonicalArithmeticProgram.instructions multiply xs ys)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source
        (label (CanonicalArithmeticProgram.top multiply))) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 115) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalArithmeticProgram.state,label,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 115)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,?_⟩
  · exact run_append body (.step ret (.done _))
  · rw [CanonicalArithmeticProgram.result_exact] at rep
    exact rep

/-- All four original fields remain stored while the actual new record is built. -/
theorem add_return (x y : BinaryRational.Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 142)
    (stack : List (Frame ℕ 142)) (source : Bits) :
    ∃ ext root, ext.length=cells x y ∧
      NaturalRun program (instructions x y)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 116) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.add x y).1 := by
  obtain ⟨xn,xd,hx,hxn,hxd⟩ := left
  obtain ⟨yn,yd,hy,hyn,hyd⟩ := right
  let frames : List (Frame ℕ 142) := ⟨pc,.r3,saved⟩::stack
  let e0 : NaturalHeap := [.pair a b]
  let h0 := heap++e0
  let n0 := next+1
  have dense0 : n0=h0.length := by simp [n0,h0,e0,hn]
  obtain ⟨ep,rp,lp,runP,repP⟩ := arithmetic_return true
    (boolList_extend hxn e0) (boolList_extend hyd e0) n0 next d dense0 ⟨xn,yd,next,d⟩ 120 frames source
  let h1 := h0++ep
  let n1 := n0+ep.length
  let e1 : NaturalHeap := [.pair rp next]
  let h2 := h1++e1
  let n2 := n1+1
  have dense1 : n1=h1.length := by simp [n1,h1,dense0]
  have dense2 : n2=h2.length := by simp [n2,h2,e1,dense1]
  obtain ⟨eq,rq,lq,runQ,repQ⟩ := arithmetic_return true
    (boolList_extend (boolList_extend (boolList_extend hyn e0) ep) e1)
    (boolList_extend (boolList_extend (boolList_extend hxd e0) ep) e1)
    n2 n1 rp dense2 ⟨yn,xd,n1,rp⟩ 127 frames source
  let h3 := h2++eq
  let n3 := n2+eq.length
  have dense3 : n3=h3.length := by simp [n3,h3,dense2]
  obtain ⟨en,rn,ln,runN,repN⟩ := arithmetic_return false
    (boolList_extend (boolList_extend repP e1) eq) repQ n3 n1 rq dense3 ⟨rp,rq,n1,rq⟩ 130 frames source
  let h4 := h3++en
  let n4 := n3+en.length
  let e2 : NaturalHeap := [.pair rn next]
  let h5 := h4++e2
  let n5 := n4+1
  have dense4 : n4=h4.length := by simp [n4,h4,dense3]
  have dense5 : n5=h5.length := by simp [n5,h5,e2,dense4]
  obtain ⟨ed,rd,ld,runD,repD⟩ := arithmetic_return true
    (boolList_extend (boolList_extend (boolList_extend (boolList_extend (boolList_extend (boolList_extend hxd e0) ep) e1) eq) en) e2)
    (boolList_extend (boolList_extend (boolList_extend (boolList_extend (boolList_extend (boolList_extend hyd e0) ep) e1) eq) en) e2)
    n5 n4 rn dense5 ⟨xd,yd,n4,rn⟩ 137 frames source
  let h6 := h5++ed
  let n6 := n5+ed.length
  let e3 : NaturalHeap := [.pair rn rd]
  let h7 := h6++e3
  let n7 := n6+1
  have dense6 : n6=h6.length := by simp [n6,h6,dense5]
  have hxh0 : h0[a]?=some (.pair xn xd) := (lookup_extend hx e0)
  have hyh0 : h0[b]?=some (.pair yn yd) := (lookup_extend hy e0)
  have hxh2 : h2[a]?=some (.pair xn xd) := (lookup_extend (lookup_extend (lookup_extend hx e0) ep) e1)
  have hyh2 : h2[b]?=some (.pair yn yd) := (lookup_extend (lookup_extend (lookup_extend hy e0) ep) e1)
  have hxh5 : h5[a]?=some (.pair xn xd) := (lookup_extend (lookup_extend (lookup_extend (lookup_extend (lookup_extend (lookup_extend hx e0) ep) e1) eq) en) e2)
  have hyh5 : h5[b]?=some (.pair yn yd) := (lookup_extend (lookup_extend (lookup_extend (lookup_extend (lookup_extend (lookup_extend hy e0) ep) e1) eq) en) e2)
  have orig0 : h0[next]?=some (.pair a b) := by simp [h0,e0,hn]
  have orig2 : h2[next]?=some (.pair a b) := lookup_extend (lookup_extend orig0 ep) e1
  have orig5 : h5[next]?=some (.pair a b) := lookup_extend (lookup_extend (lookup_extend orig2 eq) en) e2
  have save2 : h2[n1]?=some (.pair rp next) := by simp [h2,e1,dense1]
  have save3 : h3[n1]?=some (.pair rp next) := lookup_extend save2 eq
  have save4 : h4[n1]?=some (.pair rp next) := lookup_extend save3 en
  have num5 : h5[n4]?=some (.pair rn next) := by simp [h5,e2,dense4]
  have num6 : h6[n4]?=some (.pair rn next) := lookup_extend num5 ed
  have t116 : tickNatural program (state heap next a b c d frames source 116)=
      some ⟨state h0 n0 a b next d frames source 117,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,n0,e0]
  have t117 : tickNatural program (state h0 n0 a b next d frames source 117)=
      some ⟨state h0 n0 xn b next d frames source 118,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hxh0]
  have t118 : tickNatural program (state h0 n0 xn b next d frames source 118)=
      some ⟨state h0 n0 xn yd next d frames source 119,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hyh0]
  have t119 : tickNatural program (state h0 n0 xn yd next d frames source 119)=
      some ⟨state h0 n0 xn yd next d (⟨120,.r3,⟨xn,yd,next,d⟩⟩::frames) source 110,[],0⟩ := by
    simp [tickNatural,program,state]
  have t120 : tickNatural program (state h1 n1 xn yd next rp frames source 120)=
      some ⟨state h2 n2 xn yd n1 rp frames source 121,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,n2,e1]
  have t121 : tickNatural program (state h2 n2 xn yd n1 rp frames source 121)=
      some ⟨state h2 n2 xn next n1 rp frames source 122,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,save2]
  have t122 : tickNatural program (state h2 n2 xn next n1 rp frames source 122)=
      some ⟨state h2 n2 b next n1 rp frames source 123,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,orig2]
  have t123 : tickNatural program (state h2 n2 b next n1 rp frames source 123)=
      some ⟨state h2 n2 yn next n1 rp frames source 124,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hyh2]
  have t124 : tickNatural program (state h2 n2 yn next n1 rp frames source 124)=
      some ⟨state h2 n2 yn a n1 rp frames source 125,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,orig2]
  have t125 : tickNatural program (state h2 n2 yn a n1 rp frames source 125)=
      some ⟨state h2 n2 yn xd n1 rp frames source 126,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hxh2]
  have t126 : tickNatural program (state h2 n2 yn xd n1 rp frames source 126)=
      some ⟨state h2 n2 yn xd n1 rp (⟨127,.r3,⟨yn,xd,n1,rp⟩⟩::frames) source 110,[],0⟩ := by
    simp [tickNatural,program,state]
  have t127 : tickNatural program (state h3 n3 yn xd n1 rq frames source 127)=
      some ⟨state h3 n3 rp xd n1 rq frames source 128,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,save3]
  have t128 : tickNatural program (state h3 n3 rp xd n1 rq frames source 128)=
      some ⟨state h3 n3 rp rq n1 rq frames source 129,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t129 : tickNatural program (state h3 n3 rp rq n1 rq frames source 129)=
      some ⟨state h3 n3 rp rq n1 rq (⟨130,.r3,⟨rp,rq,n1,rq⟩⟩::frames) source 114,[],0⟩ := by
    simp [tickNatural,program,state]
  have t130 : tickNatural program (state h4 n4 rp rq n1 rn frames source 130)=
      some ⟨state h4 n4 next rq n1 rn frames source 131,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,save4]
  have t131 : tickNatural program (state h4 n4 next rq n1 rn frames source 131)=
      some ⟨state h5 n5 next rq n4 rn frames source 132,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h5,n5,e2]
  have t132 : tickNatural program (state h5 n5 next rq n4 rn frames source 132)=
      some ⟨state h5 n5 next b n4 rn frames source 133,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,orig5]
  have t133 : tickNatural program (state h5 n5 next b n4 rn frames source 133)=
      some ⟨state h5 n5 next yd n4 rn frames source 134,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hyh5]
  have t134 : tickNatural program (state h5 n5 next yd n4 rn frames source 134)=
      some ⟨state h5 n5 a yd n4 rn frames source 135,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,orig5]
  have t135 : tickNatural program (state h5 n5 a yd n4 rn frames source 135)=
      some ⟨state h5 n5 xd yd n4 rn frames source 136,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hxh5]
  have t136 : tickNatural program (state h5 n5 xd yd n4 rn frames source 136)=
      some ⟨state h5 n5 xd yd n4 rn (⟨137,.r3,⟨xd,yd,n4,rn⟩⟩::frames) source 110,[],0⟩ := by
    simp [tickNatural,program,state]
  have t137 : tickNatural program (state h6 n6 xd yd n4 rd frames source 137)=
      some ⟨state h6 n6 rn yd n4 rd frames source 138,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,num6]
  have t138 : tickNatural program (state h6 n6 rn yd n4 rd frames source 138)=
      some ⟨state h7 n7 rn yd n4 n6 frames source 139,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h7,n7,e3]
  have t139 : tickNatural program (state h7 n7 rn yd n4 n6 frames source 139)=
      some ⟨state h7 n7 saved.a saved.b saved.c n6 stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  let ext := e0++ep++e1++eq++en++e2++ed++e3
  have whole := NaturalRun.step t116 (NaturalRun.step t117 (NaturalRun.step t118 (NaturalRun.step t119 (run_append runP (NaturalRun.step t120 (NaturalRun.step t121 (NaturalRun.step t122 (NaturalRun.step t123 (NaturalRun.step t124 (NaturalRun.step t125 (NaturalRun.step t126 (run_append runQ (NaturalRun.step t127 (NaturalRun.step t128 (NaturalRun.step t129 (run_append runN (NaturalRun.step t130 (NaturalRun.step t131 (NaturalRun.step t132 (NaturalRun.step t133 (NaturalRun.step t134 (NaturalRun.step t135 (NaturalRun.step t136 (run_append runD (NaturalRun.step t137 (NaturalRun.step t138 (NaturalRun.step t139 (NaturalRun.done _))))))))))))))))))))))))))))
  refine ⟨ext,n6,?_,?_,?_⟩
  · simp [ext,cells,e0,e1,e2,e3,lp,lq,ln,ld,p,q,product];omega
  · convert whole using 1 <;>
      simp [instructions,p,q,product,state,ext,h7,h6,h5,h4,h3,h2,h1,h0,
        n7,n6,n5,n4,n3,n2,n1,n0,e0,e1,e2,e3,List.append_assoc,Nat.add_assoc]
    all_goals omega
  · have record : h7[n6]?=some (.pair rn rd) := by simp [h7,e3,dense6]
    have nr := boolList_extend (boolList_extend (boolList_extend repN e2) ed) e3
    have dr := boolList_extend repD e3
    have he : heap++ext=h7 := by simp [ext,h7,h6,h5,h4,h3,h2,h1,h0,List.append_assoc]
    rw [he]
    exact ⟨rn,rd,record,nr,dr⟩

/-- A real top-level caller removes the supplied return-frame premise. -/
theorem add_high (x y : BinaryRational.Fraction) (initial : NaturalState 142)
    (pc0 : initial.pc=140) (hn : initial.next=initial.heap.length)
    (left : Stored initial.heap initial.registers.a x)
    (right : Stored initial.heap initial.registers.b y) (empty : initial.stack=[]) :
    ∃ ext root, ext.length=cells x y ∧
      NaturalRun program (1+instructions x y) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          initial.registers.b initial.registers.c root [] initial.source 141) ∧
      Stored (initial.heap++ext) root (BinaryRational.add x y).1 := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn left right empty
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 140)=
          some ⟨state heap next a b c d [⟨141,.r3,⟨a,b,c,d⟩⟩] source 116,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := add_return x y left right next c d hn ⟨a,b,c,d⟩ 141 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_comm,state] using NaturalRun.step first run,rep⟩

def inputSize (x y : BinaryRational.Fraction) : ℕ :=
  x.num.length+x.den.length+y.num.length+y.den.length+2

theorem instructions_bound (x y : BinaryRational.Fraction) :
    1+instructions x y ≤ 20000*(inputSize x y)^2 := by
  let z := inputSize x y
  have hz : 2 ≤ z := by dsimp [z,inputSize];omega
  have hp := (trim_spec (mul x.num y.den).1).2.2.1
  have hq := (trim_spec (mul y.num x.den).1).2.2.1
  have hpl := (mul_spec x.num y.den).2.1
  have hql := (mul_spec y.num x.den).2.1
  have plen : (p x y).length ≤ 3*z := by dsimp [p,product,mulCanonical,z,inputSize];omega
  have qlen : (q x y).length ≤ 3*z := by dsimp [q,product,mulCanonical,z,inputSize];omega
  have h1 : x.num.length+y.den.length+2 ≤ z := by dsimp [z,inputSize];omega
  have h2 : y.num.length+x.den.length+2 ≤ z := by dsimp [z,inputSize];omega
  have h3 : x.den.length+y.den.length+2 ≤ z := by dsimp [z,inputSize];omega
  have h4 : (p x y).length+(q x y).length+2 ≤ 7*z := by omega
  have a1 := (CanonicalArithmeticProgram.instructions_bound true x.num y.den).trans
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left h1 2))
  have a2 := (CanonicalArithmeticProgram.instructions_bound true y.num x.den).trans
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left h2 2))
  have a3 := (CanonicalArithmeticProgram.instructions_bound true x.den y.den).trans
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left h3 2))
  have a4 := (CanonicalArithmeticProgram.instructions_bound false (p x y) (q x y)).trans
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left h4 2))
  dsimp only [instructions]
  change _ ≤ 20000*z^2
  nlinarith

/-- The exact original rational primitive is realized in the same lower heap,
with all scratch arithmetic, original records and one paid terminal halt. -/
theorem add_bit (x y : BinaryRational.Fraction) {H B : ℕ} (initial : BitState 142)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=140)
    (hn : value initial.next=initial.heap.length)
    (left : Stored (eraseState initial).heap (eraseState initial).registers.a x)
    (right : Stored (eraseState initial).heap (eraseState initial).registers.b y)
    (empty : initial.stack=[]) :
    ∃ charge out, Run program (1+instructions x y) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (BinaryRational.add x y).1 ∧
      Stored (eraseState out).heap (eraseState initial).registers.a x ∧
      Stored (eraseState out).heap (eraseState initial).registers.b y ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=141 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells x y) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 142 H B (20000*(inputSize x y)^2) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have hs : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := add_high x y (eraseState initial) pc0 hn' left right hs
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hn : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 141)=none := rfl
    rw [hn] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := instructions_bound x y
  have hm : completeBound 142 H B (1+instructions x y) ≤
      completeBound 142 H B (20000*(inputSize x y)^2) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact stored_extend left ext
  · rw [erase];exact stored_extend right ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=141 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.CanonicalRationalAddition
