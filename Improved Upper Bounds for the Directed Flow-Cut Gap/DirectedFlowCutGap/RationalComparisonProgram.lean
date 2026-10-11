import DirectedFlowCutGap.BinaryComparisonProgram
import DirectedFlowCutGap.BinaryMultiplicationProgram
import DirectedFlowCutGap.BinaryRational

/-! An actual cross-product comparison on two stored rational records. All
products and the final comparison use literal callable instruction bodies.
The representation and denominator-positivity premises are proof-side only. -/
namespace DirectedFlowCutGap.RationalComparisonProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def mulLabel (pc : Fin 96) : Fin 158 := ⟨pc.val,by omega⟩
def cmpLabel (pc : Fin 48) : Fin 158 := ⟨pc.val+96,by omega⟩
def program : Program 158 := fun pc =>
  if pc.val=95 ∨ pc.val=142 then .ret .r3
  else if h : pc.val<96 then
    ReferenceProgramLabels.instruction mulLabel (BinaryMultiplicationProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<144 then
    ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program ⟨pc.val-96,by omega⟩)
  else match pc.val with
  | 144 => .field .r2 .r1 false 145
  | 145 => .field .r3 .r0 true 146
  | 146 => .make .r2 (.pair .r2 .r3) 147
  | 147 => .field .r1 .r1 true 148
  | 148 => .field .r0 .r0 false 149
  | 149 => .call 94 150 .r3
  | 150 => .field .r0 .r2 false 151
  | 151 => .field .r1 .r2 true 152
  | 152 => .move .r2 .r3 153
  | 153 => .call 94 154 .r3
  | 154 => .move .r0 .r2 155
  | 155 => .move .r1 .r3 156
  | 156 => .call 126 157 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 158)) (source : Bits) (pc : Fin 158) : NaturalState 158 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def Stored (heap : NaturalHeap) (root : ℕ) (x : BinaryRational.Fraction) : Prop :=
  ∃ num den, heap[root]?=some (.pair num den) ∧ BoolList heap num x.num ∧ BoolList heap den x.den

theorem stored_extend {heap : NaturalHeap} {root : ℕ} {x : BinaryRational.Fraction}
    (h : Stored heap root x) (ext : NaturalHeap) : Stored (heap++ext) root x := by
  obtain ⟨num,den,pair,hn,hd⟩ := h
  exact ⟨num,den,lookup_extend pair ext,boolList_extend hn ext,boolList_extend hd ext⟩

def leftProduct (x y : BinaryRational.Fraction) : Bits := (mul x.num y.den).1
def rightProduct (x y : BinaryRational.Fraction) : Bits := (mul y.num x.den).1
def result (x y : BinaryRational.Fraction) : Bool := (lessEqual (leftProduct x y) (rightProduct x y)).1

theorem result_spec (x y : BinaryRational.Fraction) : result x y=(BinaryRational.le x y).1 := by
  apply Bool.eq_iff_iff.mpr
  change (lessEqual _ _).1=true ↔ (lessEqual _ _).1=true
  rw [(lessEqual_spec _ _).1,(lessEqual_spec _ _).1]
  simp [leftProduct,rightProduct,(mul_spec _ _).1,(canonical_values _ _).2.1]

def instructions (x y : BinaryRational.Fraction) : ℕ :=
  BinaryMultiplicationProgram.steps x.num y.den+BinaryMultiplicationProgram.steps y.num x.den+
    BinaryComparisonProgram.steps (leftProduct x y) (rightProduct x y)+21

def cells (x y : BinaryRational.Fraction) : ℕ :=
  BinaryMultiplicationProgram.cells x.num y.den+BinaryMultiplicationProgram.cells y.num x.den+
    BinaryComparisonProgram.cells (leftProduct x y) (rightProduct x y)+2

theorem mul_slots (pc : Fin 96) (h : BinaryMultiplicationProgram.program pc ≠ .halt) :
    program (mulLabel pc)=ReferenceProgramLabels.instruction mulLabel (BinaryMultiplicationProgram.program pc) := by
  by_cases hp : pc.val=95
  · have he : pc=95 := Fin.ext hp
    subst pc;simp [BinaryMultiplicationProgram.program] at h
  · simp [program,mulLabel,pc.isLt,hp,show ¬pc.val=142 by omega]

theorem cmp_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc ≠ .halt) :
    program (cmpLabel pc)=ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=46
  · have he : pc=46 := Fin.ext hp
    subst pc;simp [BinaryComparisonProgram.program] at h
  · simp [program,cmpLabel,show ¬pc.val+96=95 by omega,show ¬pc.val+96=142 by omega,
      show ¬pc.val+96<96 by omega,show pc.val+96<144 by omega]

theorem run_append {s u v : NaturalState 158} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The actual multiplication halt is changed into one paid return. -/
theorem multiply_return {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 158)
    (stack : List (Frame ℕ 158)) (source : Bits) :
    ∃ ext root, ext.length=BinaryMultiplicationProgram.cells xs ys ∧
      NaturalRun program (BinaryMultiplicationProgram.steps xs ys+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 94) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (mul xs ys).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := BinaryMultiplicationProgram.mul_return left right next c d hn ⟨a,b,c,d⟩ 95 [] source
  have t94 : tickNatural BinaryMultiplicationProgram.program
      (BinaryMultiplicationProgram.state heap next a b c d [] source 94)=
      some ⟨BinaryMultiplicationProgram.state heap next a b c d [⟨95,.r3,⟨a,b,c,d⟩⟩] source 64,[],0⟩ := by
    simp [tickNatural,BinaryMultiplicationProgram.program,BinaryMultiplicationProgram.state]
  have lift := ReferenceProgramLabels.run mulLabel BinaryMultiplicationProgram.program program mul_slots (.step t94 core)
  have withStack := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (BinaryMultiplicationProgram.steps xs ys+1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 94) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 95) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryMultiplicationProgram.state,mulLabel,state,len] using withStack
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 95)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

/-- The comparison body is callable with the same input heap and arbitrary
saved caller. The true/false result is the root actually returned by its code. -/
theorem compare_return {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 158)
    (stack : List (Frame ℕ 158)) (source : Bits) :
    ∃ ext root, ext.length=BinaryComparisonProgram.cells xs ys+1 ∧
      NaturalRun program (BinaryComparisonProgram.steps xs ys+4)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 126) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (lessEqual xs ys).1) := by
  obtain ⟨out,run,flag,_,_,ha,hb,hc,frames,src,hpc,dense,ext,halt⟩ :=
    BinaryComparisonProgram.compare_high (BinaryComparisonProgram.state heap next a b c d [] source 30)
      rfl hn left right rfl
  obtain ⟨ext,he,le⟩ := ext
  have lifted := ReferenceProgramLabels.run cmpLabel BinaryComparisonProgram.program program cmp_slots run
  have lifted := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lifted
  have shape : out=BinaryComparisonProgram.state (heap++ext) (next+ext.length)
      a b c out.registers.d [] source 46 := by
    cases out with
    | mk oh on regs frames pc src =>
      cases regs
      simp_all [BinaryComparisonProgram.state]
  have body : NaturalRun program (BinaryComparisonProgram.steps xs ys+3)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 126) []
      (state (heap++ext) (next+ext.length) a b c out.registers.d (⟨pc,.r3,saved⟩::stack) source 142) := by
    rw [shape] at lifted
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryComparisonProgram.state,cmpLabel,state] using lifted
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c out.registers.d (⟨pc,.r3,saved⟩::stack) source 142)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c out.registers.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,out.registers.d,le,?_,?_⟩
  · simpa [Nat.add_assoc] using run_append body (.step ret (.done _))
  · simpa only [he,BinaryComparisonProgram.state] using flag

/-- The caller extracts the four actual field pointers, saves the opposite
pair in one real cell, and computes both products before comparing them. -/
theorem run_high (x y : BinaryRational.Fraction) (initial : NaturalState 158)
    (pc0 : initial.pc=144) (hn : initial.next=initial.heap.length)
    (left : Stored initial.heap initial.registers.a x)
    (right : Stored initial.heap initial.registers.b y) (empty : initial.stack=[]) :
    ∃ final, NaturalRun program (instructions x y) initial [] final ∧
      final.heap[final.registers.d]?=some (.flag (BinaryRational.le x y).1) ∧
      Stored final.heap initial.registers.a x ∧ Stored final.heap initial.registers.b y ∧
      final.source=initial.source ∧ final.stack=[] ∧ final.pc=157 ∧
      final.next=final.heap.length ∧
      (∃ ext,final.heap=initial.heap++ext ∧ ext.length=cells x y) ∧
      tickNatural program final=none := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn left right empty
      subst pc;subst stack
      obtain ⟨xn,xd,hx,hxn,hxd⟩ := left
      obtain ⟨yn,yd,hy,hyn,hyd⟩ := right
      let pair : NaturalHeap := [.pair yn xd]
      let h1 := heap++pair
      let n1 := next+1
      have dense1 : n1=h1.length := by simp [h1,n1,pair,hn]
      obtain ⟨ep,rp,lp,hp,repP⟩ := multiply_return (boolList_extend hxn pair) (boolList_extend hyd pair)
        n1 next xd dense1 ⟨xn,yd,next,xd⟩ 150 [] source
      let h2 := h1++ep
      let n2 := n1+ep.length
      have dense2 : n2=h2.length := by simp [n2,h2,dense1]
      have pair2 : h2[next]?=some (.pair yn xd) := lookup_extend (by simp [h1,pair,hn]) ep
      obtain ⟨eq,rq,lq,hq,repQ⟩ := multiply_return
        (boolList_extend (boolList_extend hyn pair) ep) (boolList_extend (boolList_extend hxd pair) ep)
        n2 rp rp dense2 ⟨yn,xd,rp,rp⟩ 154 [] source
      let h3 := h2++eq
      let n3 := n2+eq.length
      have dense3 : n3=h3.length := by simp [n3,h3,dense2]
      obtain ⟨ec,rc,lc,hc,flag⟩ := compare_return (boolList_extend repP eq) repQ
        n3 rp rq dense3 ⟨rp,rq,rp,rq⟩ 157 [] source
      have t144 : tickNatural program (state heap next a b c d [] source 144)=
          some ⟨state heap next a b yn d [] source 145,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hy]
      have t145 : tickNatural program (state heap next a b yn d [] source 145)=
          some ⟨state heap next a b yn xd [] source 146,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hx]
      have t146 : tickNatural program (state heap next a b yn xd [] source 146)=
          some ⟨state h1 n1 a b next xd [] source 147,[],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,h1,n1,pair]
      have t147 : tickNatural program (state h1 n1 a b next xd [] source 147)=
          some ⟨state h1 n1 a yd next xd [] source 148,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,h1,lookup_extend hy pair]
      have t148 : tickNatural program (state h1 n1 a yd next xd [] source 148)=
          some ⟨state h1 n1 xn yd next xd [] source 149,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,h1,lookup_extend hx pair]
      have t149 : tickNatural program (state h1 n1 xn yd next xd [] source 149)=
          some ⟨state h1 n1 xn yd next xd [⟨150,.r3,⟨xn,yd,next,xd⟩⟩] source 94,[],0⟩ := by
        simp [tickNatural,program,state]
      have t150 : tickNatural program (state h2 n2 xn yd next rp [] source 150)=
          some ⟨state h2 n2 yn yd next rp [] source 151,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,pair2]
      have t151 : tickNatural program (state h2 n2 yn yd next rp [] source 151)=
          some ⟨state h2 n2 yn xd next rp [] source 152,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,pair2]
      have t152 : tickNatural program (state h2 n2 yn xd next rp [] source 152)=
          some ⟨state h2 n2 yn xd rp rp [] source 153,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t153 : tickNatural program (state h2 n2 yn xd rp rp [] source 153)=
          some ⟨state h2 n2 yn xd rp rp [⟨154,.r3,⟨yn,xd,rp,rp⟩⟩] source 94,[],0⟩ := by
        simp [tickNatural,program,state]
      have t154 : tickNatural program (state h3 n3 yn xd rp rq [] source 154)=
          some ⟨state h3 n3 rp xd rp rq [] source 155,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t155 : tickNatural program (state h3 n3 rp xd rp rq [] source 155)=
          some ⟨state h3 n3 rp rq rp rq [] source 156,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t156 : tickNatural program (state h3 n3 rp rq rp rq [] source 156)=
          some ⟨state h3 n3 rp rq rp rq [⟨157,.r3,⟨rp,rq,rp,rq⟩⟩] source 126,[],0⟩ := by
        simp [tickNatural,program,state]
      let final := state (h3++ec) (n3+ec.length) rp rq rp rc [] source 157
      have pre : NaturalRun program 6 (state heap next a b c d [] source 144) []
          (state h1 n1 xn yd next xd [⟨150,.r3,⟨xn,yd,next,xd⟩⟩] source 94) :=
        .step t144 (.step t145 (.step t146 (.step t147 (.step t148 (.step t149 (.done _))))))
      have middle : NaturalRun program 4 (state h2 n2 xn yd next rp [] source 150) []
          (state h2 n2 yn xd rp rp [⟨154,.r3,⟨yn,xd,rp,rp⟩⟩] source 94) :=
        .step t150 (.step t151 (.step t152 (.step t153 (.done _))))
      have last : NaturalRun program 3 (state h3 n3 yn xd rp rq [] source 154) []
          (state h3 n3 rp rq rp rq [⟨157,.r3,⟨rp,rq,rp,rq⟩⟩] source 126) :=
        .step t154 (.step t155 (.step t156 (.done _)))
      refine ⟨final,?_,?_,?_,?_,rfl,rfl,rfl,?_,?_,?_⟩
      · have all := run_append pre (run_append hp (run_append middle (run_append hq (run_append last hc))))
        convert all using 1 <;> simp [instructions,state,leftProduct,rightProduct,Nat.add_assoc];omega
      · change (heap++pair++ep++eq++ec)[rc]?=some (.flag (result x y)) at flag
        rw [result_spec] at flag
        exact flag
      · exact stored_extend (stored_extend (stored_extend (stored_extend ⟨xn,xd,hx,hxn,hxd⟩ pair) ep) eq) ec
      · exact stored_extend (stored_extend (stored_extend (stored_extend ⟨yn,yd,hy,hyn,hyd⟩ pair) ep) eq) ec
      · simp [final,state,dense3]
      · refine ⟨pair++ep++eq++ec,?_,?_⟩
        · simp [final,state,h3,h2,h1,List.append_assoc]
        · simp [cells,pair,lp,lq,lc,leftProduct,rightProduct];omega
      · simp [tickNatural,program,final,state]

/-- The bound counts all four stored fields, including padding. -/
def inputSize (x y : BinaryRational.Fraction) : ℕ :=
  x.num.length+x.den.length+y.num.length+y.den.length+1

theorem instructions_bound (x y : BinaryRational.Fraction) :
    instructions x y ≤ 400*(inputSize x y)^2 := by
  let z := inputSize x y
  have hz : 1 ≤ z := by dsimp [z,inputSize];omega
  have hx : x.num.length+1 ≤ z := by dsimp [z,inputSize];omega
  have hy : y.num.length+1 ≤ z := by dsimp [z,inputSize];omega
  have hxy : x.num.length+y.den.length+2 ≤ 2*z := by dsimp [z,inputSize];omega
  have hyx : y.num.length+x.den.length+2 ≤ 2*z := by dsimp [z,inputSize];omega
  have hp := (BinaryMultiplicationProgram.steps_bound x.num y.den).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 64 hx) hxy)
  have hq := (BinaryMultiplicationProgram.steps_bound y.num x.den).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 64 hy) hyx)
  have hpl := (mul_spec x.num y.den).2.1
  have hql := (mul_spec y.num x.den).2.1
  have hl : (leftProduct x y).length+(rightProduct x y).length+1 ≤ 3*z := by
    dsimp [leftProduct,rightProduct,z,inputSize];omega
  have hc := (BinaryComparisonProgram.steps_bound (leftProduct x y) (rightProduct x y)).trans
    (Nat.mul_le_mul_left 16 hl)
  dsimp [instructions]
  nlinarith

/-- The same low-level run pays every field lookup, saved record, both product
calls, the comparison and its sole final halt. Both original rational records
remain represented in the output heap. -/
theorem compare_bit (x y : BinaryRational.Fraction) {H B : ℕ} (initial : BitState 158)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=144)
    (hn : value initial.next=initial.heap.length)
    (left : Stored (eraseState initial).heap (eraseState initial).registers.a x)
    (right : Stored (eraseState initial).heap (eraseState initial).registers.b y)
    (empty : initial.stack=[]) :
    ∃ charge out, Run program (instructions x y) charge initial [] out ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag (BinaryRational.le x y).1) ∧
      Stored (eraseState out).heap (eraseState initial).registers.a x ∧
      Stored (eraseState out).heap (eraseState initial).registers.b y ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=157 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells x y) ∧
      instructions x y ≤ 400*(inputSize x y)^2 ∧
      out.Bounded (H+instructions x y) (B+instructions x y) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 158 H B (instructions x y) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,flag,lword,rword,source,stack,pc,_,ext,halt⟩ :=
    run_high x y (eraseState initial) pc0 hn' left right empty'
  obtain ⟨charge,out,run,erase,bound,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,?_,src.trans source,?_,?_,?_,instructions_bound x y,bound,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase];exact flag
  · rw [erase];exact lword
  · rw [erase];exact rword
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · exact (congrArg State.pc erase).trans pc
  · rw [erase];exact ext

end DirectedFlowCutGap.RationalComparisonProgram
