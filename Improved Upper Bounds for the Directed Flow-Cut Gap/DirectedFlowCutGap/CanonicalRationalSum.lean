import DirectedFlowCutGap.CanonicalRationalAddition
import DirectedFlowCutGap.BinaryFractionalRows

/-! A literal recursive scan of retained rational records. Each accumulated
cost is the exact canonical field pair used by the original fractional row sum. -/
namespace DirectedFlowCutGap.CanonicalRationalSum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def label (pc : Fin 142) : Fin 158 := ⟨pc.val,by omega⟩
def program : Program 158 := fun pc =>
  if pc.val=141 then .ret .r3
  else if h : pc.val<142 then
    ReferenceProgramLabels.instruction label (CanonicalRationalAddition.program ⟨pc.val,h⟩)
  else match pc.val with
  | 142 => .branch .r0 143 157 157 148
  | 143 => .make .r3 .nil 144
  | 144 => .make .r1 (.flag true) 145
  | 145 => .make .r1 (.pair .r1 .r3) 146
  | 146 => .make .r3 (.pair .r3 .r1) 147
  | 147 => .ret .r3
  | 148 => .field .r2 .r0 false 149
  | 149 => .field .r0 .r0 true 150
  | 150 => .call 142 151 .r3
  | 151 => .move .r0 .r2 152
  | 152 => .move .r1 .r3 153
  | 153 => .call 140 154 .r3
  | 154 => .ret .r3
  | 156 => .call 142 157 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 158)) (source : Bits) (pc : Fin 158) : NaturalState 158 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

inductive StoredList (heap : NaturalHeap) : ℕ → List Fraction → Prop
  | nil {p} : heap[p]?=some .nil → StoredList heap p []
  | cons {p head tail x xs} : heap[p]?=some (.pair head tail) →
      Stored heap head x → StoredList heap tail xs → StoredList heap p (x::xs)

theorem list_extend {heap : NaturalHeap} {p : ℕ} {xs : List Fraction}
    (h : StoredList heap p xs) (ext : NaturalHeap) : StoredList (heap++ext) p xs := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp hx _ ih => exact .cons (lookup_extend hp ext) (stored_extend hx ext) ih

def steps : List Fraction → ℕ
  | [] => 6
  | x::xs => steps xs+CanonicalRationalAddition.instructions x (BinaryFractionalRows.sum xs).1+10

def cells : List Fraction → ℕ
  | [] => 4
  | x::xs => cells xs+CanonicalRationalAddition.cells x (BinaryFractionalRows.sum xs).1

theorem slots (pc : Fin 142) (h : CanonicalRationalAddition.program pc ≠ .halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (CanonicalRationalAddition.program pc) := by
  by_cases hp : pc.val=141
  · have he : pc=141 := Fin.ext hp
    subst pc;simp [CanonicalRationalAddition.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append {s u v : NaturalState 158} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem addition_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 158)
    (stack : List (Frame ℕ 158)) (source : Bits) :
    ∃ ext root, ext.length=CanonicalRationalAddition.cells x y ∧
      NaturalRun program (CanonicalRationalAddition.instructions x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 140) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.add x y).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalRationalAddition.add_high x y
    (CanonicalRationalAddition.state heap next a b c d [] source 140) rfl hn left right rfl
  have lift := ReferenceProgramLabels.run label CanonicalRationalAddition.program program slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+CanonicalRationalAddition.instructions x y)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 140) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 141) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalRationalAddition.state,label,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 141)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append body (.step ret (.done _)) using 1 <;> simp
  omega

theorem sum_return {xs : List Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : StoredList heap a xs) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 158) (stack : List (Frame ℕ 158)) (source : Bits) :
    ∃ ext root, ext.length=cells xs ∧
      NaturalRun program (steps xs)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 142) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryFractionalRows.sum xs).1 := by
  induction xs generalizing heap a next b c d saved pc stack with
  | nil =>
    cases input with
    | nil hp =>
      let frames : List (Frame ℕ 158) := ⟨pc,.r3,saved⟩::stack
      let h1 := heap++[.nil]
      let h2 := h1++[.flag true]
      let h3 := h2++[.pair (next+1) next]
      let h4 := h3++[.pair next (next+2)]
      have t142 : tickNatural program (state heap next a b c d frames source 142)=
          some ⟨state heap next a b c d frames source 143,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t143 : tickNatural program (state heap next a b c d frames source 143)=
          some ⟨state h1 (next+1) a b c next frames source 144,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural,h1]
      have t144 : tickNatural program (state h1 (next+1) a b c next frames source 144)=
          some ⟨state h2 (next+2) a (next+1) c next frames source 145,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h2]
      have t145 : tickNatural program (state h2 (next+2) a (next+1) c next frames source 145)=
          some ⟨state h3 (next+3) a (next+2) c next frames source 146,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h3]
      have t146 : tickNatural program (state h3 (next+3) a (next+2) c next frames source 146)=
          some ⟨state h4 (next+4) a (next+2) c (next+3) frames source 147,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,Nat.add_assoc,Recipe.cell,allocateNatural,h4]
      have t147 : tickNatural program (state h4 (next+4) a (next+2) c (next+3) frames source 147)=
          some ⟨state h4 (next+4) saved.a saved.b saved.c (next+3) stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,frames]
      let ext : NaturalHeap := [.nil,.flag true,.pair (next+1) next,.pair next (next+2)]
      have eh : heap++ext=h4 := by simp [ext,h4,h3,h2,h1,List.append_assoc]
      have nilCell : h4[next]?=some .nil := by simp [h4,h3,h2,h1,hn]
      have flagCell : h4[next+1]?=some (.flag true) := by simp [h4,h3,h2,h1,hn]
      have pairCell : h4[next+2]?=some (.pair (next+1) next) := by simp [h4,h3,h2,h1,hn]
      have record : h4[next+3]?=some (.pair next (next+2)) := by simp [h4,h3,h2,h1,hn]
      refine ⟨ext,next+3,rfl,?_,?_⟩
      · simpa [steps,ext,eh] using NaturalRun.step t142 (.step t143 (.step t144 (.step t145 (.step t146 (.step t147 (.done _))))))
      · rw [eh]
        exact ⟨next,next+2,record,.nil nilCell,.cons pairCell flagCell (.nil nilCell)⟩
  | cons x xs ih =>
    cases input with
    | @cons a head tail x xs hp hx ht =>
      let frames : List (Frame ℕ 158) := ⟨pc,.r3,saved⟩::stack
      obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih ht next b head d hn ⟨tail,b,head,d⟩ 151 frames
      let h1 := heap++et
      let n1 := next+et.length
      have dense1 : n1=h1.length := by simp [h1,n1,hn]
      obtain ⟨ea,ra,la,addRun,addRep⟩ := addition_return x (BinaryFractionalRows.sum xs).1
        (stored_extend hx et) tailRep n1 head rt dense1 ⟨head,rt,head,rt⟩ 154 frames source
      let h2 := h1++ea
      let n2 := n1+ea.length
      have t142 : tickNatural program (state heap next a b c d frames source 142)=
          some ⟨state heap next a b c d frames source 148,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t148 : tickNatural program (state heap next a b c d frames source 148)=
          some ⟨state heap next a b head d frames source 149,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t149 : tickNatural program (state heap next a b head d frames source 149)=
          some ⟨state heap next tail b head d frames source 150,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t150 : tickNatural program (state heap next tail b head d frames source 150)=
          some ⟨state heap next tail b head d (⟨151,.r3,⟨tail,b,head,d⟩⟩::frames) source 142,[],0⟩ := by
        simp [tickNatural,program,state]
      have t151 : tickNatural program (state h1 n1 tail b head rt frames source 151)=
          some ⟨state h1 n1 head b head rt frames source 152,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t152 : tickNatural program (state h1 n1 head b head rt frames source 152)=
          some ⟨state h1 n1 head rt head rt frames source 153,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t153 : tickNatural program (state h1 n1 head rt head rt frames source 153)=
          some ⟨state h1 n1 head rt head rt (⟨154,.r3,⟨head,rt,head,rt⟩⟩::frames) source 140,[],0⟩ := by
        simp [tickNatural,program,state]
      have t154 : tickNatural program (state h2 n2 head rt head ra frames source 154)=
          some ⟨state h2 n2 saved.a saved.b saved.c ra stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,frames]
      have whole := NaturalRun.step t142 (.step t148 (.step t149 (.step t150
        (run_append tailRun (.step t151 (.step t152 (.step t153
          (run_append addRun (.step t154 (.done _))))))))))
      refine ⟨et++ea,ra,by simp [cells,lt,la],?_,?_⟩
      · convert whole using 1 <;> simp [steps,h2,h1,n2,n1,List.append_assoc,Nat.add_assoc]
      · simpa [BinaryFractionalRows.sum,List.append_assoc] using addRep

theorem sum_high {xs : List Fraction} (initial : NaturalState 158)
    (pc0 : initial.pc=156) (hn : initial.next=initial.heap.length)
    (input : StoredList initial.heap initial.registers.a xs) (empty : initial.stack=[]) :
    ∃ ext root, ext.length=cells xs ∧
      NaturalRun program (1+steps xs) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          initial.registers.b initial.registers.c root [] initial.source 157) ∧
      Stored (initial.heap++ext) root (BinaryFractionalRows.sum xs).1 := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn input empty
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 156)=
          some ⟨state heap next a b c d [⟨157,.r3,⟨a,b,c,d⟩⟩] source 142,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := sum_return input next b c d hn ⟨a,b,c,d⟩ 157 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_comm,state] using NaturalRun.step first run,rep⟩

def instructionBound (n B : ℕ) : ℕ :=
  n*(720000*((n+1)*(B+1)+1)^2+10)+7

/-- Canonical accumulated fields give an actual polynomial instruction bound
in the number of retained records and maximum stored input width. -/
theorem steps_bound (xs : List Fraction) (B : ℕ)
    (h : ∀ x ∈ xs, StoredBounded x B) : 1+steps xs ≤ instructionBound xs.length B := by
  let n := xs.length
  let K := (n+1)*(B+1)
  have aux : ∀ ys : List Fraction, ys.length ≤ n →
      (∀ x ∈ ys, StoredBounded x B) →
      steps ys ≤ ys.length*(720000*(K+1)^2+10)+6 := by
    intro ys
    induction ys with
    | nil => intro _ _;simp [steps]
    | cons x ys ih =>
      intro hlen hy
      have hx := hy x List.mem_cons_self
      have hh := fun y hb => hy y (List.mem_cons_of_mem _ hb)
      have hi := ih (by simp only [List.length_cons] at hlen;omega) hh
      have ht := BinaryFractionalRows.sum_stored_bound ys B
        (fun y hb => BinaryFractionalRows.stored_raw_bound (hh y hb))
      have hbK : B ≤ K := by dsimp [K];nlinarith
      have htK : ys.length*(B+1)+1 ≤ K := by
        dsimp [K]
        have hm := Nat.mul_le_mul_right (B+1) (show ys.length+1 ≤ n+1 by
          simp only [List.length_cons] at hlen;omega)
        nlinarith
      have size : CanonicalRationalAddition.inputSize x (BinaryFractionalRows.sum ys).1 ≤ 6*(K+1) := by
        dsimp [CanonicalRationalAddition.inputSize]
        rcases hx with ⟨hxn,hxd⟩
        rcases ht with ⟨htn,htd⟩
        omega
      have hc := (CanonicalRationalAddition.instructions_bound x (BinaryFractionalRows.sum ys).1).trans
        (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left size 2))
      simp only [steps,List.length_cons]
      nlinarith
  have out := aux xs le_rfl h
  dsimp [instructionBound]
  dsimp [n,K] at out
  omega

/-- Exact old row-sum fields, retained input list and reader, actual terminal
halt, and a complete charge on this same lower-machine execution. -/
theorem sum_bit {xs : List Fraction} {H A : ℕ} (initial : BitState 158)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=156)
    (hn : value initial.next=initial.heap.length)
    (input : StoredList (eraseState initial).heap (eraseState initial).registers.a xs)
    (empty : initial.stack=[]) (B : ℕ) (widths : ∀ x ∈ xs, StoredBounded x B) :
    ∃ charge out, Run program (1+steps xs) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (BinaryFractionalRows.sum xs).1 ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a xs ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=157 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells xs) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 158 H A (instructionBound xs.length B) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have hs : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := sum_high (eraseState initial) pc0 hn' input hs
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hn : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 157)=none := rfl
    rw [hn] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := steps_bound xs B widths
  have hm : completeBound 158 H A (1+steps xs) ≤ completeBound 158 H A (instructionBound xs.length B) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact list_extend input ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=157 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.CanonicalRationalSum
