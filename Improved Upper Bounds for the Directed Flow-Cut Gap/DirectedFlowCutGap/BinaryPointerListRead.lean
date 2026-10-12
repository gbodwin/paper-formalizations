import DirectedFlowCutGap.BinaryIndexedPairRead
import DirectedFlowCutGap.ReferenceProgramStack

/-! A literal binary-indexed read of an immutable pointer-list spine. The
counter is built by instructions; the selected existing head is returned to
an arbitrary real caller. This is the storage access used by graph discovery. -/
namespace DirectedFlowCutGap.BinaryPointerListRead
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

inductive PointerList (heap : NaturalHeap) : ℕ → List ℕ → Prop
  | nil {root : ℕ} : heap[root]?=some .nil → PointerList heap root []
  | cons {root head tail : ℕ} {xs : List ℕ} :
      heap[root]?=some (.pair head tail) → PointerList heap tail xs →
      PointerList heap root (head::xs)

theorem pointerList_extend {heap : NaturalHeap} {root : ℕ} {xs : List ℕ}
    (h : PointerList heap root xs) (extra : NaturalHeap) :
    PointerList (heap++extra) root xs := by
  induction h with
  | nil h => exact .nil (lookup_extend h extra)
  | cons h _ ih => exact .cons (lookup_extend h extra) ih

def label (pc : Fin 17) : Fin 27 := ⟨pc.val,by omega⟩
def program : Program 27 := fun pc =>
  if pc.val=16 then .move .r0 .r1 17
  else if h : pc.val<17 then
    ReferenceProgramLabels.instruction label (BinaryCounterProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 17 => .move .r1 .r3 18
  | 18 => .branch .r1 21 23 23 19
  | 19 => .field .r0 .r0 true 20
  | 20 => .field .r1 .r1 true 18
  | 21 => .field .r3 .r0 false 22
  | 22 => .ret .r3
  | 24 => .call 0 16 .r3
  | 25 => .call 24 26 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 27)) (source : Bits) (pc : Fin 27) : NaturalState 27 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def steps (word : Bits) : ℕ := BinaryCounterProgram.steps word+3*value word+6

theorem steps_bound (word : Bits) : steps word ≤ 6*value word+10*word.length+9 := by
  have := BinaryCounterProgram.steps_bound word
  simp only [steps];omega

theorem slots (pc : Fin 17) (h : BinaryCounterProgram.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (BinaryCounterProgram.program pc) := by
  fin_cases pc <;> simp_all [program,label,BinaryCounterProgram.program,
    ReferenceProgramLabels.instruction]

theorem run_append {s u v : NaturalState 27} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem loop {heap : NaturalHeap} {a b i : ℕ} {xs : List ℕ}
    (table : PointerList heap a xs) (index : IndexSpine heap b i) (hi : i<xs.length)
    (next c d : ℕ) (stack : List (Frame ℕ 27)) (source : Bits) :
    ∃ a' b', NaturalRun program (3*i+2) (state heap next a b c d stack source 18) []
      (state heap next a' b' c xs[i] stack source 22) := by
  induction i generalizing a b xs with
  | zero =>
      cases index with
      | nil hb =>
        cases table with
        | nil ht => simp at hi
        | @cons root head tail xs ht rest =>
          refine ⟨a,b,?_⟩
          have t18 : tickNatural program (state heap next a b c d stack source 18)=
              some ⟨state heap next a b c d stack source 21,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hb,tagBranch]
          have t21 : tickNatural program (state heap next a b c d stack source 21)=
              some ⟨state heap next a b c head stack source 22,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,ht]
          simpa using NaturalRun.step t18 (.step t21 (.done _))
  | succ i ih =>
      cases index with
      | @cons root payload tail i hb rest =>
        cases table with
        | nil ht => simp at hi
        | @cons root head nextRoot xs ht htTail =>
          obtain ⟨a',b',run⟩ := ih htTail rest (by simpa using hi)
          refine ⟨a',b',?_⟩
          have t18 : tickNatural program (state heap next a b c d stack source 18)=
              some ⟨state heap next a b c d stack source 19,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hb,tagBranch]
          have t19 : tickNatural program (state heap next a b c d stack source 19)=
              some ⟨state heap next nextRoot b c d stack source 20,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,ht]
          have t20 : tickNatural program (state heap next nextRoot b c d stack source 20)=
              some ⟨state heap next nextRoot tail c d stack source 18,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hb]
          simpa [Nat.mul_add,Nat.add_assoc] using NaturalRun.step t18 (.step t19 (.step t20 run))

/-- The incoming index is a stored word, not a supplied unary spine. -/
theorem read_return {heap : NaturalHeap} {a b : ℕ} {word : Bits} {xs : List ℕ}
    (input : BoolList heap a word) (table : PointerList heap b xs) (hi : value word<xs.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 27) (stack : List (Frame ℕ 27)) (source : Bits) :
    ∃ ext,ext.length=value word+1 ∧
      NaturalRun program (steps word)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 24) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c xs[value word] stack source pc) := by
  obtain ⟨ext,root,hlen,hcounter,counter⟩ := BinaryCounterProgram.convert_return
    input next b c d hn ⟨a,b,c,d⟩ 16 [] source
  have hlen' : ext.length=value word+1 := hlen.trans (BinaryCounterProgram.cells_eq_value word)
  have hc := ReferenceProgramLabels.run label BinaryCounterProgram.program program slots hcounter
  have hc := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) hc
  have core : NaturalRun program (BinaryCounterProgram.steps word)
      (state heap next a b c d (⟨16,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 16) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryCounterProgram.state,label,state,hlen] using hc
  have call : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 24)=
      some ⟨state heap next a b c d (⟨16,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 0,[],0⟩ := by
    simp [tickNatural,program,state]
  obtain ⟨a',b',walk⟩ := loop (pointerList_extend table ext) counter hi
    (next+ext.length) c root (⟨pc,.r3,saved⟩::stack) source
  have t16 : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 16)=
      some ⟨state (heap++ext) (next+ext.length) b b c root (⟨pc,.r3,saved⟩::stack) source 17,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t17 : tickNatural program
      (state (heap++ext) (next+ext.length) b b c root (⟨pc,.r3,saved⟩::stack) source 17)=
      some ⟨state (heap++ext) (next+ext.length) b root c root (⟨pc,.r3,saved⟩::stack) source 18,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a' b' c xs[value word] (⟨pc,.r3,saved⟩::stack) source 22)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c xs[value word] stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,hlen',?_⟩
  have joined := run_append (.step call core) (.step t16 (.step t17 (run_append walk (.step ret (.done _)))))
  convert joined using 1 <;> simp only [steps,List.nil_append]
  omega

end DirectedFlowCutGap.BinaryPointerListRead
