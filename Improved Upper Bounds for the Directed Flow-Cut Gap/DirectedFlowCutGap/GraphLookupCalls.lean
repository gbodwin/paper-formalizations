import DirectedFlowCutGap.GraphDiscoveryCalls

/-! Actual stable lookup compares padded vertex labels, then compares retained
rational walk records only for equal labels. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def lookup (u : Bits) : List Entry → Option Walk
  | [] => none
  | x::xs =>
    let tail := lookup u xs
    if BinaryComparisonProgram.order x.1 u=.eq then GraphRelaxationProgram.pick x.2 tail else tail

def lookupFinishSteps (x : Walk) : Option Walk → ℕ
  | none => 3
  | some y => GraphRelaxationProgram.pickSteps x y+5

def lookupFinishCells (x : Walk) : Option Walk → ℕ
  | none => 0
  | some y => GraphRelaxationProgram.pickCells x y

def lookupSteps (u : Bits) : List Entry → ℕ
  | [] => 3
  | x::xs => lookupSteps u xs+BinaryComparisonProgram.steps x.1 u+
      if BinaryComparisonProgram.order x.1 u=.eq then 14+lookupFinishSteps x.2 (lookup u xs) else 13

def lookupCells (u : Bits) : List Entry → ℕ
  | [] => 1
  | x::xs => lookupCells u xs+1+BinaryComparisonProgram.cells x.1 u+
      if BinaryComparisonProgram.order x.1 u=.eq then lookupFinishCells x.2 (lookup u xs) else 0

theorem choose_return {heap : NaturalHeap} {a b : ℕ} {x y : Walk}
    (left : StoredWalk heap a x) (right : StoredWalk heap b y)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext,ext.length=GraphRelaxationProgram.pickCells x y ∧
      NaturalRun program (GraphRelaxationProgram.pickSteps x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 696) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c
          (if (BinaryRational.le x.cost y.cost).1 then a else b) stack source pc) ∧
      StoredWalk (heap++ext) (if (BinaryRational.le x.cost y.cost).1 then a else b)
        (GraphRelaxationProgram.choose x y) := by
  obtain ⟨ext,len,body,rep⟩ := GraphRelaxationProgram.choose_return left right next c d hn ⟨a,b,c,d⟩ 531 [] source
  have lift := ReferenceProgramLabels.run scanLabel GraphRelaxationProgram.program program scan_slots body
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  let root := if (BinaryRational.le x.cost y.cost).1 then a else b
  have core : NaturalRun program (GraphRelaxationProgram.pickSteps x y)
      (state heap next a b c d (⟨531,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 520) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 531) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      GraphRelaxationProgram.state,scanLabel,state,root] using lift
  have first : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 696)=
      some ⟨state heap next a b c d (⟨531,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 520,[],0⟩ := by
    simp [tickNatural,program,state]
  have last : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 531)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,len,by simpa [Nat.add_assoc,root] using
    (NaturalRun.step first (run_append core (.step last (.done _)))),rep⟩

/-- A nil tail returns the actual head pointer. A nonnil tail invokes the
original rational comparison and keeps the head on ties. -/
theorem lookup_finish {heap : NaturalHeap} {a b : ℕ} {x : Walk} {tail : Option Walk}
    (left : StoredWalk heap a x) (right : StoredOption heap b tail)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=lookupFinishCells x tail ∧
      NaturalRun program (lookupFinishSteps x tail)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 694) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (GraphRelaxationProgram.pick x tail) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  cases tail with
  | none =>
    have nil : heap[b]?=some .nil := right
    have t694 : tickNatural program (state heap next a b c d frames source 694)=
        some ⟨state heap next a b c d frames source 710,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,nil,tagBranch]
    have t710 : tickNatural program (state heap next a b c d frames source 710)=
        some ⟨state heap next a b c a frames source 711,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t711 : tickNatural program (state heap next a b c a frames source 711)=
        some ⟨state heap next saved.a saved.b saved.c a stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨[],a,rfl,by simpa [lookupFinishSteps] using
      (NaturalRun.step t694 (.step t710 (.step t711 (.done _)))),by simpa [StoredOption,GraphRelaxationProgram.StoredOption,GraphRelaxationProgram.pick] using left⟩
  | some y =>
    obtain ⟨es,cost,hb,he,hc⟩ := right
    have right : StoredWalk heap b y := ⟨es,cost,hb,he,hc⟩
    obtain ⟨ext,len,body,rep⟩ := choose_return left right next c d hn ⟨a,b,c,d⟩ 697 frames source
    let root := if (BinaryRational.le x.cost y.cost).1 then a else b
    have t694 : tickNatural program (state heap next a b c d frames source 694)=
        some ⟨state heap next a b c d frames source 695,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hb,tagBranch]
    have t695 : tickNatural program (state heap next a b c d frames source 695)=
        some ⟨state heap next a b c d (⟨697,.r3,⟨a,b,c,d⟩⟩::frames) source 696,[],0⟩ := by
      simp [tickNatural,program,state]
    have t697 : tickNatural program (state (heap++ext) (next+ext.length) a b c root frames source 697)=
        some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨ext,root,len,by simpa [lookupFinishSteps,Nat.add_assoc] using
      (NaturalRun.step t694 (.step t695 (run_append body (.step t697 (.done _))))),rep⟩

end DirectedFlowCutGap.GraphDiscoveryProgram
