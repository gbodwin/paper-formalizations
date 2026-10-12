import DirectedFlowCutGap.GraphRelaxationAdapters

/-! The real branch after an adjacency test. Every accepted edge is allocated,
costed, and compared with the actual tail answer; absent answers remain nil. -/
namespace DirectedFlowCutGap.GraphRelaxationProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def optionSteps (x : Walk) : Option Walk → ℕ
  | none => 3
  | some y => pickSteps x y+5
def optionCells (x : Walk) : Option Walk → ℕ
  | none => 0
  | some y => pickCells x y

theorem option_return {heap : NaturalHeap} {a b c d head tail : ℕ} {x : Walk} {q : Option Walk}
    (scratch : heap[c]?=some (.pair head tail)) (left : StoredWalk heap d x)
    (right : StoredOption heap tail q)
    (next : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 532) (stack : List (Frame ℕ 532)) (source : Bits) :
    ∃ ext root,ext.length=optionCells x q ∧ NaturalRun program (optionSteps x q)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 481) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (pick x q) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  have t481 : tickNatural program (state heap next a b c d frames source 481)=
      some ⟨state heap next a tail c d frames source 482,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  cases q with
  | none =>
    change heap[tail]?=some .nil at right
    have t482 : tickNatural program (state heap next a tail c d frames source 482)=
        some ⟨state heap next a tail c d frames source 493,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,right,tagBranch]
    have t493 : tickNatural program (state heap next a tail c d frames source 493)=
        some ⟨state heap next saved.a saved.b saved.c d stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨[],d,rfl,?_,?_⟩
    · simpa [optionSteps] using NaturalRun.step t481 (.step t482 (.step t493 (.done _)))
    · simpa [StoredOption,pick] using left
  | some y =>
    obtain ⟨ye,yc,hy,hye,hyc⟩ := right
    obtain ⟨ext,len,core,rep⟩ := choose_return left ⟨ye,yc,hy,hye,hyc⟩ next c d hn
      ⟨d,tail,c,d⟩ 485 frames source
    let root := if (BinaryRational.le x.cost y.cost).1 then d else tail
    have t482 : tickNatural program (state heap next a tail c d frames source 482)=
        some ⟨state heap next a tail c d frames source 483,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hy,tagBranch]
    have t483 : tickNatural program (state heap next a tail c d frames source 483)=
        some ⟨state heap next d tail c d frames source 484,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t484 : tickNatural program (state heap next d tail c d frames source 484)=
        some ⟨state heap next d tail c d (⟨485,.r3,⟨d,tail,c,d⟩⟩::frames) source 520,[],0⟩ := by
      simp [tickNatural,program,state]
    have t485 : tickNatural program
        (state (heap++ext) (next+ext.length) d tail c root frames source 485)=
        some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨ext,root,len,?_,rep⟩
    have joined := NaturalRun.step t481 (.step t482 (.step t483 (.step t484
      (run_append core (.step t485 (.done _))))))
    simpa only [optionSteps,Nat.add_assoc,List.nil_append] using joined

def finishSteps (rows : List Fraction) (sw u : Bits) (x : Entry) (q : Option Walk) (edge : Bool) : ℕ :=
  if edge then extendSteps rows sw (u,x.1) x.2+8+optionSteps (GraphWalkExtension.result rows sw (u,x.1) x.2) q
  else 3
def finishCells (rows : List Fraction) (sw u : Bits) (x : Entry) (q : Option Walk) (edge : Bool) : ℕ :=
  if edge then 1+GraphWalkExtension.cells rows sw (u,x.1) x.2+
    optionCells (GraphWalkExtension.result rows sw (u,x.1) x.2) q else 0

theorem finish_return {heap : NaturalHeap} {a b c d tail : ℕ} {x : Entry} {q : Option Walk}
    {adjacency : List Bits} {rows : List Fraction} {u sw : Bits}
    (entry : StoredEntry heap a x) (context : Context heap b adjacency rows u sw)
    (scratch : heap[c]?=some (.pair a tail)) (answer : StoredOption heap tail q)
    (flag : heap[d]?=some (.flag (adjacent adjacency u x.1))) (hi : value u<rows.length)
    (next : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 532) (stack : List (Frame ℕ 532)) (source : Bits) :
    ∃ ext root,ext.length=finishCells rows sw u x q (adjacent adjacency u x.1) ∧
      NaturalRun program (finishSteps rows sw u x q (adjacent adjacency u x.1))
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 473) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root
        (if adjacent adjacency u x.1 then pick (GraphWalkExtension.result rows sw (u,x.1) x.2) q else q) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  cases he : adjacent adjacency u x.1 with
  | false =>
    have t473 : tickNatural program (state heap next a b c d frames source 473)=
        some ⟨state heap next a b c d frames source 495,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,flag,he,tagBranch]
    have t495 : tickNatural program (state heap next a b c d frames source 495)=
        some ⟨state heap next a b c tail frames source 496,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t496 : tickNatural program (state heap next a b c tail frames source 496)=
        some ⟨state heap next saved.a saved.b saved.c tail stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨[],tail,rfl,?_,?_⟩
    · simpa [finishSteps] using NaturalRun.step t473 (.step t495 (.step t496 (.done _)))
    · simpa using answer
  | true =>
    obtain ⟨v,w,hx,hv,hw⟩ := entry
    obtain ⟨ur,mix,matrix,cost,hp,hm,hu,ha,hc⟩ := context
    let e0 : NaturalHeap := [.pair ur v]
    let h0 := heap++e0
    let n0 := next+1
    have dense0 : n0=h0.length := by simp [h0,n0,e0,hn]
    have newEdge : Edge h0 next (u,x.1) :=
      ⟨ur,v,by simp [h0,e0,hn],boolList_extend hu e0,boolList_extend hv e0⟩
    have oldScratch : h0[c]?=some (.pair a tail) := lookup_extend scratch e0
    have oldEntry : h0[a]?=some (.pair v w) := lookup_extend hx e0
    obtain ⟨ew,rw,lw,runW,repW⟩ := extend_return newEdge (walk_extend hw e0)
      (context_extend ⟨ur,mix,matrix,cost,hp,hm,hu,ha,hc⟩ e0) hi n0 c dense0
      ⟨next,b,c,w⟩ 481 frames source
    let h1 := h0++ew
    let n1 := n0+ew.length
    have dense1 : n1=h1.length := by simp [h1,n1,dense0]
    obtain ⟨ep,rp,lp,runP,repP⟩ := option_return (a:=next) (b:=b)
      (lookup_extend oldScratch ew) repW (option_extend (option_extend answer e0) ew)
      n1 dense1 saved pc stack source
    have t473 : tickNatural program (state heap next a b c d frames source 473)=
        some ⟨state heap next a b c d frames source 474,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,flag,he,tagBranch]
    have t474 : tickNatural program (state heap next a b c d frames source 474)=
        some ⟨state heap next ur b c d frames source 475,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t475 : tickNatural program (state heap next ur b c d frames source 475)=
        some ⟨state heap next ur b c a frames source 476,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t476 : tickNatural program (state heap next ur b c a frames source 476)=
        some ⟨state heap next ur b c v frames source 477,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hx]
    have t477 : tickNatural program (state heap next ur b c v frames source 477)=
        some ⟨state h0 n0 next b c v frames source 478,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h0,n0,e0]
    have t478 : tickNatural program (state h0 n0 next b c v frames source 478)=
        some ⟨state h0 n0 next b c a frames source 479,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,oldScratch]
    have t479 : tickNatural program (state h0 n0 next b c a frames source 479)=
        some ⟨state h0 n0 next b c w frames source 480,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,oldEntry]
    have t480 : tickNatural program (state h0 n0 next b c w frames source 480)=
        some ⟨state h0 n0 next b c w (⟨481,.r3,⟨next,b,c,w⟩⟩::frames) source 510,[],0⟩ := by
      simp [tickNatural,program,state]
    refine ⟨e0++ew++ep,rp,?_,?_,?_⟩
    · simp [finishCells,e0,lw,lp,Nat.add_assoc];omega
    · have joined := NaturalRun.step t473 (.step t474 (.step t475 (.step t476 (.step t477
        (.step t478 (.step t479 (.step t480 (run_append runW runP))))))))
      convert joined using 1 <;> simp [finishSteps,h0,n1,n0,e0,List.append_assoc,Nat.add_assoc,Nat.add_comm]
      omega
    · simpa [h1,h0,List.append_assoc] using repP

end DirectedFlowCutGap.GraphRelaxationProgram
