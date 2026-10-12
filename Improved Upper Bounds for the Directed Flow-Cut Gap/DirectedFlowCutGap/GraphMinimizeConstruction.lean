import DirectedFlowCutGap.GraphBoundedRounds
import DirectedFlowCutGap.GraphLookupScan

/-! One fixed instruction run constructs every relaxation table, then searches
that very table for the retained source candidate. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def minimize (vertices adjacency : List Bits) (rows : List Fraction) (sw target u : Bits) : Option Walk :=
  lookup u (rounds vertices adjacency rows sw target vertices)
def minimizeSteps (vertices adjacency : List Bits) (rows : List Fraction) (sw target u : Bits) : ℕ :=
  roundSteps vertices adjacency rows sw target vertices+
    lookupSteps u (rounds vertices adjacency rows sw target vertices)+5
def minimizeCells (vertices adjacency : List Bits) (rows : List Fraction) (sw target u : Bits) : ℕ :=
  roundCells vertices adjacency rows sw target vertices+
    lookupCells u (rounds vertices adjacency rows sw target vertices)

theorem minimize_return {heap : NaturalHeap} {a b c : ℕ} {vertices adjacency : List Bits}
    {rows : List Fraction} {sw target u : Bits}
    (input : Vertices heap a vertices) (context : GlobalContext heap b vertices adjacency rows sw target)
    (word : BoolList heap c u)
    (hi : ∀ v∈vertices,value v<adjacency.length) (hc : ∀ v∈vertices,value v<rows.length)
    (targetCol : ∀ v,(hv : v∈vertices) → value target<(adjacency[value v]'(hi v hv)).length)
    (columns : ∀ v,(hv : v∈vertices) → ∀ z∈vertices,value z<(adjacency[value v]'(hi v hv)).length)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=minimizeCells vertices adjacency rows sw target u ∧
      NaturalRun program (minimizeSteps vertices adjacency rows sw target u)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 700) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (minimize vertices adjacency rows sw target u) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  obtain ⟨er,rr,lr,runR,repR⟩ := rounds_return input context hi hc targetCol columns
    next c d hn ⟨a,b,c,d⟩ 701 frames source
  let h0 := heap++er
  let n0 := next+er.length
  have dense : n0=h0.length := by simp [h0,n0,hn]
  obtain ⟨el,rl,ll,runL,repL⟩ := lookup_return repR (boolList_extend word er)
    n0 c rr dense ⟨rr,c,c,rr⟩ 704 frames source
  have t700 : tickNatural program (state heap next a b c d frames source 700)=
      some ⟨state heap next a b c d (⟨701,.r3,⟨a,b,c,d⟩⟩::frames) source 660,[],0⟩ := by
    simp [tickNatural,program,state]
  have t701 : tickNatural program (state h0 n0 a b c rr frames source 701)=
      some ⟨state h0 n0 rr b c rr frames source 702,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t702 : tickNatural program (state h0 n0 rr b c rr frames source 702)=
      some ⟨state h0 n0 rr c c rr frames source 703,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t703 : tickNatural program (state h0 n0 rr c c rr frames source 703)=
      some ⟨state h0 n0 rr c c rr (⟨704,.r3,⟨rr,c,c,rr⟩⟩::frames) source 680,[],0⟩ := by
    simp [tickNatural,program,state]
  have t704 : tickNatural program (state (h0++el) (n0+el.length) rr c c rl frames source 704)=
      some ⟨state (h0++el) (n0+el.length) saved.a saved.b saved.c rl stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨er++el,rl,by simp [minimizeCells,lr,ll],?_,?_⟩
  · have last := NaturalRun.step t701 (.step t702 (.step t703 (run_append runL (.step t704 (.done _)))))
    have joined := NaturalRun.step t700 (run_append runR last)
    convert joined using 1 <;> simp only [minimizeSteps,h0,n0,List.length_append,List.append_assoc,Nat.add_assoc,List.nil_append]
  · simpa only [minimize,h0,List.append_assoc] using repL

end DirectedFlowCutGap.GraphDiscoveryProgram
