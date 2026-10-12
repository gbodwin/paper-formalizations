import DirectedFlowCutGap.GraphOracleChoiceCall

namespace DirectedFlowCutGap.GraphOracleMachine
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor

def Context {n : ℕ} (heap : NaturalHeap) (root : ℕ) (label : Fin n → Bits)
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (capacity y : Row n) : Prop :=
  ∃ shared post,heap[root]?=some (.pair shared post) ∧
    DemandCollection.Shared heap shared ((ResidualSearch.Enumeration.fin n).vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList ∧
    CapacityBottleneck.GraphContext heap post label capacity

/-- No path, score, selected record or mask is supplied. Both embedded programs
execute on their actual newly allocated outputs in the same controller run. -/
theorem oracle_run {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {a b : ℕ} (input : DemandCollection.DemandList heap a xs)
    (context : Context heap b label adjacency capacity y)
    (next c d : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 2120)) (source : Bits) :
    ∃ steps ext selectedRoot post root,NaturalRun program steps
      (state heap next a b c d stack source 2100) []
      (state (heap++ext) (next+ext.length) selectedRoot post next root stack source 2107) ∧
      OracleChoice.StoredChoice (heap++ext) root label (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn y).1 ∧
      ∀ W,(∀ i,(label i).length≤W) →
        (∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) →
        steps ≤ DemandCollection.selectedSteps ((ResidualSearch.Enumeration.fin n).vertices.map label)
          (GraphRelaxationRefinement.matrix adjacency) y.toList (next+1) xs+
          OracleChoice.instructionBound (BinaryFractionalGraphOracle.selected adjacency y ds).1 W+10 := by
  obtain ⟨shared,post,hb,hs,hp⟩ := context
  let frame : Cell ℕ := .pair a b
  let h1 := heap++[frame]
  have dense1 : next+1=h1.length := by simp [h1,dense]
  obtain ⟨ed,rd,ld,demandRun,selected,_⟩ := demand_return adjacency y label hlabel encoded
    (DemandCollection.demands_extend input [frame]) (DemandCollection.shared_extend hs [frame])
    (next+1) next d dense1 ⟨a,shared,next,d⟩ 2103 stack source
  let n1 := next+1+ed.length
  have dense2 : n1=(h1++ed).length := by simp [n1,h1,dense];omega
  obtain ⟨cs,ec,rc,choiceRun,choiceStored,bound⟩ := choice_return label hlabel capacity hn selected
    (OracleChoice.graph_context_extend (OracleChoice.graph_context_extend hp [frame]) ed)
    n1 next rd dense2 ⟨rd,post,next,rd⟩ 2107 stack source
  have t2100 : tickNatural program (state heap next a b c d stack source 2100)=
      some ⟨state h1 (next+1) a b next d stack source 2101,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1,frame]
  have t2101 : tickNatural program (state h1 (next+1) a b next d stack source 2101)=
      some ⟨state h1 (next+1) a shared next d stack source 2102,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h1,lookup_extend hb [frame]]
  have t2102 : tickNatural program (state h1 (next+1) a shared next d stack source 2102)=
      some ⟨state h1 (next+1) a shared next d (⟨2103,.r3,⟨a,shared,next,d⟩⟩::stack) source 1600,[],0⟩ := by
    simp [tickNatural,program,state]
  have hf : (h1++ed)[next]?=some (.pair a b) := by
    apply lookup_extend (k:=ed)
    simp [h1,frame,dense]
  have t2103 : tickNatural program (state (h1++ed) n1 a shared next rd stack source 2103)=
      some ⟨state (h1++ed) n1 a b next rd stack source 2104,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hf]
  have t2104 : tickNatural program (state (h1++ed) n1 a b next rd stack source 2104)=
      some ⟨state (h1++ed) n1 a post next rd stack source 2105,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hb (frame::ed),h1]
  have t2105 : tickNatural program (state (h1++ed) n1 a post next rd stack source 2105)=
      some ⟨state (h1++ed) n1 rd post next rd stack source 2106,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t2106 : tickNatural program (state (h1++ed) n1 rd post next rd stack source 2106)=
      some ⟨state (h1++ed) n1 rd post next rd (⟨2107,.r3,⟨rd,post,next,rd⟩⟩::stack) source 2084,[],0⟩ := by
    simp [tickNatural,program,state]
  let ext : NaturalHeap := [frame]++ed++ec
  let tailRun := NaturalRun.step t2103 (.step t2104 (.step t2105 (.step t2106 choiceRun)))
  let all := NaturalRun.step t2100 (.step t2101 (.step t2102 (run_append demandRun tailRun)))
  refine ⟨DemandCollection.selectedSteps ((ResidualSearch.Enumeration.fin n).vertices.map label) (GraphRelaxationRefinement.matrix adjacency) y.toList (next+1) xs+cs+8,ext,rd,post,rc,?_,?_,?_⟩
  · convert all using 1 <;> simp [ext,n1,state,List.append_assoc]
    all_goals omega
  · rw [OracleChoice.oracle_choice]
    simpa [ext,h1,List.append_assoc] using choiceStored
  · intro W labels capacities
    have hbnd := bound W labels capacities
    omega

end DirectedFlowCutGap.GraphOracleMachine
