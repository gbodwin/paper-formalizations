import DirectedFlowCutGap.PackingStartInput

namespace DirectedFlowCutGap.PackingStart
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem initial_oracle {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (delta : Fraction) (label : Fin n → Bits)
    (hlabel : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {a b c : ℕ}
    (row : StoredList heap a capacity.toList) (scalar : Stored heap b delta)
    (input : Input heap c label adjacency capacity xs)
    (next d : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ oracleSteps ext demands context frame weights choice,
      NaturalRun program (ScalarQuotientRow.steps true delta capacity.toList+oracleSteps+25)
        (state heap next a b c d [] source 3020) []
        (state (heap++ext) (next+ext.length) demands context frame choice [] source 3033) ∧
      WeightFrame (heap++ext) frame a c weights ∧
      StoredList (heap++ext) weights (initial capacity delta).1.toList ∧
      OracleChoice.StoredChoice (heap++ext) choice label
        (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn (initial capacity delta).1).1 ∧
      ∀ W,1≤W → (∀ i,(label i).length≤W) →
        (∀ q∈(initial capacity delta).1.toList,StoredBounded q W) →
        (∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) →
        oracleSteps ≤ GraphOracleMachine.instructionBound ds.length n W+1 := by
  obtain ⟨dr,mr,hinput,demandsRep,staticRep⟩ := input
  let e0 : NaturalHeap := [.pair a c]
  let h0 := heap++e0
  let n0 := next+1
  have dense0 : n0=h0.length := by simp [n0,h0,e0,dense]
  obtain ⟨ei,ri,_,initRun,initRep⟩ := initial_return delta (list_extend row e0) (stored_extend scalar e0)
    n0 next d dense0 ⟨a,b,next,d⟩ 3022 [] source
  let h1 := h0++ei
  let n1 := n0+ei.length
  have dense1 : n1=h1.length := by simp [n1,h1,dense0]
  let e1 : NaturalHeap := [.pair ri next]
  let h2 := h1++e1
  let n2 := n1+1
  have dense2 : n2=h2.length := by simp [n2,h2,e1,dense1]
  have weights2 : StoredList h2 ri (initial capacity delta).1.toList := by
    rw [←ScalarQuotientRow.result_eq_initial]
    exact list_extend initRep e1
  have static2 := static_extend (static_extend (static_extend staticRep e0) ei) e1
  obtain ⟨ec,rc,_,contextRun,contextRep⟩ := context_return label adjacency capacity (initial capacity delta).1
    weights2 static2 n2 n1 ri dense2 ⟨ri,mr,n1,ri⟩ 3028 [] source
  let h3 := h2++ec
  let n3 := n2+ec.length
  have dense3 : n3=h3.length := by simp [n3,h3,dense2]
  have demands3 := DemandCollection.demands_extend
    (DemandCollection.demands_extend (DemandCollection.demands_extend
      (DemandCollection.demands_extend demandsRep e0) ei) e1) ec
  obtain ⟨ot,eo,rq,oracleRun,choiceRep,bound⟩ := oracle_return adjacency capacity (initial capacity delta).1
    label hlabel hn encoded demands3 contextRep n3 n1 rc dense3 ⟨dr,rc,n1,rc⟩ 3033 [] source
  let h4 := h3++eo
  let ext := e0++ei++e1++ec++eo
  have heaps : heap++ext=h4 := by simp [ext,h4,h3,h2,h1,h0,List.append_assoc]
  have sizes : next+ext.length=n3+eo.length := by simp [ext,e0,e1,n3,n2,n1,n0];omega
  have pair0 : h2[next]?=some (.pair a c) := by
    apply lookup_extend (h:=h1)
    apply lookup_extend (h:=h0)
    simp [h0,e0,dense]
  have pair1 : h2[n1]?=some (.pair ri next) := by simp [h2,e1,dense1]
  have inp2 : h2[c]?=some (.pair dr mr) := lookup_extend (lookup_extend (lookup_extend hinput e0) ei) e1
  have t3020 : tickNatural program (state heap next a b c d [] source 3020)=
      some ⟨state h0 n0 a b next d [] source 3021,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h0,n0,e0]
  have t3021 : tickNatural program (state h0 n0 a b next d [] source 3021)=
      some ⟨state h0 n0 a b next d [⟨3022,.r3,⟨a,b,next,d⟩⟩] source 180,[],0⟩ := by
    simp [tickNatural,program,state]
  have t3022 : tickNatural program (state h1 n1 a b next ri [] source 3022)=
      some ⟨state h2 n2 a b n1 ri [] source 3023,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h2,n2,e1]
  have t3023 : tickNatural program (state h2 n2 a b n1 ri [] source 3023)=
      some ⟨state h2 n2 ri b n1 ri [] source 3024,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t3024 : tickNatural program (state h2 n2 ri b n1 ri [] source 3024)=
      some ⟨state h2 n2 ri next n1 ri [] source 3025,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair1]
  have t3025 : tickNatural program (state h2 n2 ri next n1 ri [] source 3025)=
      some ⟨state h2 n2 ri c n1 ri [] source 3026,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair0]
  have t3026 : tickNatural program (state h2 n2 ri c n1 ri [] source 3026)=
      some ⟨state h2 n2 ri mr n1 ri [] source 3027,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,inp2]
  have t3027 : tickNatural program (state h2 n2 ri mr n1 ri [] source 3027)=
      some ⟨state h2 n2 ri mr n1 ri [⟨3028,.r3,⟨ri,mr,n1,ri⟩⟩] source 190,[],0⟩ := by
    simp [tickNatural,program,state]
  have t3028 : tickNatural program (state h3 n3 ri mr n1 rc [] source 3028)=
      some ⟨state h3 n3 ri rc n1 rc [] source 3029,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t3029 : tickNatural program (state h3 n3 ri rc n1 rc [] source 3029)=
      some ⟨state h3 n3 next rc n1 rc [] source 3030,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h3,lookup_extend pair1 ec]
  have t3030 : tickNatural program (state h3 n3 next rc n1 rc [] source 3030)=
      some ⟨state h3 n3 c rc n1 rc [] source 3031,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h3,lookup_extend pair0 ec]
  have t3031 : tickNatural program (state h3 n3 c rc n1 rc [] source 3031)=
      some ⟨state h3 n3 dr rc n1 rc [] source 3032,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h3,lookup_extend inp2 ec]
  have t3032 : tickNatural program (state h3 n3 dr rc n1 rc [] source 3032)=
      some ⟨state h3 n3 dr rc n1 rc [⟨3033,.r3,⟨dr,rc,n1,rc⟩⟩] source 2292,[],0⟩ := by
    simp [tickNatural,program,state]
  have tailRun := NaturalRun.step t3028 (.step t3029 (.step t3030 (.step t3031 (.step t3032 oracleRun))))
  have middle := NaturalRun.step t3022 (.step t3023 (.step t3024 (.step t3025 (.step t3026 (.step t3027
    (run_append contextRun tailRun))))))
  have whole := NaturalRun.step t3020 (.step t3021 (run_append initRun middle))
  refine ⟨ot,ext,dr,rc,n1,ri,rq,?_,?_,?_,?_,bound⟩
  · rw [heaps,sizes]
    convert whole using 1
    · omega
    · rfl
  · rw [heaps]
    exact weight_frame_extend (weight_frame_extend ⟨next,pair1,pair0⟩ ec) eo
  · rw [heaps];exact list_extend (list_extend weights2 ec) eo
  · rw [heaps];exact choiceRep
end DirectedFlowCutGap.PackingStart
