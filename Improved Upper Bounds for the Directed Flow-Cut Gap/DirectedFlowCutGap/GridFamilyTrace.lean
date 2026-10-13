import DirectedFlowCutGap.GridFamilyHead
import DirectedFlowCutGap.GridFamilyAdvance
import DirectedFlowCutGap.GridFamilySpecification

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
set_option maxRecDepth 32768

theorem loop_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c : ℕ} {exponent fuel : Bits}
    (context : Context heap a adjacency costs xs) (exp : BoolList heap b exponent)
    (input : BoolList heap c fuel) (next d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (destination : Reg) (pc : Fin 10180)
    (stack : List (Frame ℕ 10180)) (source : Bits) :
    ∃ k ext root,k ≤ instructionBound ds.length costs.toList exponent fuel ∧
      NaturalRun program k (state heap next a b c d (⟨pc,destination,saved⟩::stack) source 10130) []
        ⟨heap++ext,next+ext.length,saved.set destination root,stack,pc,source⟩ ∧
      StateList (heap++ext) root (values adjacency ds costs exponent fuel) := by
  induction exponent, fuel using instructionBound.induct
      generalizing heap a b c next d saved destination pc stack with
  | case1 exponent fuel hz =>
    obtain ⟨run,rep⟩ := empty_return n input hz next a b d dense saved destination pc stack source
    refine ⟨BinaryZeroProgram.steps fuel+9,[.flag true,.nil],next+1,?_,?_,?_⟩
    · rw [instructionBound];simp [hz]
    · simpa using run
    · simpa [values,hz] using rep
  | case2 exponent fuel hz ih =>
    have nz : (isZero fuel).1=false := by cases h : (isZero fuel).1 <;> simp_all
    let frame : Frame ℕ 10180 := ⟨pc,destination,saved⟩
    obtain ⟨kh,eh,head,bh,rh,headRep⟩ := head_run adjacency costs encoded context exp input nz
      next d dense (frame::stack) source
    obtain ⟨ea,er,fr,ra,expRep,fuelRep⟩ := advance_run (boolList_extend exp eh) (boolList_extend input eh)
      (next+eh.length) a head (by simp [dense]) (frame::stack) source
    let H := (heap++eh)++ea
    let N := next+eh.length+ea.length
    have nd : N=H.length := by simp [N,H,dense,Nat.add_assoc]
    have cx : Context H a adjacency costs xs := context_extend (context_extend context eh) ea
    obtain ⟨kt,et,tail,bt,rt,tailRep⟩ := ih cx expRep fuelRep N head nd
      ⟨a,er,fr,head⟩ .r2 10136 (frame::stack)
    have t0 : tickNatural program (state H N a er fr head (frame::stack) source 10135)=
      some ⟨state H N a er fr head (⟨10136,.r2,⟨a,er,fr,head⟩⟩::frame::stack) source 10130,[],0⟩ := by rfl
    have rt' : NaturalRun program kt
        (state H N a er fr head (⟨10136,.r2,⟨a,er,fr,head⟩⟩::frame::stack) source 10130) []
        (state (H++et) (N+et.length) a er tail head (frame::stack) source 10136) := by
      simpa [state,Registers.set] using rt
    have t1 : tickNatural program (state (H++et) (N+et.length) a er tail head (frame::stack) source 10136)=
      some ⟨state ((H++et)++[.pair head tail]) (N+et.length+1) a er tail (N+et.length)
        (frame::stack) source 10137,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,allocateNatural,Recipe.cell,Registers.set]
    have t2 : tickNatural program
        (state ((H++et)++[.pair head tail]) (N+et.length+1) a er tail (N+et.length) (frame::stack) source 10137)=
      some ⟨⟨(H++et)++[.pair head tail],N+et.length+1,saved.set destination (N+et.length),stack,pc,source⟩,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,frame]
    have represented : StateList ((H++et)++[.pair head tail]) (N+et.length)
        (MinimumGuess.result adjacency ds costs exponent::values adjacency ds costs
          (increment true exponent).1 (predecessor fuel).1) := by
      apply StateList.cons (head:=head) (tail:=tail) (by simp [nd])
      · exact result_extend (result_extend (result_extend headRep ea) et) [.pair head tail]
      · exact list_extend tailRep [.pair head tail]
    refine ⟨kh+(BinaryIncrementProgram.steps exponent+BinaryPredecessorProgram.steps fuel+12)+(1+(kt+2)),
      eh++ea++et++[.pair head tail],N+et.length,?_,?_,?_⟩
    · rw [instructionBound];simp only [nz, Bool.false_eq_true, ↓reduceDIte]
      omega
    · have whole := run_append rh (run_append ra (.step t0 (run_append rt' (.step t1 (.step t2 (.done _))))))
      convert whole using 1 <;> simp [H,N,List.append_assoc,Nat.add_assoc]
      all_goals omega
    · rw [values]
      simp only [nz, Bool.false_eq_true, ↓reduceDIte]
      simpa [H,List.append_assoc] using represented
end DirectedFlowCutGap.GridFamily
