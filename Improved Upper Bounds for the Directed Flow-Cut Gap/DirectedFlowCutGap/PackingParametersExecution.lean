import DirectedFlowCutGap.PackingParametersSpecification

namespace DirectedFlowCutGap.PackingParameters
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation PackedBooleanConstructor
open BooleanTableRead (BoolList)
open CanonicalRationalSum (StoredList)
open RationalComparisonProgram (Stored)

def steps (n : ℕ) : ℕ := BinaryLengthProgram.scanSteps n []+
  CanonicalArithmeticProgram.instructions true (dimensionWord n) (dimensionWord n)+
  CanonicalArithmeticProgram.instructions true [true,true] (squareWord n)+
  CanonicalRationalQuotient.steps two (BinaryFractionalCore.naturalFraction (fuelWord n))+24

set_option maxRecDepth 10000 in
theorem parameters_run {row : List Fraction} {heap : NaturalHeap} {cap : ℕ}
    (input : StoredList heap cap row) (next b c d : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ ext, ∃ out : NaturalState 360,
      NaturalRun program (steps row.length) (state heap next cap b c d [] source 310) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=[] ∧ out.source=source ∧ out.pc=328 ∧
      ∃ delta fuel, out.heap[out.registers.d]?=some (.pair delta fuel) ∧
        Stored out.heap delta (deltaValue row.length) ∧ BoolList out.heap fuel (fuelWord row.length) := by
  obtain ⟨eD,dim,_,dimRun,dimRep⟩ := dimension_return input next b c d dense ⟨cap,b,c,d⟩ 311 [] source
  let hD := heap++eD
  let nD := next+eD.length
  obtain ⟨eS,square,squareRun,squareRep⟩ := arithmetic_return dimRep dimRep nD c d
    (by simp [nD,dense]) .r1 ⟨dim,dim,c,d⟩ 313 [] source
  let hS := hD++eS
  let nS := nD+eS.length
  let e3 : NaturalHeap := [.nil,.flag true,.pair (nS+1) nS,.pair (nS+1) (nS+2)]
  have ⟨threeRun,threeRep⟩ := three_prefix hS nS dim square c d (by simp [hS,hD,nS,nD,dense,Nat.add_assoc]) source
  obtain ⟨eF,fuel,fuelRun,fuelRep⟩ := arithmetic_return threeRep (boolList_extend squareRep e3) (nS+4) c (nS+1)
    (by simp [hS,hD,nS,nD,dense,Nat.add_assoc]) .r3 ⟨nS+3,square,c,nS+1⟩ 318 [] source
  let hF := (hS++e3)++eF
  let nF := nS+4+eF.length
  let e2 : NaturalHeap := [.nil,.flag true,.pair (nF+1) nF,.pair fuel (nF+2),
      .flag false,.pair (nF+4) (nF+2),.pair (nF+5) (nF+2)]
  have ⟨twoRun,twoRep,naturalRep⟩ := two_prefix fuelRep nF (nS+3) square c
    (by simp only [nF,hS,hD,nS,nD,dense,List.length_append,List.length_cons,List.length_nil]) source
  obtain ⟨eQ,delta,quotientRun,deltaRep⟩ := quotient_return two (BinaryFractionalCore.naturalFraction (fuelWord row.length))
    twoRep naturalRep (nF+7) fuel (nF+5)
    (by simp only [nF,hS,hD,nS,nD,dense,List.length_append,List.length_cons,List.length_nil]) ⟨nF+6,nF+3,fuel,nF+5⟩ 327 [] source
  let hQ := (hF++e2)++eQ
  let nQ := nF+7+eQ.length
  have t0 : tickNatural program (state heap next cap b c d [] source 310)=
      some ⟨state heap next cap b c d [⟨311,.r0,⟨cap,b,c,d⟩⟩] source 16,[],0⟩ := by
    simp [program,tickNatural,state]
  have t1 : tickNatural program (state hD nD dim b c d [] source 311)=
      some ⟨state hD nD dim dim c d [] source 312,[],0⟩ := by
    simp [program,tickNatural,state,Registers.set,Registers.get]
  have t2 : tickNatural program (state hD nD dim dim c d [] source 312)=
      some ⟨state hD nD dim dim c d [⟨313,.r1,⟨dim,dim,c,d⟩⟩] source 134,[],0⟩ := by
    simp [program,tickNatural,state]
  have t3 : tickNatural program (state (hS++e3) (nS+4) (nS+3) square c (nS+1) [] source 317)=
      some ⟨state (hS++e3) (nS+4) (nS+3) square c (nS+1) [⟨318,.r3,⟨nS+3,square,c,nS+1⟩⟩] source 134,[],0⟩ := by
    simp [program,tickNatural,state]
  have t4 : tickNatural program (state (hF++e2) (nF+7) (nF+6) (nF+3) fuel (nF+5) [] source 326)=
      some ⟨state (hF++e2) (nF+7) (nF+6) (nF+3) fuel (nF+5) [⟨327,.r3,⟨nF+6,nF+3,fuel,nF+5⟩⟩] source 301,[],0⟩ := by
    simp [program,tickNatural,state]
  have t5 : tickNatural program (state hQ nQ (nF+6) (nF+3) fuel delta [] source 327)=
      some ⟨state (hQ++[.pair delta fuel]) (nQ+1) (nF+6) (nF+3) fuel nQ [] source 328,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get]
  refine ⟨eD++eS++e3++eF++e2++eQ++[.pair delta fuel],
    state (hQ++[.pair delta fuel]) (nQ+1) (nF+6) (nF+3) fuel nQ [] source 328,?_,?_,?_,rfl,rfl,rfl,delta,fuel,?_,?_,?_⟩
  · have rQ := run_append quotientRun (.step t5 (.done _))
    have r2 := run_append twoRun (.step t4 rQ)
    have rF := run_append fuelRun r2
    have r3 := run_append threeRun (.step t3 rF)
    have rS := run_append squareRun r3
    have rD := run_append dimRun (.step t1 (.step t2 rS))
    convert NaturalRun.step t0 rD using 1
    · dsimp only [steps,dimensionWord,squareWord,fuelWord]
      omega
    · rfl
  · simp [state,hQ,hF,hS,hD,List.append_assoc]
  · simp only [state,nQ,nF,nS,nD,e2,e3,List.length_append,List.length_cons,List.length_nil]
    omega
  · have hnQ : nQ=hQ.length := by
      simp only [hQ,hF,hS,hD,nQ,nF,nS,nD,e3,e2,dense,List.length_append,List.length_cons,List.length_nil]
    simp [state,hnQ]
  · exact RationalComparisonProgram.stored_extend deltaRep [.pair delta fuel]
  · exact boolList_extend (boolList_extend (boolList_extend fuelRep e2) eQ) [.pair delta fuel]
end DirectedFlowCutGap.PackingParameters
