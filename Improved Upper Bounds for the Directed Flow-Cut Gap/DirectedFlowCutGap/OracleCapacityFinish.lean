import DirectedFlowCutGap.OracleCapacityCall

namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor

def finishSteps {n : ℕ} : Option (Fin n) → ℕ
  | none => 8
  | some _ => 5

/-- Both actual bottleneck branches allocate the final mask/vertex choice.
The empty-bottleneck branch follows the original enumeration to its zero word. -/
theorem finish_return {n : ℕ} (label : Fin n → Bits) (capacity : Row n) (mask : Vector Bool n)
    (zero : Fin n) {heap : NaturalHeap} {a b c d frame selected vertices table maskRoot zeroRoot tail : ℕ}
    {result : Option (Fin n)}
    (hc : heap[c]?=some (.pair frame maskRoot)) (hf : heap[frame]?=some (.pair selected b))
    (hb : heap[b]?=some (.pair vertices table)) (hv : heap[vertices]?=some (.pair zeroRoot tail))
    (hzero : BoolList heap zeroRoot (label zero)) (hm : BoolList heap maskRoot mask.toList)
    (output : CapacityBottleneck.Output heap d label capacity result)
    (next : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 484)
    (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ ext,ext.length=1 ∧ NaturalRun program (finishSteps result)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 425) []
      (state (heap++ext) (next+1) saved.a saved.b saved.c next stack source pc) ∧
      StoredChoice (heap++ext) next label ⟨mask,result.getD zero⟩ := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  cases result with
  | none =>
    have hd : heap[d]?=some .nil := output
    have t425 : tickNatural program (state heap next a b c d frames source 425)=
        some ⟨state heap next a b c d frames source 426,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,hd]
    have t426 : tickNatural program (state heap next a b c d frames source 426)=
        some ⟨state heap next frame b c d frames source 427,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hc]
    have t427 : tickNatural program (state heap next frame b c d frames source 427)=
        some ⟨state heap next b b c d frames source 428,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hf]
    have t428 : tickNatural program (state heap next b b c d frames source 428)=
        some ⟨state heap next vertices b c d frames source 429,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hb]
    have t429 : tickNatural program (state heap next vertices b c d frames source 429)=
        some ⟨state heap next zeroRoot b c d frames source 430,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hv]
    have t430 : tickNatural program (state heap next zeroRoot b c d frames source 430)=
        some ⟨state heap next zeroRoot maskRoot c d frames source 431,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hc]
    have t431 : tickNatural program (state heap next zeroRoot maskRoot c d frames source 431)=
        some ⟨state (heap++[.pair maskRoot zeroRoot]) (next+1) zeroRoot maskRoot c next frames source 440,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
    have t440 : tickNatural program (state (heap++[.pair maskRoot zeroRoot]) (next+1) zeroRoot maskRoot c next frames source 440)=
        some ⟨state (heap++[.pair maskRoot zeroRoot]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,frames]
    refine ⟨[.pair maskRoot zeroRoot],rfl,?_,?_⟩
    · exact .step t425 (.step t426 (.step t427 (.step t428 (.step t429 (.step t430 (.step t431 (.step t440 (.done _))))))))
    · refine ⟨maskRoot,zeroRoot,?_,boolList_extend hm _,?_⟩
      · simp [hn]
      · exact boolList_extend hzero _
  | some i =>
    obtain ⟨score,word,hd,_,hw⟩ := output
    have t425 : tickNatural program (state heap next a b c d frames source 425)=
        some ⟨state heap next a b c d frames source 432,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,hd]
    have t432 : tickNatural program (state heap next a b c d frames source 432)=
        some ⟨state heap next word b c d frames source 433,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hd]
    have t433 : tickNatural program (state heap next word b c d frames source 433)=
        some ⟨state heap next word maskRoot c d frames source 434,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hc]
    have t434 : tickNatural program (state heap next word maskRoot c d frames source 434)=
        some ⟨state (heap++[.pair maskRoot word]) (next+1) word maskRoot c next frames source 440,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
    have t440 : tickNatural program (state (heap++[.pair maskRoot word]) (next+1) word maskRoot c next frames source 440)=
        some ⟨state (heap++[.pair maskRoot word]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,frames]
    refine ⟨[.pair maskRoot word],rfl,?_,?_⟩
    · exact .step t425 (.step t432 (.step t433 (.step t434 (.step t440 (.done _)))))
    · refine ⟨maskRoot,word,?_,boolList_extend hm _,?_⟩
      · simp [hn]
      · exact boolList_extend hw _

end DirectedFlowCutGap.OracleChoice
