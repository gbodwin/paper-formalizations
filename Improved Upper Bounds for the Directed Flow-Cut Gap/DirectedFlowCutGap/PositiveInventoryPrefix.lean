import DirectedFlowCutGap.PositiveInventoryCall
import DirectedFlowCutGap.PositiveInventoryData

namespace DirectedFlowCutGap.PositiveInventory
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

/-- Save the literal aligned list cursors, read the actual numerator pointer,
and run the bit zero test, leaving its returned flag alongside that context. -/
theorem numerator_prefix {heap : NaturalHeap} {a b vh vt cost ct num den : ℕ} {word : Bits}
    (ha : heap[a]?=some (.pair vh vt)) (hb : heap[b]?=some (.pair cost ct))
    (hc : heap[cost]?=some (.pair num den)) (hw : BoolList heap num word)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 48)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps word+7)
      (state heap next a b c d stack source 10) []
      (state (heap++[.pair a b,.flag (isZero word).1]) (next+2)
        num b next (next+1) stack source 18) := by
  let scratch : Cell ℕ := .pair a b
  have t10 : tickNatural program (state heap next a b c d stack source 10)=
      some ⟨state heap next a b c d stack source 14,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,ha,tagBranch]
  have t14 : tickNatural program (state heap next a b c d stack source 14)=
      some ⟨state (heap++[scratch]) (next+1) a b next d stack source 15,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,scratch]
  have hb0 := lookup_extend hb [scratch]
  have hc0 := lookup_extend hc [scratch]
  have t15 : tickNatural program (state (heap++[scratch]) (next+1) a b next d stack source 15)=
      some ⟨state (heap++[scratch]) (next+1) cost b next d stack source 16,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
  have t16 : tickNatural program (state (heap++[scratch]) (next+1) cost b next d stack source 16)=
      some ⟨state (heap++[scratch]) (next+1) num b next d stack source 17,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hc0]
  have t17 : tickNatural program (state (heap++[scratch]) (next+1) num b next d stack source 17)=
      some ⟨state (heap++[scratch]) (next+1) num b next d
        (⟨18,.r3,⟨num,b,next,d⟩⟩::stack) source 7,[],0⟩ := by rfl
  have zero := zero_return (boolList_extend hw [scratch]) (next+1) b next d (by simp [hn])
    ⟨num,b,next,d⟩ .r3 18 stack source
  convert NaturalRun.step t10 (.step t14 (.step t15 (.step t16 (.step t17 zero)))) using 1 <;>
    simp [state,scratch,Registers.set,List.append_assoc,Nat.add_assoc]
end DirectedFlowCutGap.PositiveInventory
