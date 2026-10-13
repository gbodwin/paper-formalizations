import DirectedFlowCutGap.OriginalDispatchSpec

namespace DirectedFlowCutGap.OriginalDispatch
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def tagCell : Option Bool → Cell ℕ
  | none => .nil
  | some b => .flag b

def tagStart : Option Bool → Fin 2140
  | none => 2123
  | some false => 2115
  | some true => 2128

def tagMiddle : Option Bool → Fin 2140
  | none => 2124
  | some false => 2116
  | some true => 2129

theorem tag_return (tag : Option Bool) (heap : NaturalHeap) (next a b c d : ℕ)
    (saved : Registers ℕ) (pc : Fin 2140) (stack : List (Frame ℕ 2140)) (source : Bits) :
    NaturalRun program 3
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (tagStart tag)) []
      (state (heap++[tagCell tag,.pair next d]) (next+2) saved.a saved.b saved.c (next+1) stack source pc) := by
  have t1 : tickNatural program
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (tagStart tag))=
      some ⟨state (heap++[tagCell tag]) (next+1) next b c d
        (⟨pc,.r3,saved⟩::stack) source (tagMiddle tag),[],0⟩ := by
    cases tag with
    | none => simp [tickNatural,program,state,tagStart,tagMiddle,tagCell,allocateNatural,Recipe.cell,Registers.set]
    | some flag => cases flag <;> simp [tickNatural,program,state,tagStart,tagMiddle,tagCell,allocateNatural,Recipe.cell,Registers.set]
  have t2 : tickNatural program
      (state (heap++[tagCell tag]) (next+1) next b c d (⟨pc,.r3,saved⟩::stack) source (tagMiddle tag))=
      some ⟨state (heap++[tagCell tag,.pair next d]) (next+2) next b c (next+1)
        (⟨pc,.r3,saved⟩::stack) source 2117,[],0⟩ := by
    cases tag with
    | none => simp [tickNatural,program,state,tagMiddle,tagCell,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc]
    | some flag => cases flag <;> simp [tickNatural,program,state,tagMiddle,tagCell,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc]
  have t3 : tickNatural program
      (state (heap++[tagCell tag,.pair next d]) (next+2) next b c (next+1)
        (⟨pc,.r3,saved⟩::stack) source 2117)=
      some ⟨state (heap++[tagCell tag,.pair next d]) (next+2) saved.a saved.b saved.c (next+1) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact .step t1 (.step t2 (.step t3 (.done _)))
end DirectedFlowCutGap.OriginalDispatch
