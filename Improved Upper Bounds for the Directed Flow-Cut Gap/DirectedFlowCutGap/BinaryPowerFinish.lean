import DirectedFlowCutGap.BinaryPowerCalls
namespace DirectedFlowCutGap.BinaryPowerProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def runSteps : ℕ → NaturalState 96 → Option (NaturalState 96)
  | 0,s => some s
  | n+1,s => (tickNatural program s).bind fun r => runSteps n r.state

theorem runSteps_sound {n : ℕ} {s out : NaturalState 96}
    (h : runSteps n s=some out) : ∃ ev,NaturalRun program n s ev out := by
  induction n generalizing s out with
  | zero => simp only [runSteps,Option.some.injEq] at h;subst out;exact ⟨[],.done _⟩
  | succ n ih =>
    simp only [runSteps] at h
    cases ht : tickNatural program s with
    | none => simp [ht] at h
    | some r =>
      simp only [ht,Option.bind_some] at h
      obtain ⟨ev,run⟩ := ih h
      exact ⟨r.events++ev,.step ht run⟩

-- Literal finish blocks emit no events; the explicit ticks below retain that fact.
theorem one_return (heap : NaturalHeap) (next a b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 96) (stack : List (Frame ℕ 96)) (source : Bits) :
    let ext : NaturalHeap := [.flag true,.nil,.pair next (next+1)]
    NaturalRun program 4 (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 78) []
      (state (heap++ext) (next+3) saved.a saved.b saved.c (next+2) stack source pc) ∧
    BoolList (heap++ext) (next+2) [true] := by
  dsimp only
  let frames := ⟨pc,.r3,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 78)=
      some ⟨state (heap++[.flag true]) (next+1) a b next d frames source 79,[],0⟩ := by rfl
  have t1 : tickNatural program (state (heap++[.flag true]) (next+1) a b next d frames source 79)=
      some ⟨state (heap++[.flag true,.nil]) (next+2) a b next (next+1) frames source 80,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,List.append_assoc,Nat.add_assoc]
  have t2 : tickNatural program (state (heap++[.flag true,.nil]) (next+2) a b next (next+1) frames source 80)=
      some ⟨state (heap++[.flag true,.nil,.pair next (next+1)]) (next+3) a b next (next+2) frames source 90,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc,Nat.add_assoc]
  have t3 : tickNatural program (state (heap++[.flag true,.nil,.pair next (next+1)]) (next+3) a b next (next+2) frames source 90)=
      some ⟨state (heap++[.flag true,.nil,.pair next (next+1)]) (next+3) saved.a saved.b saved.c (next+2) stack source pc,[],0⟩ := by
    simp [program,tickNatural,state,frames,Registers.get,Registers.set]
  refine ⟨.step t0 (.step t1 (.step t2 (.step t3 (.done _)))),?_⟩
  exact .cons (head:=next) (tail:=next+1) (by simp [dense]) (by simp [dense]) (.nil (by simp [dense]))

theorem shift_return {heap : NaturalHeap} {word : Bits} {d : ℕ}
    (rep : BoolList heap d word) (next a b c : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 96) (stack : List (Frame ℕ 96)) (source : Bits) :
    let ext : NaturalHeap := [.flag false,.pair next d]
    NaturalRun program 3 (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 84) []
      (state (heap++ext) (next+2) saved.a saved.b saved.c (next+1) stack source pc) ∧
    BoolList (heap++ext) (next+1) (false::word) := by
  dsimp only
  let frames := ⟨pc,.r3,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 84)=
      some ⟨state (heap++[.flag false]) (next+1) a b next d frames source 85,[],0⟩ := by rfl
  have t1 : tickNatural program (state (heap++[.flag false]) (next+1) a b next d frames source 85)=
      some ⟨state (heap++[.flag false,.pair next d]) (next+2) a b next (next+1) frames source 90,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc,Nat.add_assoc]
  have t2 : tickNatural program (state (heap++[.flag false,.pair next d]) (next+2) a b next (next+1) frames source 90)=
      some ⟨state (heap++[.flag false,.pair next d]) (next+2) saved.a saved.b saved.c (next+1) stack source pc,[],0⟩ := by
    simp [program,tickNatural,state,frames,Registers.get,Registers.set]
  refine ⟨.step t0 (.step t1 (.step t2 (.done _))),?_⟩
  exact .cons (head:=next) (tail:=d) (by simp [dense]) (by simp [dense]) (boolList_extend rep _)
end DirectedFlowCutGap.BinaryPowerProgram
