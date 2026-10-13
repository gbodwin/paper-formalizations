import DirectedFlowCutGap.KeptAdjacencyRowTrace

namespace DirectedFlowCutGap.KeptAdjacencyRow
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem steps_bound (keep : Bool) (adj kept : Bits) : steps keep adj kept+1 ≤ 24*adj.length+4 := by
  induction adj generalizing kept with
  | nil => cases kept <;> simp [steps]
  | cons a adj ih =>
    cases kept with
    | nil => simp [steps]
    | cons k kept =>
      have h := ih kept
      have hk : (if a then if keep then 24 else 21 else 19) ≤ 24 := by
        cases a <;> cases keep <;> decide
      simp only [steps,List.length_cons,Nat.mul_add,Nat.mul_one]
      omega

theorem scan {heap : NaturalHeap} {a b : ℕ} {adj kept : Bits} {keep : Bool}
    (ha : BoolList heap a adj) (hc : Context heap b keep kept) (aligned : adj.length=kept.length)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 36)) (source : Bits) :
    ∃ ext root,ext.length=5*adj.length+1 ∧ NaturalRun program (steps keep adj kept+1)
      (state heap next a b c d stack source 34) []
      (state (heap++ext) (next+ext.length) a b c root stack source 35) ∧
      BoolList (heap++ext) root (row keep adj kept) := by
  obtain ⟨ext,root,len,run,rep⟩ := row_return ha hc aligned next c d hn ⟨a,b,c,d⟩ 35 stack source
  have call : tickNatural program (state heap next a b c d stack source 34)=
      some ⟨state heap next a b c d (⟨35,.r3,⟨a,b,c,d⟩⟩::stack) source 0,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step call run,rep⟩

theorem row_zip (keep : Bool) (adj kept : Bits) :
    row keep adj kept=List.zipWith (fun a k => a && keep && k) adj kept := by
  induction adj generalizing kept with
  | nil => cases kept <;> rfl
  | cons a adj ih => cases kept <;> simp [row,ih]
end DirectedFlowCutGap.KeptAdjacencyRow
