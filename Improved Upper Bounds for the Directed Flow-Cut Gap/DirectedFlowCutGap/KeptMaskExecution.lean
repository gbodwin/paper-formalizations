import DirectedFlowCutGap.KeptMaskTrace

namespace DirectedFlowCutGap.KeptMask
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def wordBits (vs : List Bits) : ℕ := (vs.map List.length).sum

def inputSteps (s t : Bits) (vs : List Bits) : ℕ :=
  32*wordBits vs+(32*(s.length+t.length+2)+25)*vs.length+4

theorem steps_bound (s t : Bits) (vs : List Bits) (zs : Bits) :
    steps s t vs zs+1 ≤ inputSteps s t vs := by
  induction vs generalizing zs with
  | nil => cases zs <;> simp [steps,inputSteps,wordBits]
  | cons u us ih =>
    cases zs with
    | nil => simp [steps,inputSteps]
    | cons z zs =>
      have hk := KeptVertex.keep_steps_bound s t u z
      have hi := ih zs
      simp only [steps,inputSteps,wordBits,List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one] at *
      omega

theorem scan {heap : NaturalHeap} {a b : ℕ} {s t : Bits} {vs : List Bits} {zs : Bits}
    (hv : Vertices heap a vs) (hc : Context heap b s t zs) (aligned : vs.length=zs.length)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 132)) (source : Bits) :
    ∃ ext root,ext.length=cells s t vs zs ∧ NaturalRun program (steps s t vs zs+1)
      (state heap next a b c d stack source 130) []
      (state (heap++ext) (next+ext.length) a b c root stack source 131) ∧
      BoolList (heap++ext) root (mask s t vs zs) := by
  obtain ⟨ext,root,len,run,rep⟩ := mask_return hv hc aligned next c d hn ⟨a,b,c,d⟩ 131 stack source
  have call : tickNatural program (state heap next a b c d stack source 130)=
      some ⟨state heap next a b c d (⟨131,.r3,⟨a,b,c,d⟩⟩::stack) source 100,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step call run,rep⟩

theorem mask_encode {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (s t : Fin n) (vs : List (Fin n)) (zs : Bits) :
    mask (label s) (label t) (vs.map label) zs=
      List.zipWith (fun u zero => !zero || decide (u=s) || decide (u=t)) vs zs := by
  induction vs generalizing zs with
  | nil => cases zs <;> rfl
  | cons u us ih =>
    cases zs with
    | nil => rfl
    | cons z zs => simp only [List.map_cons,mask,List.zipWith_cons_cons,KeptVertex.bit_encode label hlabel,ih]
end DirectedFlowCutGap.KeptMask
