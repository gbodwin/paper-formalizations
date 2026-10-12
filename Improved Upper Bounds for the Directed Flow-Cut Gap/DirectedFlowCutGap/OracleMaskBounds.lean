import DirectedFlowCutGap.OracleMaskRefinement

namespace DirectedFlowCutGap.OracleMask
open BinaryArithmetic

def widths (W : ℕ) (es : List (Bits × Bits)) : Prop := ∀ e∈es,e.1.length ≤ W

theorem compare_steps_le {W : ℕ} {u v : Bits} (hu : u.length ≤ W) (hv : v.length ≤ W) :
    BinaryComparisonProgram.steps u v ≤ 32*W+16 := by
  have h := BinaryComparisonProgram.steps_bound u v
  omega

theorem member_steps_le {W : ℕ} {u : Bits} {es : List (Bits × Bits)}
    (hu : u.length ≤ W) (he : widths W es) :
    memberSteps u es ≤ (es.length+1)*(32*W+30) := by
  induction es with
  | nil => simp [memberSteps]
  | cons e es ih =>
    have hh := compare_steps_le (he e (by simp)) hu
    have ht := ih (fun f hf => he f (by simp [hf]))
    simp only [memberSteps,List.length_cons]
    split <;> nlinarith

theorem bit_steps_le {W : ℕ} {s t u : Bits} {es : List (Bits × Bits)}
    (hs : s.length ≤ W) (ht : t.length ≤ W) (hu : u.length ≤ W) (he : widths W es) :
    bitSteps s t u es ≤ (es.length+3)*(32*W+30) := by
  have h1 := compare_steps_le hu hs
  have h2 := compare_steps_le hu ht
  have hm := member_steps_le hu he
  simp only [bitSteps,secondSteps,finishSteps]
  split
  · nlinarith
  · split <;> nlinarith

def instructionBound (vertices edges W : ℕ) : ℕ :=
  (vertices+1)*((edges+3)*(32*W+30)+11)+1

theorem steps_le {W : ℕ} {s t : Bits} {es : List (Bits × Bits)} {vs : List Bits}
    (hs : s.length ≤ W) (ht : t.length ≤ W) (he : widths W es)
    (hv : ∀ u∈vs,u.length ≤ W) : steps s t es vs+1 ≤ instructionBound vs.length es.length W := by
  have bound : steps s t es vs ≤ (vs.length+1)*((es.length+3)*(32*W+30)+11) := by
    induction vs with
    | nil => simp [steps]
    | cons u us ih =>
      have hh := bit_steps_le hs ht (hv u (by simp)) he
      have hh' := ih (fun v h => hv v (by simp [h]))
      simp only [steps,List.length_cons]
      nlinarith
  exact Nat.add_le_add_right bound 1

end DirectedFlowCutGap.OracleMask
