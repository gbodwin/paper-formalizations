import OnlineReachabilityPreservers.SeparatorWork
import OnlineReachabilityPreservers.SteinerThinCover

/-! Search inspections across the complete fractional thin-demand run. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Inspect the metered separator and, when it succeeds, rebuild the
interval and filter its outgoing cut for the charge update. -/
def thinSeparatorWorkBound (n m : ℕ) : ℕ :=
  m*residualStepWorkBound n+(2*n^2+n*n^2)+(2*n*m+m)+(2*n*m+2*m)

def thinCoverLoopWithSearchWork (G : Arcs V) (d : V × V) :
    ℕ → CutLoads V → (CutLoads V × ℕ) × ℕ
  | 0, load => ((load, 0), 0)
  | k+1, load =>
    let step := fastThinViolationWithSearchWork G d load
    match step.1 with
    | none => ((load, 0), step.2)
    | some W =>
      let n := Fintype.card V
      let m := G.card
      let cut := outgoingCut (intervalArcs G d) W
      let rest := thinCoverLoopWithSearchWork G d k (doubleCut cut load)
      ((rest.1.1, rest.1.2+1), step.2+(2*n*m+2*m)+rest.2)

theorem thinCoverLoopWithSearchWork_spec (G : Arcs V) (d : V × V) (fuel : ℕ) (load : CutLoads V) :
    let out := thinCoverLoopWithSearchWork G d fuel load
    out.1 = thinCoverLoop G d fuel load ∧
      out.2 ≤ (out.1.2+1)*thinSeparatorWorkBound (Fintype.card V) G.card := by
  induction fuel generalizing load with
  | zero => simp [thinCoverLoopWithSearchWork, thinCoverLoop]
  | succ k ih =>
    let n := Fintype.card V
    let m := G.card
    let B := thinSeparatorWorkBound n m
    let step := fastThinViolationWithSearchWork G d load
    obtain ⟨same, bound⟩ := fastThinViolationWithSearchWork_spec G d load
    change step.1 = fastThinViolation G d load at same
    change step.2 ≤ m*residualStepWorkBound n+(2*n^2+n*n^2)+(2*n*m+m) at bound
    have full : step.2+(2*n*m+2*m) ≤ B := Nat.add_le_add_right bound _
    cases h : step.1 with
    | none =>
      have plain : fastThinViolation G d load = none := same.symm.trans h
      change (fastThinViolationWithSearchWork G d load).1 = none at h
      simp only [thinCoverLoopWithSearchWork, h, thinCoverLoop, plain, true_and, Nat.zero_add, Nat.one_mul]
      exact (Nat.le_add_right _ _).trans full
    | some W =>
      have plain : fastThinViolation G d load = some W := same.symm.trans h
      let cut := outgoingCut (intervalArcs G d) W
      let next := doubleCut cut load
      let tail := thinCoverLoopWithSearchWork G d k next
      obtain ⟨tailSame, tailWork⟩ := ih next
      change tail.1 = _ at tailSame
      change tail.2 ≤ (tail.1.2+1)*B at tailWork
      change (fastThinViolationWithSearchWork G d load).1 = some W at h
      simp only [thinCoverLoopWithSearchWork, h, thinCoverLoop, plain]
      change (tail.1.1, tail.1.2+1) = _ ∧ step.2+(2*n*m+2*m)+tail.2 ≤ (tail.1.2+1+1)*B
      refine ⟨?_, (Nat.add_le_add full tailWork).trans_eq (by ring)⟩
      rw [← tailSame]

private def thinCoverRunWithSearchWorkFrom (G : Arcs V) :
    List (V × V) → CutLoads V → (CutLoads V × ℕ) × ℕ
  | [], load => ((load, 0), 0)
  | d :: D, load =>
    let step := thinCoverLoopWithSearchWork G d (G.card*(G.card.log2+1)+1) load
    let remain := thinCoverRunWithSearchWorkFrom G D step.1.1
    ((remain.1.1, step.1.2+remain.1.2), step.2+remain.2)

private theorem thinCoverRunWithSearchWorkFrom_spec (G : Arcs V) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2)
    (load : CutLoads V) (cap : ∀ e ∈ G, load e ≤ G.card.log2+1) :
    let out := thinCoverRunWithSearchWorkFrom G D load
    out.1.1 = D.foldl (fun l d => thinCoverStep G d l) load ∧
      (∀ e ∈ G, out.1.1 e ≤ G.card.log2+1) ∧
      loadTotal G load+out.1.2 ≤ loadTotal G out.1.1 ∧
      out.2 ≤ (D.length+out.1.2)*thinSeparatorWorkBound (Fintype.card V) G.card := by
  induction D generalizing load with
  | nil => exact ⟨rfl, cap, by simp [thinCoverRunWithSearchWorkFrom], by simp [thinCoverRunWithSearchWorkFrom]⟩
  | cons d D ih =>
    let fuel := G.card*(G.card.log2+1)+1
    let step := thinCoverLoopWithSearchWork G d fuel load
    let rest := thinCoverRunWithSearchWorkFrom G D step.1.1
    let B := thinSeparatorWorkBound (Fintype.card V) G.card
    have reach := feasible d List.mem_cons_self
    obtain ⟨same, firstWork⟩ := thinCoverLoopWithSearchWork_spec G d fuel load
    change step.1 = thinCoverLoop G d fuel load at same
    change step.2 ≤ (step.1.2+1)*B at firstWork
    have thin : step.1.1 = thinCoverStep G d load := congrArg Prod.fst same
    have cap' : ∀ e ∈ G, step.1.1 e ≤ G.card.log2+1 :=
      thin.symm ▸ (thinCoverStep_spec G G (Subset.rfl) d reach load cap).2.1
    have adds : loadTotal G load+step.1.2 ≤ loadTotal G step.1.1 := by
      rw [same]
      exact thinCoverLoop_load_progress G G (Subset.rfl) d reach fuel load cap
    obtain ⟨out, outCap, outAdds, outWork⟩ := ih (fun q hq => feasible q (List.mem_cons_of_mem _ hq)) step.1.1 cap'
    change rest.1.1 = _ at out
    change loadTotal G step.1.1 + rest.1.2 ≤ loadTotal G rest.1.1 at outAdds
    change rest.2 ≤ (D.length+rest.1.2)*B at outWork
    change rest.1.1 = D.foldl (fun l d => thinCoverStep G d l) (thinCoverStep G d load) ∧
      (∀ e ∈ G, rest.1.1 e ≤ G.card.log2+1) ∧
      loadTotal G load+(step.1.2+rest.1.2) ≤ loadTotal G rest.1.1 ∧
      step.2+rest.2 ≤ ((d::D).length+(step.1.2+rest.1.2))*B
    refine ⟨out.trans (congrArg (D.foldl (fun l d => thinCoverStep G d l)) thin), outCap, by omega, ?_⟩
    exact (Nat.add_le_add firstWork outWork).trans_eq (by simp only [List.length_cons]; ring)

/-- Return the actual fractional loads, cut updates and search inspections. -/
def thinCoverRunWithSearchWork (G : Arcs V) (D : List (V × V)) : (CutLoads V × ℕ) × ℕ :=
  thinCoverRunWithSearchWorkFrom G D (fun _ => 0)

theorem thinCoverRunWithSearchWork_spec (G : Arcs V) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := thinCoverRunWithSearchWork G D
    out.1.1 = thinCoverRun G D ∧
      (∀ e ∈ G, out.1.1 e ≤ G.card.log2+1) ∧
      out.1.2 ≤ G.card*(G.card.log2+1) ∧
      out.2 ≤ (D.length+G.card*(G.card.log2+1))*thinSeparatorWorkBound (Fintype.card V) G.card := by
  obtain ⟨same, caps, updates, work⟩ := thinCoverRunWithSearchWorkFrom_spec G D feasible (fun _ => 0)
    (fun _ _ => Nat.zero_le _)
  let out := thinCoverRunWithSearchWork G D
  have total : loadTotal G out.1.1 ≤ G.card*(G.card.log2+1) := by
    unfold loadTotal
    exact (sum_le_sum caps).trans_eq (by simp)
  have updates' : out.1.2 ≤ G.card*(G.card.log2+1) := (Nat.le_add_left ..).trans (updates.trans total)
  exact ⟨same, caps, updates', work.trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_left updates' _))⟩

end OnlineReachabilityPreservers
