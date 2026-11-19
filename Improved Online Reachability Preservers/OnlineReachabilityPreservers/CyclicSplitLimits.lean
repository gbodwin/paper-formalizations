import OnlineReachabilityPreservers.OppositePathChains

/-! Limits of the opposite-intersection condition for local path splitting. -/

namespace OnlineReachabilityPreservers.SourceAudit

/-- Two reversed return chains connect opposite pairs on the long path. -/
def sixMirrorExample : Fin 5 → List (Fin 6) :=
  ![[2,0,5,3],[0,1],[1,2],[3,4],[4,5]]

/-- Splitting the long row into two order-preserving filtered pieces. -/
def sixMirrorPieces : Fin 6 → List (Fin 6) :=
  ![[2,3],[0,5],[0,1],[1,2],[3,4],[4,5]]

def sixMirrorParent : Fin 6 → Fin 5 := ![0,0,1,2,3,4]

/-- Every piece is an order-preserving restriction of its parent. -/
theorem sixMirrorPieces_sublist (i : Fin 6) :
    List.Sublist (sixMirrorPieces i) (sixMirrorExample (sixMirrorParent i)) := by
  fin_cases i
  · exact List.Sublist.cons_cons 2 (.cons 0 (.cons 5 (.cons_cons 3 .slnil)))
  · exact List.Sublist.cons 2 (.cons_cons 0 (.cons_cons 5 (.cons 3 .slnil)))
  all_goals exact List.Sublist.refl _

set_option maxRecDepth 65536 in
/-- Different pieces of the same parent are disjoint. -/
theorem sixMirrorPieces_disjoint (i j : Fin 6) (v : Fin 6) (apart : i ≠ j)
    (same : sixMirrorParent i = sixMirrorParent j)
    (left : v ∈ sixMirrorPieces i) (right : v ∈ sixMirrorPieces j) : False := by
  have checked : ∀ (i j v : Fin 6), i ≠ j → sixMirrorParent i = sixMirrorParent j →
      (sixMirrorPieces i).contains v = true → (sixMirrorPieces j).contains v = true → False := by
    decide
  exact checked i j v apart same (List.contains_iff_mem.mpr left) (List.contains_iff_mem.mpr right)

private def sixMirrorReverseCertificate (r t v : Fin 6) : Bool :=
  if r = 0 then decide (v.val/3 = t.val/3 ∧ v ≤ t)
  else if r = 1 ∧ t = 1 then decide (v = 1)
  else if r = 2 ∧ t = 2 then decide (v ≠ 1)
  else if r = 3 ∧ t = 4 then decide (v = 4)
  else if r = 4 ∧ t = 5 then decide (v ≠ 4)
  else true

private def beforeSixBool (r : Fin 5) (v w : Fin 6) : Bool :=
  (sixMirrorExample r).contains v && (sixMirrorExample r).contains w &&
    decide ((sixMirrorExample r).idxOf v < (sixMirrorExample r).idxOf w)

private theorem beforeSixBool_eq {r : Fin 5} {v w : Fin 6} (h : BeforeIn sixMirrorExample r v w) :
    beforeSixBool r v w = true := by
  unfold beforeSixBool
  simpa only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_iff] using
    And.intro (And.intro h.1 h.2.1) h.2.2

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2500000 in
private theorem certificate_closed : ∀ (r i : Fin 5) (t v w : Fin 6),
    i ≠ r → beforeSixBool i v w = true →
    sixMirrorReverseCertificate r.castSucc t w = true →
    sixMirrorReverseCertificate r.castSucc t v = true := by
  decide

set_option maxRecDepth 65536 in
private theorem certificate_miss : ∀ (r : Fin 5) (s t : Fin 6),
    beforeSixBool r s t = true → sixMirrorReverseCertificate r.castSucc t s = false := by
  decide

set_option maxRecDepth 65536 in
private theorem certificate_end : ∀ (r : Fin 5) (t : Fin 6),
    sixMirrorReverseCertificate r.castSucc t t = true := by
  decide

private theorem sixMirror_chain {k : ℕ} (b : Bridge (BeforeIn sixMirrorExample) k)
    (t : Fin 6) (i : Fin (k+2)) : sixMirrorReverseCertificate b.river.castSucc t (b.vertex i) = true →
      sixMirrorReverseCertificate b.river.castSucc t (b.vertex 0) = true := by
  induction i using Fin.induction with
  | zero => exact id
  | succ j ih =>
    intro closed
    exact ih (certificate_closed b.river (b.arc j) t _ _ (b.river_ne_arc j).symm
      (beforeSixBool_eq (b.arcStep j)) closed)

/-- The original local orders exclude full bridges of every size. -/
theorem sixMirrorExample_no_full : ∀ k, IsEmpty (Bridge (BeforeIn sixMirrorExample) k) := by
  intro k
  refine ⟨fun b => ?_⟩
  let t := b.vertex (Fin.last (k+1))
  have accepted := sixMirror_chain b t (Fin.last (k+1)) (certificate_end b.river t)
  rw [certificate_miss b.river _ t (beforeSixBool_eq b.riverStep)] at accepted
  contradiction

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
/-- Distinct original paths share at most one vertex. -/
theorem sixMirrorExample_unique : ∀ (i j : Fin 5) (v w : Fin 6),
    i ≠ j → v ∈ sixMirrorExample i → v ∈ sixMirrorExample j →
    w ∈ sixMirrorExample i → w ∈ sixMirrorExample j → v = w := by
  intro i j v w
  have verified : ∀ (i j : Fin 5) (v w : Fin 6),
      i ≠ j → (sixMirrorExample i).contains v = true → (sixMirrorExample j).contains v = true →
      (sixMirrorExample i).contains w = true → (sixMirrorExample j).contains w = true → v = w := by
    decide
  simpa only [List.contains_iff_mem] using verified i j v w

/-- The pieces admit a six-bridge despite the vacuous opposite-intersection constraint. -/
def sixMirrorPieces_bridge : Bridge (BeforeIn sixMirrorPieces) 4 :=
  ⟨id, ![2,3,0,4,5], 1, Function.injective_id,
    by intro a b eq; fin_cases a <;> fin_cases b <;> simp_all,
    by intro i; fin_cases i <;> decide,
    by unfold BeforeIn; decide,
    by intro i; fin_cases i <;> (unfold BeforeIn; decide)⟩

end OnlineReachabilityPreservers.SourceAudit

namespace OnlineReachabilityPreservers.SourceAudit

/-- A half-free path can have two different opposite neighbors at a vertex. -/
def halfOppositeBranches : Fin 3 → List (Fin 3) := ![[0,1,2],[1,0],[2,0]]

private def halfBranchStep (r v w : Fin 3) : Bool :=
  (halfOppositeBranches r).contains v && (halfOppositeBranches r).contains w &&
    decide ((halfOppositeBranches r).idxOf v < (halfOppositeBranches r).idxOf w)

private theorem halfBranchStep_of_before {r v w : Fin 3} (h : BeforeIn halfOppositeBranches r v w) :
    halfBranchStep r v w = true := by
  unfold halfBranchStep
  simpa only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_iff] using
    And.intro (And.intro h.1 h.2.1) h.2.2

set_option maxRecDepth 65536 in
private theorem halfOppositeBranches_no_parallel : ∀ (r a x y : Fin 3), r ≠ a →
    halfBranchStep a x y = true → halfBranchStep r x y = true → False := by
  decide

set_option maxRecDepth 65536 in
private theorem halfOppositeBranches_no_half_three : ∀ (r a b x y z : Fin 3),
    r ≠ a → r ≠ b → a ≠ b → b < r →
    halfBranchStep a x y = true → halfBranchStep b y z = true → halfBranchStep r x z = true → False := by
  decide

/-- Every half-bridge is excluded even though there is a full three-bridge. -/
theorem halfOppositeBranches_free (k : ℕ) : HalfBridgeFree (BeforeIn halfOppositeBranches) k := by
  intro q cutoff b earlier
  have count := Fintype.card_le_of_injective _ b.distinctVertices
  simp only [Fintype.card_fin] at count
  have short : q ≤ 1 := by omega
  interval_cases q
  · exact halfOppositeBranches_no_parallel b.river (b.arc 0) _ _ (b.river_ne_arc 0)
      (halfBranchStep_of_before (b.arcStep 0)) (halfBranchStep_of_before b.riverStep)
  · have different : b.arc 0 ≠ b.arc 1 := fun same =>
      (by decide : (0 : Fin 2) ≠ 1) (b.distinctArcs same)
    exact halfOppositeBranches_no_half_three b.river (b.arc 0) (b.arc 1) _ _ _
      (b.river_ne_arc 0) (b.river_ne_arc 1) different earlier
      (halfBranchStep_of_before (b.arcStep 0)) (halfBranchStep_of_before (b.arcStep 1))
      (halfBranchStep_of_before b.riverStep)

/-- This local chain branches in half mode, so full-mode partner uniqueness fails. -/
theorem halfOppositeBranches_has_branch :
    OppositeNeighbors halfOppositeBranches 0 1 0 1 ∧ OppositeNeighbors halfOppositeBranches 0 2 0 2 := by
  unfold OppositeNeighbors BeforeIn
  constructor
  · refine ⟨by decide, by decide, by decide, ?_⟩
    rintro ⟨z,left,right,onOther⟩
    fin_cases z <;> simp_all [halfOppositeBranches]
  · refine ⟨by decide, by decide, by decide, ?_⟩
    rintro ⟨z,left,right,onOther⟩
    fin_cases z <;> simp_all [halfOppositeBranches]

end OnlineReachabilityPreservers.SourceAudit
