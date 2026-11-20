import OnlineReachabilityPreservers.ContiguousHalfCleaning
import OnlineReachabilityPreservers.OppositePruningGain

/-! Counterexamples at the exact printed mean and at the four-average upper caps. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset
open scoped Sigma.Lex

private theorem star_family_bridge_free {V I : Type*} [DecidableEq V]
    (paths : I → List V) (center : I)
    (noParallel : ∀ (a r : I) (x y : V), a ≠ r →
      BeforeIn paths a x y → BeforeIn paths r x y → False)
    (intersects : ∀ (a b : I) (v : V), a ≠ b → v ∈ paths a → v ∈ paths b →
      a = center ∨ b = center)
    (k : ℕ) : IsEmpty (Bridge (BeforeIn paths) k) := by
  refine ⟨fun b => ?_⟩
  cases k with
  | zero =>
    exact noParallel (b.arc 0) b.river _ _ (b.river_ne_arc 0).symm (b.arcStep 0) b.riverStep
  | succ k =>
    cases k with
    | zero =>
      have distinct : b.arc 0 ≠ b.arc 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (b.distinctArcs h)
      have a := intersects b.river (b.arc 0) _ (b.river_ne_arc 0) b.riverStep.1 (b.arcStep 0).1
      have c := intersects (b.arc 0) (b.arc 1) _ distinct (b.arcStep 0).2.1 (b.arcStep 1).1
      have d := intersects b.river (b.arc 1) _ (b.river_ne_arc 1) b.riverStep.2.1 (b.arcStep 1).2.1
      rcases a with r | u
      · exact c.elim (fun u => b.river_ne_arc 0 (r.trans u.symm))
          (fun v => b.river_ne_arc 1 (r.trans v.symm))
      · exact d.elim (fun r => b.river_ne_arc 0 (r.trans u.symm))
          (fun v => distinct (u.trans v.symm))
    | succ k =>
      let a0 : Fin (k+3) := ⟨0,by omega⟩
      let a1 : Fin (k+3) := ⟨1,by omega⟩
      let a2 : Fin (k+3) := ⟨2,by omega⟩
      have distinct {i j : Fin (k+3)} (different : i ≠ j) : b.arc i ≠ b.arc j :=
        fun h => different (b.distinctArcs h)
      have apart01 : a0 ≠ a1 := by intro h; have eq := congrArg Fin.val h; change 0 = 1 at eq; omega
      have apart02 : a0 ≠ a2 := by intro h; have eq := congrArg Fin.val h; change 0 = 2 at eq; omega
      have apart12 : a1 ≠ a2 := by intro h; have eq := congrArg Fin.val h; change 1 = 2 at eq; omega
      have a := intersects b.river (b.arc a0) _ (b.river_ne_arc a0)
        b.riverStep.1 (b.arcStep a0).1
      have c := intersects (b.arc a1) (b.arc a2) _ (distinct apart12)
        (b.arcStep a1).2.1 (b.arcStep a2).1
      rcases a with r | u <;> rcases c with v | v
      · exact b.river_ne_arc a1 (r.trans v.symm)
      · exact b.river_ne_arc a2 (r.trans v.symm)
      · exact distinct apart01 (u.trans v.symm)
      · exact distinct apart02 (u.trans v.symm)

/-- The long path and its three opposite partners have mean length four
and uniform vertex degree two. -/
def midpointSplitExample : Fin 4 → List (Fin 8) :=
  ![[0,4,5,1,2,6,7,3],[3,0],[2,1],[7,6,5,4]]

/-- The first path is replaced in place by its two consecutive halves. -/
def midpointSplitExampleAfter : Fin 5 → List (Fin 8) :=
  ![[0,4,5,1],[2,6,7,3],[3,0],[2,1],[7,6,5,4]]

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 1024 in
private theorem midpoint_no_parallel :
    ∀ (a r : Fin 4) (x y : Fin 8), a ≠ r →
      BeforeIn midpointSplitExample a x y → BeforeIn midpointSplitExample r x y → False := by
  unfold BeforeIn
  decide

private theorem midpoint_shares_only_with_first :
    ∀ (a b : Fin 4) (v : Fin 8), a ≠ b → v ∈ midpointSplitExample a → v ∈ midpointSplitExample b →
      a = 0 ∨ b = 0 := by decide

/-- All bridges are excluded. Among the three short paths no two intersect,
and no ordered vertex pair occurs on two distinct paths. -/
theorem midpointSplitExample_free (k : ℕ) : IsEmpty (Bridge (BeforeIn midpointSplitExample) k) :=
  star_family_bridge_free midpointSplitExample 0 midpoint_no_parallel midpoint_shares_only_with_first k

theorem midpointSplitExample_has_nested_opposites : ¬ NoLaterNestedOpposites midpointSplitExample := by
  intro noNested
  apply noNested (outer := 1) (first := 0) (inner := 2) (by decide) (by decide) (by decide)
    (u := 0) (v := 1) (w := 2) (z := 3) <;> unfold BeforeIn <;> decide

/-- The original averages are degree two and length four. Only the first
path exceeds the mean length, and its two pieces have length four. -/
theorem midpointSplitExample_parameters :
    (∑ i, (midpointSplitExample i).length) = 16 ∧
      (∀ v, (occurrences (fun i => (midpointSplitExample i).toFinset) v).card = 2) ∧
      (∀ i, (midpointSplitExample i).Nodup ∧ 1 ≤ (midpointSplitExample i).length ∧
        (i ≠ 0 → (midpointSplitExample i).length ≤ 4)) ∧
      (midpointSplitExample 0).length = 8 ∧
      midpointSplitExampleAfter 0 = (midpointSplitExample 0).take 4 ∧
      midpointSplitExampleAfter 1 = (midpointSplitExample 0).drop 4 ∧
      (∀ i : Fin 3, midpointSplitExampleAfter ⟨i.val+2,by omega⟩ = midpointSplitExample i.succ) ∧
      (∀ i, (midpointSplitExampleAfter i).Nodup ∧
        1 ≤ (midpointSplitExampleAfter i).length ∧ (midpointSplitExampleAfter i).length ≤ 4) ∧
      (∀ v, (occurrences (fun i => (midpointSplitExampleAfter i).toFinset) v).card = 2) := by
  decide

/-- The only required midpoint split leaves a half-4-bridge after the
printed deletion and mean-width splitting rules have all terminated. -/
theorem midpointSplitExample_creates_half_four :
    ∃ b : Bridge (BeforeIn midpointSplitExampleAfter) 2, b.arc (Fin.last 2) < b.river := by
  let v : Fin 4 → Fin 8 := ![2,3,0,1]
  let a : Fin 3 → Fin 5 := ![1,2,0]
  have hv : ∀ i j, v i = v j → i = j := by decide
  have ha : ∀ i j, a i = a j → i = j := by decide
  have hr : ∀ i, (3 : Fin 5) ≠ a i := by decide
  have flow : BeforeIn midpointSplitExampleAfter 3 (v 0) (v (Fin.last 3)) := by
    unfold BeforeIn
    decide
  have chain : ∀ i, BeforeIn midpointSplitExampleAfter (a i) (v i.castSucc) (v i.succ) := by
    unfold BeforeIn
    decide
  refine ⟨⟨v,a,3,fun {_ _} => hv _ _,fun {_ _} => ha _ _,hr,flow,chain⟩,?_⟩
  change (0 : Fin 5) < 3
  decide

private def capSplitCore : Fin 3 → List (Fin 8) :=
  ![[0,4,5,1,2,6,7,3],[3,0],[2,1]]

private def capSplitPadding (i : Fin 37) : Fin 8 := ⟨i.val % 8,Nat.mod_lt _ (by decide)⟩

private def padSingletonPaths {V : Type*} {p r : ℕ} (core : Fin r → List V)
    (single : Fin p → V) (i : Fin p) : List V :=
  if inCore : i.val < r then core ⟨i.val,inCore⟩ else [single i]

private theorem padSingletonPaths_free {V : Type*} [DecidableEq V] {p r : ℕ}
    (core : Fin r → List V) (single : Fin p → V)
    (free : ∀ k, IsEmpty (Bridge (BeforeIn core) k)) (k : ℕ) :
    IsEmpty (Bridge (BeforeIn (padSingletonPaths core single)) k) := by
  refine ⟨fun b => ?_⟩
  have active {i : Fin p} {x y : V} (step : BeforeIn (padSingletonPaths core single) i x y) :
      i.val < r := by
    by_contra outside
    have row : padSingletonPaths core single i = [single i] := by simp [padSingletonPaths,outside]
    unfold BeforeIn at step
    rw [row] at step
    obtain ⟨left,right,order⟩ := step
    have equal : x = y := (List.mem_singleton.mp left).trans (List.mem_singleton.mp right).symm
    subst y
    exact (lt_irrefl _) order
  have project {i : Fin p} {x y : V} (step : BeforeIn (padSingletonPaths core single) i x y) :
      BeforeIn core ⟨i.val,active step⟩ x y := by
    simpa only [BeforeIn,padSingletonPaths,active step,dite_eq_left] using step
  let river : Fin r := ⟨b.river.val,active b.riverStep⟩
  let arc (i : Fin (k+1)) : Fin r := ⟨(b.arc i).val,active (b.arcStep i)⟩
  exact (free k).false
    ⟨b.vertex,arc,river,b.distinctVertices,
      fun _ _ same => b.distinctArcs (Fin.ext (congrArg (fun j : Fin r => j.val) same)),
      fun i same => b.river_ne_arc i (Fin.ext (congrArg (fun j : Fin r => j.val) same)),
      project b.riverStep,fun i => project (b.arcStep i)⟩

/-- Add singleton paths so the exact original-average upper path cap is
four, with the long row cut between its two opposite intervals. -/
def capSplitExample : Fin 37 → List (Fin 8) :=
  padSingletonPaths capSplitCore capSplitPadding

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem capSplitCore_two :
    ∀ (r a : Fin 3) (x y : Fin 8), r ≠ a →
      BeforeIn capSplitCore a x y → BeforeIn capSplitCore r x y → False := by
  unfold BeforeIn
  decide

private theorem capSplitCore_intersects :
    ∀ (a b : Fin 3) (v : Fin 8), a ≠ b → v ∈ capSplitCore a → v ∈ capSplitCore b →
      a = 0 ∨ b = 0 := by decide

private theorem capSplitCore_free (k : ℕ) : IsEmpty (Bridge (BeforeIn capSplitCore) k) :=
  star_family_bridge_free capSplitCore 0
    (fun a r x y different first second => capSplitCore_two r a x y different.symm first second)
    capSplitCore_intersects k

/-- The padded input has no bridge at any size. Its singleton rows
cannot serve as an arc or a river. -/
theorem capSplitExample_free (k : ℕ) : IsEmpty (Bridge (BeforeIn capSplitExample) k) :=
  padSingletonPaths_free capSplitCore capSplitPadding capSplitCore_free k

theorem capSplitExample_has_nested_opposites : ¬ NoLaterNestedOpposites capSplitExample := by
  intro noNested
  apply noNested (outer := 1) (first := 0) (inner := 2) (by decide) (by decide) (by decide)
    (u := 0) (v := 1) (w := 2) (z := 3) <;> unfold BeforeIn <;> decide

theorem capSplitExample_mass : (∑ i, (capSplitExample i).length) = 46 := by decide

theorem capSplitExample_simple : ∀ i, (capSplitExample i).Nodup := by decide

set_option synthInstance.maxSize 1024 in
theorem capSplitExample_degree_range :
    ∀ v, 2 ≤ (occurrences (fun i => (capSplitExample i).toFinset) v).card ∧
      (occurrences (fun i => (capSplitExample i).toFinset) v).card ≤ 23 := by decide

/-- Every original row and vertex already satisfies the fixed lower caps. -/
theorem capSplitExample_initial_lower_caps :
    (∀ v, (46 : ℝ)/(4*8) ≤ (occurrences (fun i => (capSplitExample i).toFinset) v).card) ∧
      (∀ i, (46 : ℝ)/(4*37) ≤ (capSplitExample i).length) := by
  have nonempty : ∀ i, 1 ≤ (capSplitExample i).length := by decide
  constructor
  · intro v
    exact (by norm_num : (46 : ℝ)/(4*8) ≤ 2).trans (by exact_mod_cast (capSplitExample_degree_range v).1)
  · intro i
    exact (by norm_num : (46 : ℝ)/(4*37) ≤ 1).trans (by exact_mod_cast nonempty i)

set_option maxRecDepth 65536 in
set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 3000000 in
/-- The exact widths from the original four-average caps can introduce a
half-4-bridge, even when the input is fully bridge-free. -/
theorem capSplitExample_four_average_blocks_create_half_four :
    let M := ∑ i, (capSplitExample i).length
    ∃ b : Bridge (BeforeIn (listRegularizedPaths capSplitExample (4*M/8) (4*M/37))) 2,
      b.arc (Fin.last 2) < b.river := by
  dsimp only
  rw [capSplitExample_mass]
  change ∃ b : Bridge (BeforeIn (listRegularizedPaths capSplitExample 23 4)) 2,
    b.arc (Fin.last 2) < b.river
  let copies := splitListVertices capSplitExample 23
  let T := ListBlockIndex copies 4
  let a0 : T := ⟨0,⟨1,by decide⟩⟩
  let a1 : T := ⟨1,⟨0,by decide⟩⟩
  let a2 : T := ⟨0,⟨0,by decide⟩⟩
  let r : T := ⟨2,⟨0,by decide⟩⟩
  let a : Fin 3 → T := ![a0,a1,a2]
  let corner (v : Fin 8) : ListVertexBlockIndex capSplitExample 23 := ⟨v,⟨0,Nat.succ_pos _⟩⟩
  let v : Fin 4 → ListVertexBlockIndex capSplitExample 23 := ![corner 2,corner 3,corner 0,corner 1]
  have hv : ∀ i j, v i = v j → i = j := by decide
  have ha : ∀ i j, a i = a j → i = j := by decide
  have hr : ∀ i, r ≠ a i := by
    intro i equal
    have roots := congrArg (fun t : T => t.fst) equal
    fin_cases i
    · exact (by decide : (2 : Fin 37) ≠ 0) roots
    · exact (by decide : (2 : Fin 37) ≠ 1) roots
    · exact (by decide : (2 : Fin 37) ≠ 0) roots
  have flow : BeforeIn (listRegularizedPaths capSplitExample 23 4) r (v 0) (v (Fin.last 3)) := by
    unfold BeforeIn
    decide
  have chain : ∀ i, BeforeIn (listRegularizedPaths capSplitExample 23 4) (a i) (v i.castSucc) (v i.succ) := by
    unfold BeforeIn
    decide
  refine ⟨⟨v,a,r,fun {_ _} => hv _ _,fun {_ _} => ha _ _,hr,flow,chain⟩,?_⟩
  change a2 < r
  exact Sigma.Lex.left _ _ (by decide : (0 : Fin 37) < 2)

private def oppositeComparison (p : ℕ) : Fin p → List (Fin 8) :=
  padSingletonPaths (oppositeRows 8) (fun i => ⟨i.val%8,Nat.mod_lt _ (by decide)⟩)

private theorem oppositeComparison_simple (p : ℕ) (i : Fin p) :
    (oppositeComparison p i).Nodup := by
  have rows : ∀ j : Fin 2, (oppositeRows 8 j).Nodup := by decide
  by_cases inCore : i.val < 2
  · simpa only [oppositeComparison,padSingletonPaths,inCore,dite_eq_left] using rows ⟨i.val,inCore⟩
  · simp [oppositeComparison,padSingletonPaths,inCore]

private theorem oppositeComparison_free (p k : ℕ) :
    IsEmpty (Bridge (BeforeIn (oppositeComparison p)) k) :=
  padSingletonPaths_free _ _ (fun j => oppositeRows_bridge_free 8 (j+2) le_rfl) k

/-- The mean-width counterexample is smaller than a fully bridge-free
system at the same vertex and path counts. -/
theorem midpointSplitExample_nonmaximal :
    ∃ paths : Fin 4 → List (Fin 8), (∀ i, (paths i).Nodup) ∧
      (∀ k, IsEmpty (Bridge (BeforeIn paths) k)) ∧
      (∑ i, (midpointSplitExample i).length) < ∑ i, (paths i).length :=
  ⟨oppositeComparison 4,oppositeComparison_simple 4,oppositeComparison_free 4,by decide⟩

/-- The padded counterexample is also smaller than a fully bridge-free
indexed system at the same budgets. -/
theorem capSplitExample_nonmaximal :
    ∃ paths : Fin 37 → List (Fin 8), (∀ i, (paths i).Nodup) ∧
      (∀ k, IsEmpty (Bridge (BeforeIn paths) k)) ∧
      (∑ i, (capSplitExample i).length) < ∑ i, (paths i).length :=
  ⟨oppositeComparison 37,oppositeComparison_simple 37,oppositeComparison_free 37,by decide⟩

end OnlineReachabilityPreservers.SourceAudit
