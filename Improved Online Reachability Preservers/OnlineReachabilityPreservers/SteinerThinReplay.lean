import OnlineReachabilityPreservers.ThinSearchWork
import OnlineReachabilityPreservers.SteinerThinRound

/-! Search work in all prefix tests of the thin rounding procedure. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def thinRoundWorkEntry (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    (D : List (V × V)) (i : Fin D.length) : Fin D.length × Bool × ℕ :=
  let fraction := thinCoverRunWithSearchWork G (D.take (i.val+1))
  let arcs := roundedThinArcs G factor fraction.1.1 sample
  let reach := reachInWithArcInspections arcs (D.get i).2 (Fintype.card V)
  (i, decide ((D.get i).1 ∉ reach.1), fraction.2+G.card+reach.2)

private theorem thinRoundWorkEntry_flag (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    (D : List (V × V)) (i : Fin D.length) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (thinRoundWorkEntry G factor sample D i).2.1 = true ↔
      (D.get i).1 ∉ reaches
        (roundedThinArcs G factor (thinCoverRun G (D.take (i.val+1))) sample) (D.get i).2 := by
  have earlier : ∀ d ∈ D.take (i.val+1), Reach G d.1 d.2 :=
    fun d hd => feasible d (List.mem_of_mem_take hd)
  have same := (thinCoverRunWithSearchWork_spec G (D.take (i.val+1)) earlier).1
  simp only [thinRoundWorkEntry, reachInWithArcInspections_spec, decide_eq_true_eq, same, reaches]

/-- Individual charges include a scan of the rounded arc set and a
reachability test, in addition to the fractional prefix evaluator. -/
def thinRoundPrefixWorkBound (n m p : ℕ) : ℕ :=
  (p+m*(m.log2+1))*thinSeparatorWorkBound n m+m+n*m

private theorem thinRoundWorkEntry_bound (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    (D : List (V × V)) (i : Fin D.length) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (thinRoundWorkEntry G factor sample D i).2.2 ≤
      thinRoundPrefixWorkBound (Fintype.card V) G.card D.length := by
  have earlier : ∀ d ∈ D.take (i.val+1), Reach G d.1 d.2 :=
    fun d hd => feasible d (List.mem_of_mem_take hd)
  let P := D.take (i.val+1)
  let result := thinCoverRunWithSearchWork G P
  let n := Fintype.card V
  let m := G.card
  let R := roundedThinArcs G factor result.1.1 sample
  have frac := (thinCoverRunWithSearchWork_spec G P earlier).2.2.2.trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (show P.length ≤ D.length from (List.take_prefix _ _).length_le) _))
  have arcs : R.card ≤ m := card_le_card (roundedThinArcs_subset _ _ _ _)
  change result.2+m+(reachInWithArcInspections R (D.get i).2 n).2 ≤ _
  rw [reachInWithArcInspections_spec R (D.get i).2 n]
  exact Nat.add_le_add (Nat.add_le_add_right frac m) (Nat.mul_le_mul_left _ arcs)

/-- Reproduce the ordinary thin fallback and final graph while charging
each fractional replay, rounded-arc scan and reachability test. -/
def thinRoundRunWithSearchWork (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    (D : List (V × V)) : Arcs V × ℕ :=
  if D.isEmpty then (∅,0) else
    let rows := (univ : Finset (Fin D.length)).image (thinRoundWorkEntry G factor sample D)
    let cost := ∑ row ∈ rows, row.2.2
    if (rows.filter (fun r => r.2.1 = true)).Nonempty then (G,cost)
    else
      let result := thinCoverRunWithSearchWork G D
      (roundedThinArcs G factor result.1.1 sample,cost+result.2+G.card)

theorem thinRoundRunWithSearchWork_spec (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := thinRoundRunWithSearchWork G factor sample D
    out.1 = thinRoundRun G factor sample D ∧
      out.2 ≤ (D.length+1)*thinRoundPrefixWorkBound (Fintype.card V) G.card D.length := by
  let rows := (univ : Finset (Fin D.length)).image (thinRoundWorkEntry G factor sample D)
  let cost := ∑ row ∈ rows, row.2.2
  let B := thinRoundPrefixWorkBound (Fintype.card V) G.card D.length
  have same : (rows.filter (fun r => r.2.1 = true)).Nonempty ↔ ThinRoundFailure G factor sample D := by
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨inside, mark⟩ := mem_filter.mp hr
      obtain ⟨i, _, rfl⟩ := mem_image.mp inside
      exact ⟨i, (thinRoundWorkEntry_flag G factor sample D i feasible).mp mark⟩
    · rintro ⟨i, missed⟩
      exact ⟨_, mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ i),
        (thinRoundWorkEntry_flag G factor sample D i feasible).mpr missed⟩⟩
  have work : cost ≤ D.length*B := by
    dsimp only [cost, rows]
    rw [sum_image (fun a _ b _ eq => congrArg Prod.fst eq)]
    calc
      _ ≤ ∑ _ : Fin D.length, B :=
        sum_le_sum (fun i _ => thinRoundWorkEntry_bound G factor sample D i feasible)
      _ = _ := by simp
  by_cases empty : D.isEmpty = true
  · simp [thinRoundRunWithSearchWork, thinRoundRun, empty]
  by_cases failed : ThinRoundFailure G factor sample D
  · have failed' := same.mpr failed
    simp only [thinRoundRunWithSearchWork, thinRoundRun, empty, Bool.false_eq_true, ite_false]
    rw [ite_eq_left failed', ite_eq_left failed]
    exact ⟨rfl, work.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))⟩
  · have passed := (not_congr same).mpr failed
    obtain ⟨output, _, _, finalWork⟩ := thinCoverRunWithSearchWork_spec G D feasible
    simp only [thinRoundRunWithSearchWork, thinRoundRun, empty, Bool.false_eq_true, ite_false]
    rw [ite_eq_right passed, ite_eq_right failed]
    refine ⟨congrArg (fun load => roundedThinArcs G factor load sample) output, ?_⟩
    have cap : (thinCoverRunWithSearchWork G D).2+G.card ≤ B :=
      (Nat.add_le_add_right finalWork _).trans (Nat.le_add_right _ _)
    change cost+(thinCoverRunWithSearchWork G D).2+G.card ≤ (D.length+1)*B
    rw [Nat.add_assoc, Nat.succ_mul]
    exact Nat.add_le_add work cap

end OnlineReachabilityPreservers
