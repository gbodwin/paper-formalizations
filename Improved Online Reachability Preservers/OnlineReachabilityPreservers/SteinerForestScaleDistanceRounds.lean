import OnlineReachabilityPreservers.SteinerDistanceTable
import OnlineReachabilityPreservers.SteinerForestScaleRecurrence
import OnlineReachabilityPreservers.SteinerSeedDecoderWork
import OnlineReachabilityPreservers.SteinerUnaryBitWidthMachine

/-! Cache all rooted scale weights at each depth of the height reduction. -/

namespace OnlineReachabilityPreservers

open Finset StateTransition Turing

/-- At each depth compute one weight per root, using the previous vector
and the distance table. A distance larger than n denotes no transfer. -/
def inwardHeightWeightRounds {n : ℕ} (dist : Fin n × Fin n → ℕ) : ℕ → Vector ℕ n
  | 0 => Vector.replicate n 0
  | h+1 =>
    let last := inwardHeightWeightRounds dist h
    Vector.ofFn fun root =>
      ∑ vertex, (let distance := dist (vertex,root)
                 if distance ≤ n then distance+last[vertex.val] else 0)

theorem inwardHeightWeightRounds_get {n : ℕ} (G : Arcs (Fin n)) (dist : Fin n × Fin n → ℕ)
    (reachable : ∀ v r : Fin n, dist (v,r) ≤ n ↔ Reach G v r) (h : ℕ) (root : Fin n) :
    (inwardHeightWeightRounds dist h)[root.val] =
      inwardHeightWeightRecurrence G (fun v r => dist (v,r)) h root := by
  induction h generalizing root with
  | zero => simp [inwardHeightWeightRounds,inwardHeightWeightRecurrence]
  | succ h ih =>
    rw [inwardHeightWeightRounds,inwardHeightWeightRecurrence]
    simp only [Vector.getElem_ofFn]
    have same : (univ.filter fun v : Fin n => dist (v,root) ≤ n) = reaches G root := by
      ext v
      simp only [mem_filter,mem_univ,true_and,mem_reaches]
      exact reachable v root
    rw [← same,sum_filter]
    exact sum_congr rfl fun v _ => by simp [ih v]

/-- Compute both orientations of the scale from one distance table.
Only the preceding depth's vectors are needed at each round. -/
def forestScaleFromDistanceRounds {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) : ℕ :=
  let left := inwardHeightWeightRounds dist h
  let right := inwardHeightWeightRounds (fun d => dist d.swap) h
  max 1 (∑ root : Fin n, (left[root.val]+right[root.val]))

/-- The table rounds give the exact priced forest scale. -/
theorem forestScaleFromDistanceRounds_eq {n : ℕ} (G : Arcs (Fin n)) (dist : Fin n × Fin n → ℕ)
    (values : ∀ d, dist d = hops G d.1 d.2) (h : ℕ) :
    forestScaleFromDistanceRounds dist h = forestScale G h := by
  rw [forestScale_eq_recurrence,forestScaleFromDistanceRounds,forestScaleByRecurrence]
  have reach (v r : Fin n) : dist (v,r) ≤ n ↔ Reach G v r := by
    rw [values]
    simpa only [Fintype.card_fin] using hops_le_vertices_iff G v r
  have reverse (v r : Fin n) : (fun d : Fin n × Fin n => dist d.swap) (v,r) ≤ n ↔
      Reach (reverseArcs G) v r := (reach r v).trans reach_reverseArcs.symm
  apply congrArg (max 1)
  apply sum_congr rfl
  intro root _
  rw [inwardHeightWeightRounds_get G dist reach,inwardHeightWeightRounds_get (reverseArcs G) _ reverse]
  have same : (fun v r => dist (v,r)) = hops G := by
    funext v r
    exact values (v,r)
  have swapped : (fun v r : Fin n => dist ((v,r) : Fin n × Fin n).swap) = fun v r => hops G r v := by
    funext v r
    exact values (r,v)
  rw [same,swapped]

/-- Counts in the rooted vectors obey this bound at each depth. -/
def inwardHeightWeightRoundBound (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | h+1 => n*(n+inwardHeightWeightRoundBound n h)

theorem inwardHeightWeightRounds_get_le {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) (root : Fin n) :
    (inwardHeightWeightRounds dist h)[root.val] ≤ inwardHeightWeightRoundBound n h := by
  induction h generalizing root with
  | zero => simp [inwardHeightWeightRounds,inwardHeightWeightRoundBound]
  | succ h ih =>
    rw [inwardHeightWeightRounds,inwardHeightWeightRoundBound]
    simp only [Vector.getElem_ofFn]
    calc
      _ ≤ ∑ _ : Fin n, (n+inwardHeightWeightRoundBound n h) := by
        apply sum_le_sum
        intro vertex _
        split_ifs with close
        · exact Nat.add_le_add close (ih vertex)
        · exact Nat.zero_le _
      _ = _ := by simp

theorem inwardHeightWeightRoundBound_add_le (n h : ℕ) :
    inwardHeightWeightRoundBound n h+n ≤ (n+1)^(h+1) := by
  induction h with
  | zero => simp [inwardHeightWeightRoundBound]
  | succ h ih =>
    have top : n ≤ (n+1)^(h+1) :=
      (Nat.le_succ n).trans (Nat.le_self_pow (by omega) (n+1))
    calc
      _ = n*(inwardHeightWeightRoundBound n h+n)+n := by rw [inwardHeightWeightRoundBound,add_comm n]
      _ ≤ n*((n+1)^(h+1))+(n+1)^(h+1) := Nat.add_le_add (Nat.mul_le_mul_left _ ih) top
      _ = _ := by rw [pow_succ]; ring

/-- The round arithmetic stays within a fixed-height polynomial magnitude
even for arbitrary supplied distance entries. -/
theorem forestScaleFromDistanceRounds_le {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    forestScaleFromDistanceRounds dist h ≤ 1+2*n*(n+1)^(h+1) := by
  have cap : inwardHeightWeightRoundBound n h ≤ (n+1)^(h+1) :=
    (Nat.le_add_right _ _).trans (inwardHeightWeightRoundBound_add_le n h)
  unfold forestScaleFromDistanceRounds
  apply max_le (by omega)
  calc
    _ ≤ ∑ _ : Fin n, (2*(n+1)^(h+1)) := by
      apply sum_le_sum
      intro root _
      have l := (inwardHeightWeightRounds_get_le dist h root).trans cap
      have r := (inwardHeightWeightRounds_get_le (fun d => dist d.swap) h root).trans cap
      omega
    _ = 2*n*(n+1)^(h+1) := by simp; ring
    _ ≤ _ := by omega

/-- Once the unary scale tally is supplied, the checked width machine
returns the exact forest proposal width used by seed decoding. -/
def steinerForestScaleWidthMachine_distanceRounds {n : ℕ} (G : Arcs (Fin n))
    (dist : Fin n × Fin n → ℕ) (values : ∀ d, dist d = hops G d.1 d.2) (h : ℕ) :
    let scale := forestScaleFromDistanceRounds dist h
    TM2OutputsInTime steinerUnaryBitWidthMachine (encodeSteinerUnaryProductCount scale)
      (some (encodeSteinerUnaryProductCount ((forestScale G h).log2+1))) (3*scale+1) := by
  let scale := forestScaleFromDistanceRounds dist h
  have correct : scale = forestScale G h := forestScaleFromDistanceRounds_eq G dist values h
  have positive : 1 ≤ (forestScale G h).size :=
    Nat.one_le_iff_ne_zero.mpr fun zero => (ne_of_gt (forestScale_pos G h)) (Nat.size_eq_zero.mp zero)
  have width : scale.size = (forestScale G h).log2+1 := by
    rw [correct,← max_size_eq_log2_add_one,max_eq_right positive]
  simpa only [width] using steinerUnaryBitWidthMachine_run scale

end OnlineReachabilityPreservers
