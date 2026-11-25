import Mathlib.Basic.Real.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

/-! Each sorted breakpoint and each midpoint of consecutive breakpoints
is a representative for one comparison pattern. -/
namespace DirectedFlowCutGap.RationalThresholdRepresentatives

private def after (a : ℚ) : List ℚ → List ℚ
  | [] => [a]
  | b::rest => a :: (a+b)/2 :: after b rest

def candidates (breaks : List ℚ) : List ℚ :=
  match breaks.mergeSort (fun a b => a ≤ b) with
  | [] => []
  | a::rest => after a rest

private theorem after_length (a : ℚ) (tail : List ℚ) :
    (after a tail).length = 1+2*tail.length := by
  induction tail generalizing a with
  | nil => rfl
  | cons b rest ih => simp only [after,List.length_cons,ih]; omega

theorem candidates_length (breaks : List ℚ) : (candidates breaks).length = 2*breaks.length-1 := by
  have count : (breaks.mergeSort (fun a b => a ≤ b)).length = breaks.length := by simp
  cases shape : breaks.mergeSort (fun a b => a ≤ b) with
  | nil =>
    have len : breaks.length = 0 := by simpa [shape] using count.symm
    simp [candidates,shape,len]
  | cons a tail =>
    have len : breaks.length = tail.length+1 := by simpa [shape] using count.symm
    simp only [candidates,shape,after_length,len]
    omega

private theorem after_bounds {a q : ℚ} {tail : List ℚ}
    (bounds : ∀ c ∈ a::tail, 0 ≤ c ∧ c ≤ 1) (listed : q ∈ after a tail) : 0 ≤ q ∧ q ≤ 1 := by
  induction tail generalizing a with
  | nil =>
    have equal : q = a := by simpa [after] using listed
    exact equal ▸ bounds a (by simp)
  | cons b rest ih =>
    simp only [after,List.mem_cons] at listed
    rcases listed with rfl | rfl | recursive
    · exact bounds q (by simp)
    · have ha := bounds a (by simp)
      have hb := bounds b (by simp)
      exact ⟨by linarith [ha.1,hb.1],by linarith [ha.2,hb.2]⟩
    · exact ih (fun c atTail => bounds c (List.mem_cons_of_mem _ atTail)) recursive

theorem bounds_of_mem (breaks : List ℚ) (bounds : ∀ c ∈ breaks, 0 ≤ c ∧ c ≤ 1)
    {q : ℚ} (listed : q ∈ candidates breaks) : 0 ≤ q ∧ q ≤ 1 := by
  unfold candidates at listed
  split at listed
  · exact (List.not_mem_nil listed).elim
  · rename_i a tail eq
    exact after_bounds (fun c present => bounds c (List.mem_mergeSort.mp (eq.symm ▸ present))) listed

private def comparisons (level : ℝ) (q c : ℚ) : Prop :=
  ((q : ℝ) ≤ (c : ℝ) ↔ level ≤ (c : ℝ)) ∧
    ((c : ℝ) ≤ (q : ℝ) ↔ (c : ℝ) ≤ level)

private theorem after_representative (a : ℚ) (tail : List ℚ) {level : ℝ}
    (sorted : (a::tail).Pairwise (· ≤ ·)) (lo : (a : ℝ) ≤ level)
    (hi : ∃ b ∈ a::tail, level ≤ (b : ℝ)) :
    ∃ q ∈ after a tail, ∀ c ∈ a::tail, comparisons level q c := by
  induction tail generalizing a with
  | nil =>
    obtain ⟨b,mem,above⟩ := hi
    have eq : b = a := by simpa using mem
    have same : (a : ℝ) = level := by rw [eq] at above; exact le_antisymm lo above
    exact ⟨a,by simp [after],fun c _ => by simp [comparisons,same]⟩
  | cons b rest ih =>
    by_cases atFirst : (a : ℝ) = level
    · exact ⟨a,by simp [after],fun c _ => by simp [comparisons,atFirst]⟩
    have left : (a : ℝ) < level := lt_of_le_of_ne lo atFirst
    have ordered := List.pairwise_cons.mp sorted
    by_cases beforeNext : level < (b : ℝ)
    · let q := (a+b)/2
      have cast : (q : ℝ) = ((a : ℝ)+(b : ℝ))/2 := by simp [q]
      have lq : (a : ℝ) < (q : ℝ) := by linarith
      have rq : (q : ℝ) < (b : ℝ) := by linarith
      refine ⟨q,by simp [after,q],?_⟩
      intro c mem
      rcases List.mem_cons.mp mem with rfl | inTail
      · simp [comparisons,not_le_of_gt lq,not_le_of_gt left,lq.le,left.le]
      · have minimum : b ≤ c := by
          rcases List.mem_cons.mp inTail with rfl | later
          · exact le_rfl
          · exact (List.pairwise_cons.mp ordered.2).1 _ later
        have bound : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast minimum
        have a := rq.trans_le bound
        have b := beforeNext.trans_le bound
        simp [comparisons,not_le_of_gt a,not_le_of_gt b,a.le,b.le]
    · have next : (b : ℝ) ≤ level := le_of_not_gt beforeNext
      have upper : ∃ u ∈ b::rest, level ≤ (u : ℝ) := by
        obtain ⟨u,mem,upper⟩ := hi
        rcases List.mem_cons.mp mem with rfl | later
        · exact (not_le_of_gt left upper).elim
        · exact ⟨u,later,upper⟩
      obtain ⟨q,listed,matching⟩ := ih b ordered.2 next upper
      refine ⟨q,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ listed),?_⟩
      intro c mem
      rcases List.mem_cons.mp mem with rfl | later
      · have aLe : (c : ℝ) ≤ (b : ℝ) := by exact_mod_cast ordered.1 b (by simp)
        have good := matching b (by simp)
        have qAbove : (c : ℝ) < (q : ℝ) := by
          rcases lt_or_eq_of_le aLe with apart | same
          · exact apart.trans_le (good.2.mpr next)
          · rw [same]
            have leftB : (b : ℝ) < level := same ▸ left
            exact lt_of_not_ge fun below => not_le_of_gt leftB (good.1.mp below)
        simp [comparisons,not_le_of_gt qAbove,not_le_of_gt left,qAbove.le,left.le]
      · exact matching c later

theorem exists_representative (breaks : List ℚ)
    (loIn : (0 : ℚ) ∈ breaks) (hiIn : (1 : ℚ) ∈ breaks)
    {level : ℝ} (lo : 0 ≤ level) (hi : level ≤ 1) :
    ∃ q ∈ candidates breaks, (0 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧
      ∀ c ∈ breaks, ((q : ℝ) ≤ (c : ℝ) ↔ level ≤ (c : ℝ)) ∧
        ((c : ℝ) ≤ (q : ℝ) ↔ (c : ℝ) ≤ level) := by
  have sorted := List.pairwise_mergeSort' (α := ℚ) (· ≤ ·) breaks
  have low : (0 : ℚ) ∈ breaks.mergeSort (fun a b => a ≤ b) := List.mem_mergeSort.mpr loIn
  have high : (1 : ℚ) ∈ breaks.mergeSort (fun a b => a ≤ b) := List.mem_mergeSort.mpr hiIn
  unfold candidates
  split
  · rename_i eq
    rw [eq] at low
    exact (List.not_mem_nil low).elim
  · rename_i a tail eq
    rw [eq] at sorted low high
    have first : a ≤ 0 := by
      rcases List.mem_cons.mp low with equal | later
      · simp [← equal]
      · exact (List.pairwise_cons.mp sorted).1 _ later
    have left : (a : ℝ) ≤ 0 := by exact_mod_cast first
    obtain ⟨q,listed,agrees⟩ := after_representative a tail sorted (left.trans lo)
      ⟨1,high,by simpa using hi⟩
    have lower := (agrees 0 low).2.mpr (by simpa using lo)
    have upper := (agrees 1 high).1.mpr (by simpa using hi)
    refine ⟨q,listed,by simpa using lower,by simpa using upper,fun c mem => ?_⟩
    exact agrees c (eq ▸ List.mem_mergeSort.mpr mem)

end DirectedFlowCutGap.RationalThresholdRepresentatives
