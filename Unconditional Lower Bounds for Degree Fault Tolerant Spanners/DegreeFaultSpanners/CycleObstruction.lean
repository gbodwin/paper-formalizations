import DegreeFaultSpanners.GeometryWalk
import DegreeFaultSpanners.ShortReach
import Mathlib.Tactic.Abel

/-!
# Short cycles meet the algebraic failure relation

The compressed alternating-cycle form of Lemma 13. We put the protected
line at the end of the cycle and choose the first earlier occurrence of
its slope. The preceding arc is transverse; its distinct-slope budget,
not its original number of steps, is what gives a short-reach witness.
-/

namespace DegreeFaultSpanners

open scoped BigOperators

/-- Telescoping any initial segment of a finite sequence. -/
theorem sum_prefix_successive_sub {A : Type*} [AddCommGroup A] {r : ℕ}
    (a : Fin (r + 1) → A) (m : ℕ) (hm : m ≤ r) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < m),
      (a i.succ - a i.castSucc)) = a ⟨m, by omega⟩ - a 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmr : m < r := by omega
    have hfilter : Finset.univ.filter (fun i : Fin r => i.val < m + 1) =
        insert ⟨m, hmr⟩ (Finset.univ.filter (fun i : Fin r => i.val < m)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]
      omega
    rw [hfilter, Finset.sum_insert (by simp), ih (by omega)]
    change (a ⟨m + 1, by omega⟩ - a ⟨m, by omega⟩) +
      (a ⟨m, by omega⟩ - a 0) = a ⟨m + 1, by omega⟩ - a 0
    abel

variable {F : Type*} [Field F] {d r : ℕ}

/-- Lemma 13 in a genuine alternating-cycle encoding, with the reference line last. -/
theorem compressed_cycle_shortFailure
    (a : Fin (r + 1) → Point F d) (l : Fin r → Line F d)
    (hfrom : ∀ i : Fin r, a i.castSucc ∈ lineSet (l i))
    (hto : ∀ i : Fin r, a i.succ ∈ lineSet (l i))
    (hne : ∀ i : Fin r, a i.castSucc ≠ a i.succ)
    (hclosed : a (Fin.last r) = a 0) (hr : r ≤ d + 2)
    (hlinj : Function.Injective l) (ref : Fin r) (href : ref.val + 1 = r) :
    ∃ i : Fin r, i.val < ref.val ∧
      shortFailure (a 0) (l ref) (a i.castSucc) (l i) := by
  classical
  let t : Fin r → F := fun i => (l i).1
  let T : Finset (Fin r) := Finset.univ.filter (fun i => t i = t ref)
  have hrefT : ref ∈ T := by simp [T]
  have hT : T.Nonempty := ⟨ref, hrefT⟩
  let first : Fin r := T.min' hT
  have hfirstT : first ∈ T := Finset.min'_mem T hT
  have hfirstSlope : t first = t ref := (Finset.mem_filter.mp hfirstT).2
  have hminimal (i : Fin r) (hi : t i = t ref) : first ≤ i :=
    Finset.min'_le T i (by simp [T, hi])
  obtain ⟨j, hjne, hjslope⟩ :=
    closed_incidence_walk_no_singleton_slope a l hfrom hto hne hclosed hr ref
  have hjlt : j.val < ref.val := by
    have hj := j.isLt
    have hij : j.val ≠ ref.val := fun h => hjne (Fin.ext h)
    omega
  have hfirstlt : first.val < ref.val := by
    have hle := hminimal j hjslope
    exact lt_of_le_of_lt hle hjlt
  let P : Finset (Fin r) := Finset.univ.filter (fun i => i.val < first.val)
  let S : Finset F := P.image t
  let U : Finset F := Finset.univ.image t
  have htransverse : ∀ i ∈ P, t i ≠ t ref := by
    intro i hi heq
    have hlt := (Finset.mem_filter.mp hi).2
    have hle := hminimal i heq
    exact (not_lt_of_ge hle) hlt
  have hnot : t ref ∉ S := by
    intro h
    rcases Finset.mem_image.mp h with ⟨i, hi, heq⟩
    exact htransverse i hi heq
  have hsub : S ⊆ U := Finset.image_subset_image (Finset.filter_subset _ _)
  have hcard : S.card + 1 ≤ U.card := by
    have h := Finset.card_le_card
      (Finset.insert_subset_iff.mpr ⟨Finset.mem_image_of_mem t (Finset.mem_univ ref), hsub⟩)
    simpa only [Finset.card_insert_of_notMem hnot] using h
  have hbudget : 2 * (S.card + 1) ≤ d + 2 := by
    have hcount := closed_incidence_walk_two_mul_card_slopes_le a l hfrom hto hne hclosed hr
    change 2 * U.card ≤ r at hcount
    omega
  have hreach : ShortReach (d + 2) (t ref) (a 0) (a first.castSucc) := by
    apply shortReach_of_finset_moments P t
      (fun i => a i.succ 0 - a i.castSucc 0) htransverse hbudget
    intro q
    calc
      a first.castSucc q - a 0 q =
          ∑ i ∈ P, (a i.succ q - a i.castSucc q) := by
        symm
        exact sum_prefix_successive_sub (fun i => a i q) first.val (Nat.le_of_lt first.isLt)
      _ = ∑ i ∈ P, (a i.succ 0 - a i.castSucc 0) * t i ^ (q : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrFun (sub_eq_smul_slope_of_mem (hfrom i) (hto i)) q
  refine ⟨first, hfirstlt, ?_, hfirstSlope, hfrom first, hreach⟩
  intro heq
  have := congrArg Fin.val (hlinj heq)
  omega

end DegreeFaultSpanners
