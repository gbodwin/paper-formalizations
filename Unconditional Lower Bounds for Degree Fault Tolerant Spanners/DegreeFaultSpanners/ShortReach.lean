import DegreeFaultSpanners.SlopeAlgebra
import DegreeFaultSpanners.Incidence
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Algebraic short transverse reachability

This file proves the algebraic unique-endpoint argument underlying Lemma 10
of Bodwin--Lopez, arXiv:2607.07576v1.  A short-reach witness is a sparse
linear combination of moment-curve directions, all avoiding a designated
slope.  Its support has size at most `floor (k / 2 - 1)`, expressed without
division as `2 * (S.card + 1) ≤ k`.

The definition here is algebraic.  In particular, this file does not assert
that every witness is realized by a simple path in an incidence graph.
The main result says that two algebraically short-reachable endpoints on
the same designated-slope line coincide.  All results hold over any field.
-/

namespace DegreeFaultSpanners

open scoped BigOperators

variable {F : Type*} [Field F]

/-- The first `k` coordinates of the moment curve. -/
def momentCurve (k : ℕ) (t : F) : Fin k → F := fun j => t ^ (j : ℕ)

/-- A displacement represented by a finite set of moment-curve directions. -/
def SparseCombination (k : ℕ) (S : Finset F) (c : F → F) (v : Fin k → F) : Prop :=
  v = ∑ s ∈ S, c s • momentCurve k s

/-- Algebraic bounded transverse reachability, with the designated slope excluded. -/
def ShortReach (k : ℕ) (t : F) (a b : Fin k → F) : Prop :=
  ∃ (S : Finset F) (c : F → F),
    t ∉ S ∧ 2 * (S.card + 1) ≤ k ∧ SparseCombination k S c (b - a)

/-- The bound in a short-reach witness explicitly forces dimension at least two. -/
theorem ShortReach.two_le {k : ℕ} {t : F} {a b : Fin k → F}
    (h : ShortReach k t a b) : 2 ≤ k := by
  obtain ⟨S, c, ht, hcard, hcomb⟩ := h
  omega

/-- A point is short-reachable from itself whenever the dimension is at least two. -/
theorem shortReach_refl {k : ℕ} (hk : 2 ≤ k) (t : F) (a : Fin k → F) :
    ShortReach k t a a := by
  exact ⟨∅, 0, by simp, by simpa using hk, by simp [SparseCombination]⟩

/-- Reversing a short displacement preserves its support and transverse direction. -/
theorem ShortReach.symm {k : ℕ} {t : F} {a b : Fin k → F}
    (h : ShortReach k t a b) : ShortReach k t b a := by
  obtain ⟨S, c, ht, hcard, hcomb⟩ := h
  refine ⟨S, fun s => -c s, ht, hcard, ?_⟩
  dsimp [SparseCombination] at hcomb ⊢
  rw [← neg_sub b a, hcomb]
  simp only [neg_smul, Finset.sum_neg_distrib]

/--
Finite-index version of the grouped-displacement construction.  This applies
directly to an arc or suffix selected by a finite set of indices, without
reindexing it as `Fin r`.  Only the number of distinct slopes is bounded.
-/
theorem shortReach_of_finset_moments [DecidableEq F] {I : Type*} [DecidableEq I]
    {k : ℕ} {t : F} {a b : Fin k → F} (J : Finset I) (u c : I → F)
    (hu : ∀ i ∈ J, u i ≠ t) (hcard : 2 * ((J.image u).card + 1) ≤ k)
    (hm : ∀ j : Fin k, b j - a j = ∑ i ∈ J, c i * u i ^ (j : ℕ)) :
    ShortReach k t a b := by
  classical
  let S := J.image u
  let d : F → F := fun s => ∑ i ∈ J.filter (fun i => u i = s), c i
  refine ⟨S, d, ?_, hcard, ?_⟩
  · intro ht
    obtain ⟨i, hi, hit⟩ := Finset.mem_image.mp ht
    exact hu i hi hit
  · funext j
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, momentCurve]
    rw [hm j]
    symm
    calc
      (∑ s ∈ S, d s * s ^ (j : ℕ)) =
          ∑ s ∈ S, ∑ i ∈ J.filter (fun i => u i = s), c i * u i ^ (j : ℕ) := by
        apply Finset.sum_congr rfl
        intro s hs
        dsimp only [d]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = ∑ i ∈ J, c i * u i ^ (j : ℕ) :=
        Finset.sum_fiberwise_of_maps_to
          (fun i hi => Finset.mem_image_of_mem u hi) _

/--
A sequence of transverse moment displacements yields a short-reach witness
when the number of distinct slopes is bounded.  The sequence itself may be
longer: grouping repeated slopes is the algebraic path-compression step.
-/
theorem shortReach_of_support_moments [DecidableEq F] {k r : ℕ} {t : F}
    {a b : Fin k → F} (u c : Fin r → F) (hu : ∀ i, u i ≠ t)
    (hcard : 2 * ((Finset.univ.image u).card + 1) ≤ k)
    (hm : ∀ j : Fin k, b j - a j = ∑ i : Fin r, c i * u i ^ (j : ℕ)) :
    ShortReach k t a b := by
  classical
  let S := Finset.univ.image u
  let d : F → F := fun s => ∑ i ∈ Finset.univ.filter (fun i => u i = s), c i
  refine ⟨S, d, ?_, ?_, ?_⟩
  · simpa [S, Finset.mem_image] using hu
  · exact hcard
  · funext j
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, momentCurve]
    rw [hm j]
    symm
    calc
      (∑ s ∈ S, d s * s ^ (j : ℕ)) =
          ∑ s ∈ S, ∑ i ∈ Finset.univ.filter (fun i => u i = s), c i * u i ^ (j : ℕ) := by
        apply Finset.sum_congr rfl
        intro s hs
        dsimp only [d]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = ∑ i : Fin r, c i * u i ^ (j : ℕ) :=
        Finset.sum_fiberwise_of_maps_to
          (fun i _ => Finset.mem_image_of_mem u (Finset.mem_univ i)) _

/--
A bounded sequence is a special case of the distinct-support bound.  This is
the algebraic input needed after telescoping a bounded-length graph walk.
-/
theorem shortReach_of_moments {k r : ℕ} {t : F} {a b : Fin k → F}
    (u c : Fin r → F) (hu : ∀ i, u i ≠ t) (hr : 2 * (r + 1) ≤ k)
    (hm : ∀ j : Fin k, b j - a j = ∑ i : Fin r, c i * u i ^ (j : ℕ)) :
    ShortReach k t a b := by
  classical
  apply shortReach_of_support_moments u c hu _ hm
  have hcard : (Finset.univ.image u).card ≤ r := by
    calc
      (Finset.univ.image u).card ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
      _ = r := Finset.card_fin r
  omega

/-- Moment independence, indexed directly by a finite support. -/
theorem finite_moment_coefficients_eq_zero {k : ℕ} (S : Finset F)
    (hcard : S.card ≤ k) (c : F → F)
    (hm : ∀ j : Fin k, (∑ s ∈ S, c s * s ^ (j : ℕ)) = 0) :
    ∀ s ∈ S, c s = 0 := by
  classical
  have hz : (fun s : S => c s.val) = 0 :=
    coefficients_eq_zero_of_moments_fintype
      (by simpa only [Fintype.card_coe] using hcard)
      (fun s : S => s.val) (fun s : S => c s.val) Subtype.val_injective (by
        intro j
        calc
          (∑ s : S, c s.val * s.val ^ (j : ℕ)) =
              ∑ s ∈ S, c s * s ^ (j : ℕ) :=
                Finset.sum_coe_sort S (fun s : F => c s * s ^ (j : ℕ))
          _ = 0 := hm j)
  intro s hs
  exact congrFun hz ⟨s, hs⟩

/-- A short sum avoiding a direction cannot equal a nonzero multiple of that direction. -/
theorem sparse_moments_separate {k : ℕ} (S : Finset F) (t : F)
    (ht : t ∉ S) (hcard : S.card + 1 ≤ k) (c : F → F) (q : F)
    (hm : ∀ j : Fin k, (∑ s ∈ S, c s * s ^ (j : ℕ)) = q * t ^ (j : ℕ)) :
    q = 0 := by
  classical
  let d : F → F := fun s => if s = t then -q else c s
  have hz := finite_moment_coefficients_eq_zero (insert t S)
    (by simpa [Finset.card_insert_of_notMem ht] using hcard) d (by
      intro j
      rw [Finset.sum_insert ht]
      have heq : (∑ s ∈ S, d s * s ^ (j : ℕ)) = ∑ s ∈ S, c s * s ^ (j : ℕ) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hst : s ≠ t := by rintro rfl; exact ht hs
        simp [d, hst]
      rw [heq, hm j]
      simp [d])
  have hneg : -q = 0 := by simpa [d] using hz t (Finset.mem_insert_self t S)
  exact neg_eq_zero.mp hneg

private theorem sum_restrict_support [DecidableEq F] (S U : Finset F) (hSU : S ⊆ U)
    (c : F → F) (j : ℕ) :
    (∑ s ∈ U, (if s ∈ S then c s else 0) * s ^ j) =
      ∑ s ∈ S, c s * s ^ j := by
  classical
  calc
    (∑ s ∈ U, (if s ∈ S then c s else 0) * s ^ j) =
        ∑ s ∈ S, (if s ∈ S then c s else 0) * s ^ j := by
      symm
      apply Finset.sum_subset hSU
      intro s hsU hsS
      simp [hsS]
    _ = ∑ s ∈ S, c s * s ^ j := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [hs]

/--
General unique-endpoint criterion: the two support sizes, plus the target
direction, fit within the available number of moment coordinates.
-/
theorem sparse_endpoint_unique {k : ℕ} {t : F} {a b b' : Fin k → F}
    (S T : Finset F) (c d : F → F)
    (htS : t ∉ S) (htT : t ∉ T) (hcard : S.card + T.card + 1 ≤ k)
    (hb : SparseCombination k S c (b - a))
    (hb' : SparseCombination k T d (b' - a))
    (hline : ∃ q : F, b - b' = q • momentCurve k t) :
    b = b' := by
  classical
  obtain ⟨q, hq⟩ := hline
  let U := S ∪ T
  let e : F → F := fun s => (if s ∈ S then c s else 0) - (if s ∈ T then d s else 0)
  have hcardU : U.card + 1 ≤ k := by
    have hU : U.card ≤ S.card + T.card := Finset.card_union_le S T
    omega
  have htU : t ∉ U := by simpa [U] using And.intro htS htT
  have hzero : q = 0 := sparse_moments_separate U t htU hcardU e q (by
    intro j
    have hbcoord : b j - a j = ∑ s ∈ S, c s * s ^ (j : ℕ) := by
      simpa [SparseCombination, momentCurve, Finset.sum_apply] using congrFun hb j
    have hb'coord : b' j - a j = ∑ s ∈ T, d s * s ^ (j : ℕ) := by
      simpa [SparseCombination, momentCurve, Finset.sum_apply] using congrFun hb' j
    have hqcoord : b j - b' j = q * t ^ (j : ℕ) := by
      simpa [momentCurve] using congrFun hq j
    calc
      (∑ s ∈ U, e s * s ^ (j : ℕ)) =
          (∑ s ∈ U, (if s ∈ S then c s else 0) * s ^ (j : ℕ)) -
          (∑ s ∈ U, (if s ∈ T then d s else 0) * s ^ (j : ℕ)) := by
        simp only [e, sub_mul, Finset.sum_sub_distrib]
      _ = (∑ s ∈ S, c s * s ^ (j : ℕ)) - (∑ s ∈ T, d s * s ^ (j : ℕ)) := by
        rw [sum_restrict_support S U (Finset.subset_union_left) c,
          sum_restrict_support T U (Finset.subset_union_right) d]
      _ = (b j - a j) - (b' j - a j) := by rw [← hbcoord, ← hb'coord]
      _ = b j - b' j := by ring
      _ = q * t ^ (j : ℕ) := hqcoord)
  exact sub_eq_zero.mp (by simpa [hzero] using hq)

/--
The algebraic component of Lemma 10: short transverse witnesses have at most
one endpoint on any line with the designated direction.
-/
theorem ShortReach.endpoint_unique {k : ℕ} {t : F} {a b b' : Fin k → F}
    (hb : ShortReach k t a b) (hb' : ShortReach k t a b')
    (hline : ∃ q : F, b - b' = q • momentCurve k t) :
    b = b' := by
  obtain ⟨S, c, htS, hS, hc⟩ := hb
  obtain ⟨T, d, htT, hT, hd⟩ := hb'
  exact sparse_endpoint_unique S T c d htS htT (by omega) hc hd hline

/-- Geometric form of the algebraic unique-endpoint result for the incidence lines. -/
theorem ShortReach.endpoint_unique_on_line {d : ℕ} {l : Line F d}
    {a b b' : Point F d}
    (hb : ShortReach (d + 2) l.1 a b) (hb' : ShortReach (d + 2) l.1 a b')
    (hbl : b ∈ lineSet l) (hb'l : b' ∈ lineSet l) :
    b = b' := by
  apply hb.endpoint_unique hb'
  exact ⟨b 0 - b' 0, sub_eq_smul_slope_of_mem hb'l hbl⟩

/--
A designated endpoint can be chosen on every target line.  When no endpoint
is reachable, an arbitrary point on that nonempty line suffices.
-/
theorem exists_shortReach_endpoint {d : ℕ} (l : Line F d) (a : Point F d) :
    ∃ b ∈ lineSet l, ∀ b' ∈ lineSet l, ShortReach (d + 2) l.1 a b' → b' = b := by
  classical
  by_cases h : ∃ b ∈ lineSet l, ShortReach (d + 2) l.1 a b
  · obtain ⟨b, hbl, hb⟩ := h
    exact ⟨b, hbl, fun b' hb'l hb' => hb'.endpoint_unique_on_line hb hb'l hbl⟩
  · refine ⟨linePoint l 0, linePoint_mem l 0, ?_⟩
    intro b' hb'l hb'
    exact False.elim (h ⟨b', hb'l, hb'⟩)

/--
The algebraic version of the paper's failure relation.  A failed incidence
lies on a different line of the reference slope and has a short-reach witness.
Equivalence to the graph-path definition is a separate obligation.
-/
def shortFailure {d : ℕ} (a : Point F d) (l : Line F d)
    (b : Point F d) (m : Line F d) : Prop :=
  m ≠ l ∧ m.1 = l.1 ∧ b ∈ lineSet m ∧ ShortReach (d + 2) l.1 a b

/-- Each point belongs to at most one failed incidence. -/
theorem shortFailure_line_unique {d : ℕ} {a b : Point F d} {l m n : Line F d}
    (hm : shortFailure a l b m) (hn : shortFailure a l b n) : m = n := by
  exact eq_of_common_point_of_slope_eq (hm.2.1.trans hn.2.1.symm) hm.2.2.1 hn.2.2.1

/-- Each line belongs to at most one failed incidence. -/
theorem shortFailure_point_unique {d : ℕ} {a b b' : Point F d} {l m : Line F d}
    (hb : shortFailure a l b m) (hb' : shortFailure a l b' m) : b = b' := by
  apply hb.2.2.2.endpoint_unique hb'.2.2.2
  refine ⟨b 0 - b' 0, ?_⟩
  have h := sub_eq_smul_slope_of_mem hb'.2.2.1 hb.2.2.1
  rw [hb.2.1] at h
  exact h

/-- No failure edge touches the reference point when it is on the reference line. -/
theorem shortFailure_not_source {d : ℕ} {a : Point F d} {l m : Line F d}
    (ha : a ∈ lineSet l) : ¬ shortFailure a l a m := by
  intro hm
  exact hm.1 (eq_of_common_point_of_slope_eq hm.2.1 hm.2.2.1 ha)

/-- The failure relation together with its distinguished reference incidence. -/
def augmentedShortFailure {d : ℕ} (a : Point F d) (l : Line F d)
    (b : Point F d) (m : Line F d) : Prop :=
  (b = a ∧ m = l) ∨ shortFailure a l b m

/-- Adding the reference incidence preserves uniqueness at every point. -/
theorem augmentedShortFailure_line_unique {d : ℕ} {a b : Point F d}
    {l m n : Line F d} (ha : a ∈ lineSet l)
    (hm : augmentedShortFailure a l b m) (hn : augmentedShortFailure a l b n) :
    m = n := by
  rcases hm with ⟨hba, hml⟩ | hm <;> rcases hn with ⟨hba', hnl⟩ | hn
  · exact hml.trans hnl.symm
  · subst b
    exact False.elim (shortFailure_not_source ha hn)
  · subst b
    exact False.elim (shortFailure_not_source ha hm)
  · exact shortFailure_line_unique hm hn

/-- Adding the reference incidence preserves uniqueness at every line. -/
theorem augmentedShortFailure_point_unique {d : ℕ} {a b b' : Point F d}
    {l m : Line F d}
    (hb : augmentedShortFailure a l b m) (hb' : augmentedShortFailure a l b' m) :
    b = b' := by
  rcases hb with ⟨hba, hml⟩ | hb <;> rcases hb' with ⟨hb'a, hml'⟩ | hb'
  · exact hba.trans hb'a.symm
  · exact False.elim (hb'.1 hml)
  · exact False.elim (hb.1 hml')
  · exact shortFailure_point_unique hb hb'

/-- Every pair in the augmented relation is an actual point-line incidence. -/
theorem augmentedShortFailure_incident {d : ℕ} {a b : Point F d} {l m : Line F d}
    (ha : a ∈ lineSet l) (h : augmentedShortFailure a l b m) : b ∈ lineSet m := by
  rcases h with ⟨rfl, rfl⟩ | h
  · exact ha
  · exact h.2.2.1

end DegreeFaultSpanners
