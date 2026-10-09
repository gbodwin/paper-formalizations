import DegreeFaultSpanners.Incidence
import DegreeFaultSpanners.SlopeAlgebra
import Mathlib.Combinatorics.SimpleGraph.Paths
import Lean.Elab.Tactic.Omega

/-!
# The geometry of compressed incidence walks

The algebraic part of Lemma 9 of Bodwin--Lopez, arXiv:2607.07576v1,
and the distinct-slope counting step of Lemma 13.

A point-rooted alternating walk is represented by `r + 1` points and `r`
lines. Its incidences are explicit hypotheses. The non-backtracking
hypothesis used here is precisely that each passage through a line has
different point endpoints. Consequently this statement also applies to
walks which repeat a line, as required in Lemma 9.

The final section extracts this representation from actual point-to-point
`SimpleGraph.Walk`s and derives the conclusion for point-rooted cycles.
-/

namespace DegreeFaultSpanners

open scoped BigOperators

/-- Telescoping a finite sequence, with no cyclic-index arithmetic. -/
theorem sum_fin_successive_sub {A : Type*} [AddCommGroup A] {r : ℕ}
    (a : Fin (r + 1) → A) :
    (∑ i : Fin r, (a i.succ - a i.castSucc)) = a (Fin.last r) - a 0 := by
  rw [Finset.sum_sub_distrib]
  apply sub_eq_sub_iff_add_eq_add.mpr
  have h := (Fin.sum_univ_succ a).symm.trans (Fin.sum_univ_castSucc a)
  simpa only [add_comm] using h

variable {F : Type*} [Field F] {d r : ℕ}

/-- Closing an alternating incidence walk makes every slope moment vanish. -/
theorem closed_incidence_walk_moments
    (a : Fin (r + 1) → Point F d) (l : Fin r → Line F d)
    (hfrom : ∀ i : Fin r, a i.castSucc ∈ lineSet (l i))
    (hto : ∀ i : Fin r, a i.succ ∈ lineSet (l i))
    (hclosed : a (Fin.last r) = a 0) (q : Fin (d + 2)) :
    (∑ i : Fin r, (a i.succ 0 - a i.castSucc 0) * (l i).1 ^ (q : ℕ)) = 0 := by
  calc
    (∑ i : Fin r, (a i.succ 0 - a i.castSucc 0) * (l i).1 ^ (q : ℕ)) =
        ∑ i : Fin r, (a i.succ q - a i.castSucc q) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := congrFun (sub_eq_smul_slope_of_mem (hfrom i) (hto i)) q
      exact hi.symm
    _ = a (Fin.last r) q - a 0 q := sum_fin_successive_sub (fun i => a i q)
    _ = 0 := by rw [hclosed, sub_self]

/-- Lemma 9 for point-rooted compressed alternating closed walks.

Every occurrence of a line has another occurrence with the same slope.
The conclusion concerns occurrences, so the two line records may be equal.
-/
theorem closed_incidence_walk_no_singleton_slope
    (a : Fin (r + 1) → Point F d) (l : Fin r → Line F d)
    (hfrom : ∀ i : Fin r, a i.castSucc ∈ lineSet (l i))
    (hto : ∀ i : Fin r, a i.succ ∈ lineSet (l i))
    (hne : ∀ i : Fin r, a i.castSucc ≠ a i.succ)
    (hclosed : a (Fin.last r) = a 0) (hr : r ≤ d + 2)
    (i : Fin r) : ∃ j : Fin r, j ≠ i ∧ (l j).1 = (l i).1 := by
  apply no_singleton_slope hr (fun j => (l j).1)
    (fun j => a j.succ 0 - a j.castSucc 0) ?_ ?_ i
  · intro j
    exact sub_ne_zero.mpr (first_ne_of_ne_of_mem (hfrom j) (hto j) (hne j)).symm
  · exact closed_incidence_walk_moments a l hfrom hto hclosed

/-- If every value of a finite function occurs at least twice, the image
has at most half as many elements as the domain. -/
theorem two_mul_card_image_le_of_no_singleton {I T : Type*} [Fintype I]
    [DecidableEq T] (t : I → T)
    (h : ∀ i, ∃ j, j ≠ i ∧ t j = t i) :
    2 * (Finset.univ.image t).card ≤ Fintype.card I := by
  classical
  have hfiber : ∀ u ∈ Finset.univ.image t,
      2 ≤ (Finset.univ.filter (fun i => t i = u)).card := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨i, _, rfl⟩
    rcases h i with ⟨j, hji, ht⟩
    have hsub : ({i, j} : Finset I) ⊆ Finset.univ.filter (fun z => t z = t i) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · simp
      · simp [ht]
    have hcard := Finset.card_le_card hsub
    simpa [Ne.symm hji] using hcard
  calc
    2 * (Finset.univ.image t).card = ∑ _ ∈ Finset.univ.image t, 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ Finset.univ.image t,
        (Finset.univ.filter (fun i => t i = u)).card := Finset.sum_le_sum hfiber
    _ = (Finset.univ : Finset I).card :=
      (Finset.card_eq_sum_card_image t Finset.univ).symm
    _ = Fintype.card I := Finset.card_univ

/-- The distinct-slope counting step of Lemma 13, stated without division. -/
theorem closed_incidence_walk_two_mul_card_slopes_le [DecidableEq F]
    (a : Fin (r + 1) → Point F d) (l : Fin r → Line F d)
    (hfrom : ∀ i : Fin r, a i.castSucc ∈ lineSet (l i))
    (hto : ∀ i : Fin r, a i.succ ∈ lineSet (l i))
    (hne : ∀ i : Fin r, a i.castSucc ≠ a i.succ)
    (hclosed : a (Fin.last r) = a 0) (hr : r ≤ d + 2) :
    2 * (Finset.univ.image (fun i => (l i).1)).card ≤ r := by
  simpa only [Fintype.card_fin] using
    two_mul_card_image_le_of_no_singleton (fun i => (l i).1)
      (closed_incidence_walk_no_singleton_slope a l hfrom hto hne hclosed hr)

/-- In a cycle representation whose line occurrences are distinct,
the repeated slope is supplied by a genuinely parallel line. -/
theorem closed_incidence_walk_exists_parallel
    (a : Fin (r + 1) → Point F d) (l : Fin r → Line F d)
    (hfrom : ∀ i : Fin r, a i.castSucc ∈ lineSet (l i))
    (hto : ∀ i : Fin r, a i.succ ∈ lineSet (l i))
    (hne : ∀ i : Fin r, a i.castSucc ≠ a i.succ)
    (hclosed : a (Fin.last r) = a 0) (hr : r ≤ d + 2)
    (hinj : Function.Injective l) (i : Fin r) :
    ∃ j : Fin r, j ≠ i ∧ Parallel (l j) (l i) := by
  rcases closed_incidence_walk_no_singleton_slope a l hfrom hto hne hclosed hr i with
    ⟨j, hji, hs⟩
  exact ⟨j, hji, fun he => hji (hinj he), hs⟩

section GraphWalkBridge

variable {x y : Point F d} {v : Vertex F d}

/-- Even positions of a walk starting at a point are points. -/
theorem incidence_walk_even_vertex
    (p : (incidenceGraph F d).Walk (Sum.inl x) v) (i : ℕ)
    (hi : 2 * i ≤ p.length) :
    ∃ a : Point F d, p.getVert (2 * i) = Sum.inl a := by
  induction i with
  | zero => exact ⟨x, p.getVert_zero⟩
  | succ i ih =>
    obtain ⟨a, ha⟩ := ih (by omega)
    have hadj := p.adj_getVert_succ (i := 2 * i) (by omega)
    rw [ha] at hadj
    cases hv : p.getVert (2 * i + 1) with
    | inl b => rw [hv] at hadj; exact False.elim hadj
    | inr l =>
      have hadj' := p.adj_getVert_succ (i := 2 * i + 1) (by omega)
      rw [hv] at hadj'
      have he : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
      rw [he]
      cases hw : p.getVert (2 * i + 1 + 1) with
      | inl b => exact ⟨b, rfl⟩
      | inr m => rw [hw] at hadj'; exact False.elim hadj'

/-- Odd positions of a walk starting at a point are lines. -/
theorem incidence_walk_odd_vertex
    (p : (incidenceGraph F d).Walk (Sum.inl x) v) (i : ℕ)
    (hi : 2 * i + 1 ≤ p.length) :
    ∃ l : Line F d, p.getVert (2 * i + 1) = Sum.inr l := by
  obtain ⟨a, ha⟩ := incidence_walk_even_vertex p i (by omega)
  have hadj := p.adj_getVert_succ (i := 2 * i) (by omega)
  rw [ha] at hadj
  cases hv : p.getVert (2 * i + 1) with
  | inl b => rw [hv] at hadj; exact False.elim hadj
  | inr l => exact ⟨l, rfl⟩

/-- Every point-to-point incidence walk has even length. -/
theorem incidence_walk_length_eq_twice_half
    (p : (incidenceGraph F d).Walk (Sum.inl x) (Sum.inl y)) :
    p.length = 2 * (p.length / 2) := by
  have hmod := Nat.mod_lt p.length (by omega : 0 < 2)
  by_contra h
  have hodd : 2 * (p.length / 2) + 1 = p.length := by omega
  obtain ⟨l, hl⟩ := incidence_walk_odd_vertex p (p.length / 2) (by omega)
  rw [hodd, p.getVert_length] at hl
  cases hl

/-- A checked extraction of alternating coordinates from a genuine walk. -/
structure IncidenceWalkEncoding
    (p : (incidenceGraph F d).Walk (Sum.inl x) (Sum.inl y)) where
  halfLength : ℕ
  points : Fin (halfLength + 1) → Point F d
  lines : Fin halfLength → Line F d
  length_eq : p.length = 2 * halfLength
  get_even : ∀ i : Fin (halfLength + 1), p.getVert (2 * (i : ℕ)) = Sum.inl (points i)
  get_odd : ∀ i : Fin halfLength, p.getVert (2 * (i : ℕ) + 1) = Sum.inr (lines i)

/-- No representation assumptions are required from the caller. -/
noncomputable def incidenceWalkEncoding
    (p : (incidenceGraph F d).Walk (Sum.inl x) (Sum.inl y)) :
    IncidenceWalkEncoding p := by
  classical
  let r := p.length / 2
  have hlen : p.length = 2 * r := incidence_walk_length_eq_twice_half p
  have heven (i : Fin (r + 1)) := incidence_walk_even_vertex p i.val (by omega)
  have hodd (i : Fin r) := incidence_walk_odd_vertex p i.val (by omega)
  exact
    { halfLength := r
      points := fun i => Classical.choose (heven i)
      lines := fun i => Classical.choose (hodd i)
      length_eq := hlen
      get_even := fun i => Classical.choose_spec (heven i)
      get_odd := fun i => Classical.choose_spec (hodd i) }

namespace IncidenceWalkEncoding

variable {p : (incidenceGraph F d).Walk (Sum.inl x) (Sum.inl y)}

theorem from_mem (e : IncidenceWalkEncoding p) (i : Fin e.halfLength) :
    e.points i.castSucc ∈ lineSet (e.lines i) := by
  have h := p.adj_getVert_succ (i := 2 * i.val) (by have := e.length_eq; omega)
  have hp := e.get_even i.castSucc
  simp only [Fin.val_castSucc] at hp
  rw [hp, e.get_odd i] at h
  exact h

theorem to_mem (e : IncidenceWalkEncoding p) (i : Fin e.halfLength) :
    e.points i.succ ∈ lineSet (e.lines i) := by
  have h := p.adj_getVert_succ (i := 2 * i.val + 1) (by have := e.length_eq; omega)
  rw [e.get_odd i, show 2 * i.val + 1 + 1 = 2 * (i.succ : ℕ) by simp; omega,
    e.get_even i.succ] at h
  exact h

theorem first_point (e : IncidenceWalkEncoding p) : e.points 0 = x := by
  have h := e.get_even 0
  simpa using h.symm

theorem last_point (e : IncidenceWalkEncoding p) :
    e.points (Fin.last e.halfLength) = y := by
  have h := e.get_even (Fin.last e.halfLength)
  simp only [Fin.val_last, ← e.length_eq, p.getVert_length, Sum.inl.injEq] at h
  exact h.symm

variable {c : (incidenceGraph F d).Walk (Sum.inl x) (Sum.inl x)}

theorem closed (e : IncidenceWalkEncoding c) :
    e.points (Fin.last e.halfLength) = e.points 0 := by
  rw [e.last_point, e.first_point]

/-- Lemma 9 for actual point-rooted closed graph walks, with the usual
no-immediate-reversal condition written in terms of successive vertices. -/
theorem no_singleton_slope_of_nonbacktracking (e : IncidenceWalkEncoding c)
    (hnb : ∀ n, n + 2 ≤ c.length → c.getVert n ≠ c.getVert (n + 2))
    (hlen : c.length ≤ 2 * (d + 2)) (i : Fin e.halfLength) :
    ∃ j : Fin e.halfLength, j ≠ i ∧ (e.lines j).1 = (e.lines i).1 := by
  apply closed_incidence_walk_no_singleton_slope e.points e.lines e.from_mem e.to_mem
    ?_ e.closed ?_ i
  · intro j hj
    have hn := hnb (2 * j.val) (by have := e.length_eq; omega)
    apply hn
    have hp := e.get_even j.castSucc
    simp only [Fin.val_castSucc] at hp
    rw [hp,
      show 2 * j.val + 2 = 2 * (j.succ : ℕ) by simp; omega,
      e.get_even j.succ, hj]
  · have := e.length_eq
    omega

theorem points_ne_of_isCycle (e : IncidenceWalkEncoding c) (hc : c.IsCycle)
    (i : Fin e.halfLength) : e.points i.castSucc ≠ e.points i.succ := by
  have hn := hc.getVert_sub_one_ne_getVert_add_one
    (i := 2 * i.val + 1) (by have := e.length_eq; omega)
  rw [show 2 * i.val + 1 - 1 = 2 * (i.castSucc : ℕ) by simp,
    show 2 * i.val + 1 + 1 = 2 * (i.succ : ℕ) by simp; omega,
    e.get_even i.castSucc, e.get_even i.succ] at hn
  exact fun h => hn (congrArg Sum.inl h)

theorem lines_injective_of_isCycle (e : IncidenceWalkEncoding c) (hc : c.IsCycle) :
    Function.Injective e.lines := by
  intro i j hij
  have h : c.getVert (2 * i.val + 1) = c.getVert (2 * j.val + 1) := by
    rw [e.get_odd i, e.get_odd j, hij]
  have heq := hc.getVert_injOn (by simp only [Set.mem_ofPred_eq]; have := e.length_eq; omega)
    (by simp only [Set.mem_ofPred_eq]; have := e.length_eq; omega) h
  apply Fin.ext
  omega

/-- A graph-cycle version of the repeated-slope conclusion, with the
encoding obtained from the actual graph walk. -/
theorem exists_parallel_of_isCycle (e : IncidenceWalkEncoding c) (hc : c.IsCycle)
    (hlen : c.length ≤ 2 * (d + 2)) (i : Fin e.halfLength) :
    ∃ j : Fin e.halfLength, j ≠ i ∧ Parallel (e.lines j) (e.lines i) := by
  apply closed_incidence_walk_exists_parallel e.points e.lines e.from_mem e.to_mem
    (e.points_ne_of_isCycle hc) e.closed ?_ (e.lines_injective_of_isCycle hc) i
  have := e.length_eq
  omega

/-- The slope-count step applies to genuine incidence-graph cycles. -/
theorem two_mul_card_slopes_le_of_isCycle [DecidableEq F]
    (e : IncidenceWalkEncoding c) (hc : c.IsCycle) (hlen : c.length ≤ 2 * (d + 2)) :
    2 * (Finset.univ.image (fun i => (e.lines i).1)).card ≤ e.halfLength := by
  apply closed_incidence_walk_two_mul_card_slopes_le e.points e.lines e.from_mem e.to_mem
    (e.points_ne_of_isCycle hc) e.closed
  have := e.length_eq
  omega

end IncidenceWalkEncoding

/-- Every line on an actual short point-rooted incidence-graph cycle has
a distinct parallel line on the same cycle. No encoding is supplied by
the caller. This is the first geometric step of Lemma 13. -/
theorem incidence_cycle_exists_parallel
    (c : (incidenceGraph F d).Walk (Sum.inl x) (Sum.inl x)) (hc : c.IsCycle)
    (hlen : c.length ≤ 2 * (d + 2)) (l : Line F d)
    (hl : Sum.inr l ∈ c.support) :
    ∃ m : Line F d, Sum.inr m ∈ c.support ∧ Parallel m l := by
  let e := incidenceWalkEncoding c
  obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hl
  have hnlt : n < c.length := by
    by_contra h
    have heq : n = c.length := by omega
    rw [heq, c.getVert_length] at hn
    cases hn
  have hmod := Nat.mod_lt n (by omega : 0 < 2)
  have hodd : 2 * (n / 2) + 1 = n := by
    by_contra h
    have heven : 2 * (n / 2) = n := by omega
    obtain ⟨a, ha⟩ := incidence_walk_even_vertex c (n / 2) (by omega)
    rw [heven, hn] at ha
    cases ha
  let i : Fin e.halfLength := ⟨n / 2, by have := e.length_eq; omega⟩
  have hil : e.lines i = l := by
    have h := e.get_odd i
    change c.getVert (2 * (n / 2) + 1) = Sum.inr (e.lines i) at h
    rw [hodd, hn, Sum.inr.injEq] at h
    exact h.symm
  obtain ⟨j, _, hj⟩ := e.exists_parallel_of_isCycle hc hlen i
  refine ⟨e.lines j, ?_, ?_⟩
  · rw [← e.get_odd j]
    exact c.getVert_mem_support _
  · simpa only [hil] using hj

end GraphWalkBridge

end DegreeFaultSpanners
