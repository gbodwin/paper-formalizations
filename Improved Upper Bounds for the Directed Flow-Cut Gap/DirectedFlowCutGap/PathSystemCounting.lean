import Mathlib

/-!
# Finite counting for indexed ordered path systems

These are the graph-independent counting facts behind the base-path lemma (Lemma 19,
printed page 14, `body.tex` line 542) of arXiv:2604.03412v3. A family is an indexed collection of actual vertex lists:
identical lists at distinct indices remain distinct incidences. Individual
lists are assumed nodup only when converting vertex incidences to lengths.

Prefixes and suffixes are the first and last `length / 4` entries in the
original list order. They are frozen here; later deletion schemes must use
subsets of these original suffixes. For lengths at least eight, suffix mass
is at least one eighth of total incidence. The resulting base-path bound
has the explicit factor 64; no coefficient-one estimate is inferred from
asymptotic notation. Graph reachability and witness construction are separate.
-/

namespace DirectedFlowCutGap.PathSystemCounting

noncomputable section

open scoped BigOperators Classical

variable {I V P : Type*}

/-- The ordered first quarter, rounded down. -/
def quarterPrefix (p : List V) : List V := p.take (p.length / 4)

/-- The ordered last quarter, rounded down. -/
def quarterSuffix (p : List V) : List V := p.drop (p.length - p.length / 4)

@[simp] theorem quarterPrefix_length (p : List V) :
    (quarterPrefix p).length = p.length / 4 := by
  simp [quarterPrefix, Nat.div_le_self]

@[simp] theorem quarterSuffix_length (p : List V) :
    (quarterSuffix p).length = p.length / 4 := by
  simp only [quarterSuffix, List.length_drop]
  have := Nat.div_le_self p.length 4
  omega

/-- Taking the quarter preserves the actual list order. -/
theorem quarterPrefix_sublist (p : List V) : List.Sublist (quarterPrefix p) p :=
  List.take_sublist _ _

/-- Taking the quarter preserves the actual list order. -/
theorem quarterSuffix_sublist (p : List V) : List.Sublist (quarterSuffix p) p :=
  List.drop_sublist _ _

theorem quarterPrefix_nodup {p : List V} (h : p.Nodup) :
    (quarterPrefix p).Nodup := h.sublist (quarterPrefix_sublist p)

theorem quarterSuffix_nodup {p : List V} (h : p.Nodup) :
    (quarterSuffix p).Nodup := h.sublist (quarterSuffix_sublist p)

theorem mem_of_mem_quarterPrefix {p : List V} {v : V}
    (h : v ∈ quarterPrefix p) : v ∈ p := (quarterPrefix_sublist p).subset h

theorem mem_of_mem_quarterSuffix {p : List V} {v : V}
    (h : v ∈ quarterSuffix p) : v ∈ p := (quarterSuffix_sublist p).subset h

/-- The floor loss is explicit, with a stated small-length condition. -/
theorem length_le_eight_mul_quarter {q : ℕ} (hq : 8 ≤ q) :
    q ≤ 8 * (q / 4) := by omega

theorem quarterSuffix_mass_lower_bound {p : List V} (hp : 8 ≤ p.length) :
    p.length ≤ 8 * (quarterSuffix p).length := by
  simpa using length_le_eight_mul_quarter hp

theorem quarterPrefix_mass_lower_bound {p : List V} (hp : 8 ≤ p.length) :
    p.length ≤ 8 * (quarterPrefix p).length := by
  simpa using length_le_eight_mul_quarter hp

/-- Every original prefix index and suffix index are separated by at least
half the original vertex count. This statement includes all integer rounding. -/
theorem prefix_suffix_index_separation {q a b : ℕ}
    (ha : a < q / 4) (hb : q - q / 4 ≤ b) : q ≤ 2 * (b - a) := by
  omega

section Finite

variable [Fintype I] [Fintype V]

/-- Total vertex incidences, with multiplicity across indices. -/
def totalIncidence (paths : I → List V) : ℕ := ∑ i, (paths i).length

/-- Total original suffix incidences. -/
def suffixIncidence (paths : I → List V) : ℕ :=
  totalIncidence (fun i => quarterSuffix (paths i))

/-- Number of indexed lists containing a vertex. -/
def degree (paths : I → List V) (v : V) : ℕ := by
  classical
  exact ∑ i, if v ∈ paths i then 1 else 0

/-- Number of original ordered suffixes containing a vertex. -/
def suffixDegree (paths : I → List V) (v : V) : ℕ :=
  degree (fun i => quarterSuffix (paths i)) v

/-- The suffix-degree sum along a candidate base list. -/
def baseScore (paths : I → List V) (i : I) : ℕ := by
  classical
  exact ∑ v ∈ (paths i).toFinset, suffixDegree paths v

/-- Average vertex degree in the ambient vertex set. -/
def averageDegree (paths : I → List V) : ℝ :=
  (totalIncidence paths : ℝ) / Fintype.card V

omit [Fintype V] in
/-- The indicator definition is exactly the number of family indices. -/
theorem degree_eq_card (paths : I → List V) (v : V) :
    degree paths v = (Finset.univ.filter (fun i => v ∈ paths i)).card := by
  classical
  simp [degree]

/-- Weighted incidence double counting. No nodup assumption is needed here:
both sides count membership once within each indexed list. -/
theorem weighted_double_count (paths : I → List V) (w : V → ℕ) :
    (∑ i, ∑ v ∈ (paths i).toFinset, w v) =
      ∑ v, degree paths v * w v := by
  classical
  simp only [degree, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

/-- Exact double counting of vertex-list lengths and vertex degrees. -/
theorem incidence_double_count (paths : I → List V)
    (hnd : ∀ i, (paths i).Nodup) :
    totalIncidence paths = ∑ v, degree paths v := by
  classical
  have h := weighted_double_count paths (fun _ => 1)
  simpa [totalIncidence, List.toFinset_card_of_nodup, hnd] using h

/-- Exact suffix counting retains multiplicity between distinct indices. -/
theorem suffix_incidence_double_count (paths : I → List V)
    (hnd : ∀ i, (paths i).Nodup) :
    suffixIncidence paths = ∑ v, suffixDegree paths v := by
  exact incidence_double_count (fun i => quarterSuffix (paths i))
    (fun i => quarterSuffix_nodup (hnd i))

omit [Fintype V] in
theorem suffixDegree_le_degree (paths : I → List V) (v : V) :
    suffixDegree paths v ≤ degree paths v := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hs : v ∈ quarterSuffix (paths i)
  · simp [hs, mem_of_mem_quarterSuffix hs]
  · simp [hs]

/-- All base scores sum to the exact mixed degree product. -/
theorem sum_baseScore (paths : I → List V) :
    (∑ i, baseScore paths i) = ∑ v, degree paths v * suffixDegree paths v := by
  exact weighted_double_count paths (suffixDegree paths)

/-- Restricting every candidate base list to its original suffix gives the
exact sum of squared suffix degrees. -/
theorem suffix_score_double_count (paths : I → List V) :
    (∑ i, ∑ v ∈ (quarterSuffix (paths i)).toFinset, suffixDegree paths v) =
      ∑ v, suffixDegree paths v ^ 2 := by
  classical
  simpa [suffixDegree, pow_two] using
    weighted_double_count (fun i => quarterSuffix (paths i)) (suffixDegree paths)

theorem sum_suffixDegree_sq_le_sum_baseScore (paths : I → List V) :
    (∑ v, suffixDegree paths v ^ 2) ≤ ∑ i, baseScore paths i := by
  rw [sum_baseScore]
  apply Finset.sum_le_sum
  intro v _
  simpa [pow_two] using
    Nat.mul_le_mul_right (suffixDegree paths v) (suffixDegree_le_degree paths v)

/-- Exact finite Cauchy--Schwarz for the original suffix-degree sequence. -/
theorem suffix_cauchy_schwarz (paths : I → List V)
    (hnd : ∀ i, (paths i).Nodup) :
    suffixIncidence paths ^ 2 ≤
      Fintype.card V * ∑ v, suffixDegree paths v ^ 2 := by
  rw [suffix_incidence_double_count paths hnd]
  simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V)
    (fun _ => (1 : ℕ)) (suffixDegree paths)

omit [Fintype V] in
theorem totalIncidence_le_eight_suffixIncidence (paths : I → List V)
    (hlength : ∀ i, 8 ≤ (paths i).length) :
    totalIncidence paths ≤ 8 * suffixIncidence paths := by
  change (∑ i, (paths i).length) ≤ 8 * ∑ i, (quarterSuffix (paths i)).length
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => quarterSuffix_mass_lower_bound (hlength i))

/-- The global base-score mass, with the factor lost by quarter rounding
and Cauchy--Schwarz made explicit. -/
theorem aggregate_baseScore_lower_bound (paths : I → List V)
    (hnd : ∀ i, (paths i).Nodup) (hlength : ∀ i, 8 ≤ (paths i).length) :
    totalIncidence paths ^ 2 ≤ 64 * Fintype.card V * ∑ i, baseScore paths i := by
  have hmass := totalIncidence_le_eight_suffixIncidence paths hlength
  have hsq : totalIncidence paths ^ 2 ≤ 64 * suffixIncidence paths ^ 2 := by
    simpa [mul_pow] using Nat.pow_le_pow_left hmass 2
  have hcs := suffix_cauchy_schwarz paths hnd
  have hscores := sum_suffixDegree_sq_le_sum_baseScore paths
  calc
    totalIncidence paths ^ 2 ≤ 64 * suffixIncidence paths ^ 2 := hsq
    _ ≤ 64 * (Fintype.card V * ∑ v, suffixDegree paths v ^ 2) :=
      Nat.mul_le_mul_left 64 hcs
    _ ≤ 64 * (Fintype.card V * ∑ i, baseScore paths i) :=
      Nat.mul_le_mul_left 64 (Nat.mul_le_mul_left _ hscores)
    _ = 64 * Fintype.card V * ∑ i, baseScore paths i := by ring

/-- An actual family index achieves the finite base-path bound. The indexed
family must be nonempty; no division or positivity of the ambient size is
needed in this denominator-free statement. -/
theorem exists_basePath [Nonempty I] (paths : I → List V)
    (hnd : ∀ i, (paths i).Nodup) (hlength : ∀ i, 8 ≤ (paths i).length) :
    ∃ i, totalIncidence paths ^ 2 ≤
      64 * Fintype.card I * Fintype.card V * baseScore paths i := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (baseScore paths)
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  have havg : (∑ j, baseScore paths j) ≤ Fintype.card I * baseScore paths i := by
    calc
      (∑ j, baseScore paths j) ≤ ∑ _j : I, baseScore paths i :=
        Finset.sum_le_sum (fun j _ => hi j (Finset.mem_univ j))
      _ = Fintype.card I * baseScore paths i := by simp
  calc
    totalIncidence paths ^ 2 ≤ 64 * Fintype.card V * ∑ j, baseScore paths j :=
      aggregate_baseScore_lower_bound paths hnd hlength
    _ ≤ 64 * Fintype.card V * (Fintype.card I * baseScore paths i) :=
      Nat.mul_le_mul_left _ havg
    _ = 64 * Fintype.card I * Fintype.card V * baseScore paths i := by ring

/-- Real-valued averaging form. Both nonempty domains are explicit, so its
denominator is strictly positive. -/
theorem exists_basePath_div [Nonempty I] [Nonempty V] (paths : I → List V)
    (hnd : ∀ i, (paths i).Nodup) (hlength : ∀ i, 8 ≤ (paths i).length) :
    ∃ i, (totalIncidence paths : ℝ) ^ 2 /
      (64 * (Fintype.card I : ℝ) * (Fintype.card V : ℝ)) ≤ baseScore paths i := by
  obtain ⟨i, hi⟩ := exists_basePath paths hnd hlength
  refine ⟨i, (div_le_iff₀ (by positivity)).mpr ?_⟩
  have hreal : (totalIncidence paths : ℝ) ^ 2 ≤
      64 * (Fintype.card I : ℝ) * (Fintype.card V : ℝ) * baseScore paths i := by
    exact_mod_cast hi
  nlinarith

/-- A uniform real lower bound on list lengths gives the familiar form in
terms of average degree, retaining the necessary factor 64. -/
theorem exists_basePath_of_length_lower_bound [Nonempty I] [Nonempty V]
    (paths : I → List V) (hnd : ∀ i, (paths i).Nodup)
    (hlength : ∀ i, 8 ≤ (paths i).length) (ell : ℝ)
    (hmin : ∀ i, ell ≤ ((paths i).length : ℝ)) :
    ∃ i, ell * averageDegree paths / 64 ≤ baseScore paths i := by
  obtain ⟨i, hi⟩ := exists_basePath paths hnd hlength
  have hI : (0 : ℝ) < Fintype.card I := by positivity
  have hV : (0 : ℝ) < Fintype.card V := by positivity
  have hminsum : (Fintype.card I : ℝ) * ell ≤ totalIncidence paths := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset I))
      (fun i _ => hmin i)
    simpa [totalIncidence, Nat.cast_sum] using hsum
  have hbase : (totalIncidence paths : ℝ) ^ 2 ≤
      64 * (Fintype.card I : ℝ) * (Fintype.card V : ℝ) * baseScore paths i := by
    exact_mod_cast hi
  have hmul := mul_le_mul_of_nonneg_right hminsum
    (show (0 : ℝ) ≤ totalIncidence paths by positivity)
  have hcancel : ell * (totalIncidence paths : ℝ) ≤
      64 * (Fintype.card V : ℝ) * baseScore paths i := by
    apply le_of_mul_le_mul_left (a := (Fintype.card I : ℝ)) ?_ hI
    nlinarith
  refine ⟨i, ?_⟩
  unfold averageDegree
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hV).mpr
  nlinarith

/-- The corrected witness scale yields the concrete base-path constant
`lambda = 256 * B`, using the actual minimum vertex count. -/
theorem exists_basePath_witness_scale [Nonempty I] [Nonempty V]
    (paths : I → List V) (hnd : ∀ i, (paths i).Nodup)
    (hlength : ∀ i, 8 ≤ (paths i).length) {B L : ℝ} (hB : 0 < B)
    (hmin : ∀ i, L / (4 * B) ≤ ((paths i).length : ℝ)) :
    ∃ i, L * averageDegree paths / (256 * B) ≤ baseScore paths i := by
  obtain ⟨i, hi⟩ := exists_basePath_of_length_lower_bound
    paths hnd hlength (L / (4 * B)) hmin
  refine ⟨i, ?_⟩
  convert hi using 1
  field_simp [ne_of_gt hB]
  ring

end Finite

/-- Same-label disjointness only constrains lists within one label. Equal
vertex lists with different labels are deliberately permitted. -/
def LabelDisjoint (paths : I → List V) (label : I → P) : Prop :=
  ∀ i j, label i = label j → i ≠ j → Disjoint (paths i).toFinset (paths j).toFinset

/-- Paths through one vertex have different labels. -/
theorem labels_injective_on_vertex (paths : I → List V) (label : I → P)
    (hd : LabelDisjoint paths label) (v : V) :
    Set.InjOn label {i | v ∈ paths i} := by
  intro i hi j hj hij
  by_contra hne
  exact Finset.disjoint_left.mp (hd i j hij hne)
    (by simpa using hi) (by simpa using hj)

/-- Global vertex congestion is at most the number of labels. Duplicate
lists across labels are still counted separately on the left-hand side. -/
theorem degree_le_label_card [Fintype I] [Fintype P] (paths : I → List V)
    (label : I → P) (hd : LabelDisjoint paths label) (v : V) :
    degree paths v ≤ Fintype.card P := by
  rw [degree_eq_card]
  apply Finset.card_le_card_of_injOn label
    (t := (Finset.univ : Finset P)) (fun _ _ => Finset.mem_univ _)
  intro i hi j hj hij
  exact labels_injective_on_vertex paths label hd v
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hij

/-- An endpoint can belong to at most one witness of a fixed label. -/
theorem label_vertex_card_le_one [Fintype I] (paths : I → List V)
    (label : I → P) (hd : LabelDisjoint paths label) (p : P) (v : V) :
    (Finset.univ.filter (fun i => label i = p ∧ v ∈ paths i)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact labels_injective_on_vertex paths label hd v hi'.2 hj'.2
    (hi'.1.trans hj'.1.symm)

/-- Two endpoint slots per fixed label; this counts an endpoint twice if the
two endpoints coincide, so remains a conservative bound for a loop. -/
theorem label_endpoint_capacity [Fintype I] (paths : I → List V)
    (label : I → P) (hd : LabelDisjoint paths label) (p : P) (x y : V) :
    (Finset.univ.filter (fun i => label i = p ∧ x ∈ paths i)).card +
      (Finset.univ.filter (fun i => label i = p ∧ y ∈ paths i)).card ≤ 2 := by
  have hx := label_vertex_card_le_one paths label hd p x
  have hy := label_vertex_card_le_one paths label hd p y
  omega

/-- A concrete charging interface. Events of one label at the two endpoints
of one edge are at most two, provided each indexed vertex occurrence is
charged at most once. Suffix-deletion events satisfy the membership premise
by `mem_of_mem_quarterSuffix`; the original suffix must stay frozen. -/
theorem endpoint_charge_card_le_two {E : Type*} (events : Finset E)
    (paths : I → List V) (label : I → P) (hd : LabelDisjoint paths label)
    (witness : E → I) (endpoint : E → V) (p : P) (x y : V)
    (hlabel : ∀ e ∈ events, label (witness e) = p)
    (hedge : ∀ e ∈ events, endpoint e = x ∨ endpoint e = y)
    (hmem : ∀ e ∈ events, endpoint e ∈ paths (witness e))
    (honce : Set.InjOn (fun e => (witness e, endpoint e)) (events : Set E)) :
    events.card ≤ 2 := by
  have hinj : Set.InjOn endpoint (events : Set E) := by
    intro e he f hf hef
    apply honce he hf
    apply Prod.ext
    · apply labels_injective_on_vertex paths label hd (endpoint e)
      · exact hmem e he
      · rw [hef]
        exact hmem f hf
      · exact (hlabel e he).trans (hlabel f hf).symm
    · exact hef
  have hcard : events.card ≤ ({x, y} : Finset V).card :=
    Finset.card_le_card_of_injOn endpoint
      (fun e he => by simpa using hedge e he) hinj
  exact hcard.trans Finset.card_le_two

end

end DirectedFlowCutGap.PathSystemCounting
