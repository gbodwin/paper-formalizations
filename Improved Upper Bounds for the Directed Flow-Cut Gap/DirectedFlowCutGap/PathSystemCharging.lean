import DirectedFlowCutGap.PathSystemCounting
import DirectedFlowCutGap.MedianShortcuts
import DirectedFlowCutGap.LevelCutProbability
import DirectedFlowCutGap.WitnessSystem

/-!
# Finite charging for actual indexed path occurrences

The charge set below is constructed, rather than assumed: it contains every
original suffix/base occurrence which has an eligible incident shortcut.
Each occurrence is charged once, to a chosen eligible edge. Eligibility is
independent of other deletions, so this is exactly a terminating execution
of the source's deletion procedure. The original prefixes and suffixes stay
frozen. Values are positive parts of differences of clipped heights.
-/

namespace DirectedFlowCutGap.PathSystemCharging

noncomputable section
open scoped BigOperators Classical NNReal ENNReal
open PathSystemCounting MedianShortcuts

variable {I V P : Type*}

/-- The exact real directed separation value for already clipped heights. -/
def value (h : P → V → ℝ) (p : P) (u v : V) : ℝ := max 0 (h p v - h p u)

@[simp] theorem value_self (h : P → V → ℝ) (p : P) (u : V) :
    value h p u u = 0 := by simp [value]

theorem value_nonneg (h : P → V → ℝ) (p : P) (u v : V) :
    0 ≤ value h p u v := le_max_left _ _

theorem difference_le_value (h : P → V → ℝ) (p : P) (u v : V) :
    h p v - h p u ≤ value h p u v := le_max_right _ _

/-- No monotonicity of the intermediate height is assumed. -/
theorem value_triangle (h : P → V → ℝ) (p : P) (u v x : V) :
    value h p u x ≤ value h p u v + value h p v x := by
  apply max_le
  · exact add_nonneg (value_nonneg ..) (value_nonneg ..)
  · have := difference_le_value h p u v
    have := difference_le_value h p v x
    linarith

/-- Clipping is performed before converting the extended distance to a real,
so an infinite distance has clipped height one, never zero. -/
def clippedHeight (d : P → V → ℝ≥0∞) (p : P) (v : V) : ℝ :=
  (min 1 (d p v)).toReal

theorem clippedHeight_nonneg (d : P → V → ℝ≥0∞) (p : P) (v : V) :
    0 ≤ clippedHeight d p v := ENNReal.toReal_nonneg

theorem clippedHeight_le_one (d : P → V → ℝ≥0∞) (p : P) (v : V) :
    clippedHeight d p v ≤ 1 := by
  simpa [clippedHeight] using
    ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) (min_le_left 1 (d p v))

/-- Exact bridge to the bounded extended subtraction used by level cuts. -/
theorem value_clippedHeight (d : P → V → ℝ≥0∞) (p : P) (u v : V) :
    value (clippedHeight d) p u v = (min 1 (d p v) - min 1 (d p u)).toReal := by
  have hfin (x : V) : min 1 (d p x) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (min_le_left _ _)
  by_cases huv : min 1 (d p u) ≤ min 1 (d p v)
  · rw [ENNReal.toReal_sub_of_le huv (hfin v)]
    exact max_eq_right (sub_nonneg.mpr (ENNReal.toReal_mono (hfin v) huv))
  · have hvu := le_of_not_ge huv
    rw [tsub_eq_zero_of_le hvu, ENNReal.toReal_zero]
    exact max_eq_left (sub_nonpos.mpr (ENNReal.toReal_mono (hfin u) hvu))

section GraphValue
variable [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- This connects charging's exact real value to the existing separation
probability, including vertices unreachable from the demand source. -/
theorem value_eq_levelSeparationValue_toReal (G : Digraph V)
    (w : P → V → ℝ≥0) (source : P → V) (p : P) (u v : V) :
    value (clippedHeight (fun q x => vertexDistance G (w q) (source q) x)) p u v =
      (levelSeparationValue G (w p) (source p) u v).toReal :=
  value_clippedHeight _ _ _ _
end GraphValue

/-- Values summed over demand labels, without counting witness indices as labels. -/
def totalValue [Fintype P] (h : P → V → ℝ) (u v : V) : ℝ := ∑ p, value h p u v

section Charges
variable [Fintype I] [Fintype V]

/-- Original, frozen suffix/base occurrences. Different witness indices remain distinct. -/
def occurrences (paths : I → List V) (base : List V) : Finset (I × V) :=
  Finset.univ.filter fun a => a.2 ∈ quarterSuffix (paths a.1) ∧ a.2 ∈ base

/-- An actual shortcut can be charged at either of its endpoints. -/
def Eligible (S : Finset (V × V)) (h : P → V → ℝ) (label : I → P)
    (τ : ℝ) (a : I × V) (e : V × V) : Prop :=
  e ∈ S ∧ (a.2 = e.1 ∨ a.2 = e.2) ∧ τ ≤ value h (label a.1) e.1 e.2

/-- All eligible occurrences are deleted once. This finite set gives an
actual maximal execution because deleting one occurrence changes no other
occurrence's eligibility. -/
def charged (paths : I → List V) (base : List V) (S : Finset (V × V))
    (h : P → V → ℝ) (label : I → P) (τ : ℝ) : Finset (I × V) :=
  (occurrences paths base).filter fun a => ∃ e, Eligible S h label τ a e

/-- The chosen edge is relevant only on `charged`; the fallback is harmless. -/
def assignedEdge (S : Finset (V × V)) (h : P → V → ℝ) (label : I → P)
    (τ : ℝ) (a : I × V) : V × V :=
  if he : ∃ e, Eligible S h label τ a e then Classical.choose he else (a.2, a.2)

def surviving (paths : I → List V) (base : List V) (S : Finset (V × V))
    (h : P → V → ℝ) (label : I → P) (τ : ℝ) : Finset (I × V) :=
  occurrences paths base \ charged paths base S h label τ

@[simp] theorem mem_charged {paths : I → List V} {base : List V}
    {S : Finset (V × V)} {h : P → V → ℝ} {label : I → P} {τ : ℝ} {a : I × V} :
    a ∈ charged paths base S h label τ ↔
      a ∈ occurrences paths base ∧ ∃ e, Eligible S h label τ a e := by
  simp [charged]

theorem assignedEdge_eligible {paths : I → List V} {base : List V}
    {S : Finset (V × V)} {h : P → V → ℝ} {label : I → P} {τ : ℝ} {a : I × V}
    (ha : a ∈ charged paths base S h label τ) :
    Eligible S h label τ a (assignedEdge S h label τ a) := by
  have he := (mem_charged.mp ha).2
  simpa [assignedEdge, he] using Classical.choose_spec he

/-- The survivor has no eligible incident edge, so the process really halts. -/
theorem surviving_halted {paths : I → List V} {base : List V}
    {S : Finset (V × V)} {h : P → V → ℝ} {label : I → P} {τ : ℝ} {a : I × V}
    (ha : a ∈ surviving paths base S h label τ) {e : V × V}
    (he : e ∈ S) (hend : a.2 = e.1 ∨ a.2 = e.2) :
    value h (label a.1) e.1 e.2 < τ := by
  obtain ⟨ho, hc⟩ := Finset.mem_sdiff.mp ha
  by_contra hn
  exact hc (mem_charged.mpr ⟨ho, e, he, hend, le_of_not_gt hn⟩)

/-- Exactly one original occurrence is removed per charging event. -/
theorem charge_survivor_card (paths : I → List V) (base : List V)
    (S : Finset (V × V)) (h : P → V → ℝ) (label : I → P) (τ : ℝ) :
    (charged paths base S h label τ).card +
      (surviving paths base S h label τ).card = (occurrences paths base).card := by
  have hsub : charged paths base S h label τ ⊆ occurrences paths base :=
    Finset.filter_subset _ _
  rw [surviving, Finset.card_sdiff_of_subset hsub]
  exact Nat.add_sub_of_le (Finset.card_le_card hsub)

/-- The actual charge multiset for one shortcut, retaining distinct occurrences. -/
def edgeEvents (paths : I → List V) (base : List V) (S : Finset (V × V))
    (h : P → V → ℝ) (label : I → P) (τ : ℝ) (e : V × V) : Finset (I × V) :=
  (charged paths base S h label τ).filter fun a => assignedEdge S h label τ a = e

def edgeCharge (paths : I → List V) (base : List V) (S : Finset (V × V))
    (h : P → V → ℝ) (label : I → P) (τ : ℝ) (e : V × V) : ℝ :=
  ∑ a ∈ edgeEvents paths base S h label τ e, value h (label a.1) e.1 e.2

/-- The two-endpoint multiplicity bound applies to the constructed charge set. -/
theorem edgeEvents_label_card_le_two (paths : I → List V) (base : List V)
    (S : Finset (V × V)) (h : P → V → ℝ) (label : I → P) (τ : ℝ)
    (hd : LabelDisjoint paths label) (e : V × V) (p : P) :
    ((edgeEvents paths base S h label τ e).filter fun a => label a.1 = p).card ≤ 2 := by
  let A := (edgeEvents paths base S h label τ e).filter fun a => label a.1 = p
  apply endpoint_charge_card_le_two A paths label hd Prod.fst Prod.snd p e.1 e.2
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a ha
    have hae := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1)
    have hel := assignedEdge_eligible hae.1
    rw [hae.2] at hel
    exact hel.2.1
  · intro a ha
    have hac := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
    exact mem_of_mem_quarterSuffix
      ((Finset.mem_filter.mp (mem_charged.mp hac).1).2.1)
  · intro a _ b _ hab
    exact Prod.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)

variable [Fintype P]

/-- Lemma 21 with exact finite constants and the actual charge assignment. -/
theorem edgeCharge_le_two_totalValue (paths : I → List V) (base : List V)
    (S : Finset (V × V)) (h : P → V → ℝ) (label : I → P) (τ : ℝ)
    (hd : LabelDisjoint paths label) (e : V × V) :
    edgeCharge paths base S h label τ e ≤ 2 * totalValue h e.1 e.2 := by
  classical
  let A := edgeEvents paths base S h label τ e
  have hsum : (∑ p : P, ∑ a ∈ A.filter (fun a => label a.1 = p),
      value h (label a.1) e.1 e.2) = ∑ a ∈ A, value h (label a.1) e.1 e.2 := by
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  unfold edgeCharge
  rw [← hsum]
  unfold totalValue
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  have heq : (∑ a ∈ A.filter (fun a => label a.1 = p), value h (label a.1) e.1 e.2) =
      (((A.filter fun a => label a.1 = p).card : ℕ) : ℝ) * value h p e.1 e.2 := by
    calc
      _ = ∑ _a ∈ A.filter (fun a => label a.1 = p), value h p e.1 e.2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [(Finset.mem_filter.mp ha).2]
      _ = _ := by simp
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (value_nonneg ..)
  exact_mod_cast edgeEvents_label_card_le_two paths base S h label τ hd e p

omit [Fintype P] in
/-- Total charged value counts each deleted occurrence exactly once. -/
theorem sum_edgeCharge (paths : I → List V) (base : List V) (S : Finset (V × V))
    (h : P → V → ℝ) (label : I → P) (τ : ℝ) :
    (∑ e ∈ S, edgeCharge paths base S h label τ e) =
      ∑ a ∈ charged paths base S h label τ,
        value h (label a.1) (assignedEdge S h label τ a).1 (assignedEdge S h label τ a).2 := by
  unfold edgeCharge edgeEvents
  have hm : ∀ a ∈ charged paths base S h label τ, assignedEdge S h label τ a ∈ S :=
    fun a ha => (assignedEdge_eligible ha).1
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

omit [Fintype P] in
/-- Every event pays the threshold, including zero or negative thresholds. -/
theorem charge_threshold_le_sum (paths : I → List V) (base : List V)
    (S : Finset (V × V)) (h : P → V → ℝ) (label : I → P) (τ : ℝ) :
    (charged paths base S h label τ).card * τ ≤
      ∑ e ∈ S, edgeCharge paths base S h label τ e := by
  rw [sum_edgeCharge]
  calc
    _ = ∑ _a ∈ charged paths base S h label τ, τ := by simp
    _ ≤ _ := Finset.sum_le_sum (fun a ha => (assignedEdge_eligible ha).2.2)

/-- An actual edge witnesses the long-charge average. Positive event mass
also proves that the shortcut set is nonempty before any division is used. -/
theorem exists_long_charge_edge (paths : I → List V) (base : List V)
    (S : Finset (V × V)) (h : P → V → ℝ) (label : I → P) (τ : ℝ)
    (hd : LabelDisjoint paths label)
    (hpositive : 0 < (charged paths base S h label τ).card * τ) :
    ∃ e ∈ S, (charged paths base S h label τ).card * τ ≤
      2 * S.card * totalValue h e.1 e.2 := by
  have hsum := charge_threshold_le_sum paths base S h label τ
  have hne : S.Nonempty := by
    by_contra hn
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty] at hsum
    rw [he] at hpositive
    linarith
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image S
    (fun e => totalValue h e.1 e.2) hne
  refine ⟨e, he, hsum.trans ?_⟩
  calc
    _ ≤ ∑ f ∈ S, 2 * totalValue h e.1 e.2 := by
      apply Finset.sum_le_sum
      intro f hf
      exact (edgeCharge_le_two_totalValue paths base S h label τ hd f).trans
        (mul_le_mul_of_nonneg_left (hmax f hf) (by norm_num))
    _ = _ := by simp; ring

end Charges

/-- A halted pair connected by at most two shortcuts has small value. The
surviving first or last endpoint makes the appropriate edge ineligible. -/
theorem halted_twoHop_value_lt (h : P → V → ℝ) (p : P) (S : Finset (V × V))
    (M : Finset V) {x y : V} {τ : ℝ} (hτ : 0 < τ) (hxy : TwoHop S M x y)
    (hx : ∀ e ∈ S, e.1 = x ∨ e.2 = x → value h p e.1 e.2 < τ)
    (hy : ∀ e ∈ S, e.1 = y ∨ e.2 = y → value h p e.1 e.2 < τ) :
    value h p x y < 2 * τ := by
  rcases hxy with rfl | he | ⟨m, _hm, hxm, hmy⟩
  · simp only [value_self]; linarith
  · have := hx (x, y) he (Or.inl rfl)
    linarith
  · have h₁ := hx (x, m) hxm (Or.inl rfl)
    have h₂ := hy (m, y) hmy (Or.inr rfl)
    have := value_triangle h p x m y
    linarith

/-- The three canonical-sequence cases, with their actual shortcut and
uniform mediator data, all supply one of at most `M.card + 1` candidate pairs. -/
theorem canonical_value_alternative (h : P → V → ℝ) (p : P)
    (S : Finset (V × V)) (M : Finset V) (u first target : V) {a τ : ℝ}
    (ha : 0 ≤ a) (hgap : 2 * a + τ ≤ value h p u target)
    (hτ : 0 ≤ τ) (hpath : TwoHop S M first target)
    (hhalt : ∀ e ∈ S, e.1 = target ∨ e.2 = target → value h p e.1 e.2 < τ) :
    a ≤ value h p u first ∨
      ∃ m ∈ M, (first, m) ∈ S ∧ a ≤ value h p first m := by
  rcases hpath with rfl | he | ⟨m, hm, hfm, hmt⟩
  · exact Or.inl (by linarith)
  · have hlast := hhalt (first, target) he (Or.inr rfl)
    have htri := value_triangle h p u first target
    exact Or.inl (by linarith)
  · have hlast := hhalt (m, target) hmt (Or.inr rfl)
    have ht₁ := value_triangle h p u first target
    have ht₂ := value_triangle h p first m target
    by_cases hfirst : a ≤ value h p u first
    · exact Or.inl hfirst
    · exact Or.inr ⟨m, hm, hfm, by linarith⟩


/-- Consecutive positive height gaps telescope over the actual list indices.
The proof uses every intermediate entry, not a single pairwise gap. -/
theorem spaced_index_gap (l : List V) (h : V → ℝ) (δ : ℝ)
    (hs : l.Pairwise (fun x y => h x + δ ≤ h y))
    (i j : ℕ) (hj : j < l.length) (hij : i ≤ j) :
    ((j - i : ℕ) : ℝ) * δ ≤ h l[j] - h (l[i]'(lt_of_le_of_lt hij hj)) := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      simp
  | succ j ih =>
      by_cases heq : i = j + 1
      · subst i
        simp
      have hij' : i ≤ j := by omega
      have hj' : j < l.length := by omega
      have hp := ih hj' hij'
      have hstep := List.pairwise_iff_getElem.mp hs j (j + 1) hj' hj (by omega)
      have hdiff : j + 1 - i = (j - i) + 1 := by omega
      rw [hdiff, Nat.cast_add, Nat.cast_one]
      nlinarith

/-- A finite sum over distinct demand labels is bounded by the true total
value. Counting path indices here without label injectivity would be invalid. -/
theorem sum_value_le_totalValue [Fintype P] (Q : Finset I) (label : I → P)
    (hinj : Set.InjOn label (Q : Set I)) (h : P → V → ℝ) (x y : V) :
    (∑ i ∈ Q, value h (label i) x y) ≤ totalValue h x y := by
  classical
  calc
    _ = ∑ p ∈ Q.image label, value h p x y := (Finset.sum_image hinj).symm
    _ ≤ ∑ p, value h p x y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => value_nonneg ..)

/-- Finite weighted pigeonhole principle with every contributing demand
label proved distinct. The edge is selected from the actual candidate set. -/
theorem exists_large_candidate [Fintype P] (Q : Finset I) (E : Finset (V × V))
    (hne : E.Nonempty) (label : I → P) (hinj : Set.InjOn label (Q : Set I))
    (h : P → V → ℝ) (a : ℝ)
    (hw : ∀ i ∈ Q, ∃ e ∈ E, a ≤ value h (label i) e.1 e.2) :
    ∃ e ∈ E, Q.card * a ≤ E.card * totalValue h e.1 e.2 := by
  classical
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image E (fun e => totalValue h e.1 e.2) hne
  refine ⟨e, he, ?_⟩
  calc
    _ = ∑ _i ∈ Q, a := by simp
    _ ≤ ∑ i ∈ Q, ∑ f ∈ E, value h (label i) f.1 f.2 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨f, hf, hif⟩ := hw i hi
      exact hif.trans (Finset.single_le_sum (fun _ _ => value_nonneg ..) hf)
    _ = ∑ f ∈ E, ∑ i ∈ Q, value h (label i) f.1 f.2 := Finset.sum_comm
    _ ≤ ∑ f ∈ E, totalValue h f.1 f.2 := by
      apply Finset.sum_le_sum
      intro f _
      exact sum_value_le_totalValue Q label hinj h f.1 f.2
    _ ≤ ∑ _f ∈ E, totalValue h e.1 e.2 := Finset.sum_le_sum (fun f hf => hmax f hf)
    _ = _ := by simp

/-- Actual canonical candidate edges: the common first pair, and reachable
shortcut edges through the uniform mediator set. -/
def canonicalEdges (S : Finset (V × V)) (M : Finset V) (u first : V) : Finset (V × V) :=
  insert (u, first) ((M.filter fun m => (first, m) ∈ S).image fun m => (first, m))

theorem canonicalEdges_card (S : Finset (V × V)) (M : Finset V) (u first : V) :
    (canonicalEdges S M u first).card ≤ M.card + 1 := by
  classical
  exact (Finset.card_insert_le _ _).trans (by
    have h₁ := Finset.card_image_le (s := M.filter fun m => (first, m) ∈ S)
      (f := fun m => (first, m))
    have h₂ := Finset.card_filter_le M (fun m => (first, m) ∈ S)
    omega)

/-- Lemma 24's canonical-sequence conversion, with all reachable edges and
label contributions verified. No desired charged pair is a premise. -/
theorem exists_canonical_value [Fintype P] (Q : Finset I)
    (paths : I → List V) (label : I → P) (hd : LabelDisjoint paths label)
    (h : P → V → ℝ) (R : V → V → Prop) (S : Finset (V × V)) (M : Finset V)
    (u first : V) (target : I → V) {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    (hu : ∀ i ∈ Q, u ∈ paths i) (hfirst : R u first)
    (hS : ∀ x y, (x, y) ∈ S → R x y)
    (hgap : ∀ i ∈ Q, 2 * a + τ ≤ value h (label i) u (target i))
    (hpath : ∀ i ∈ Q, TwoHop S M first (target i))
    (hhalt : ∀ i ∈ Q, ∀ e ∈ S, e.1 = target i ∨ e.2 = target i →
      value h (label i) e.1 e.2 < τ) :
    ∃ x y, R x y ∧ Q.card * a ≤ (M.card + 1) * totalValue h x y := by
  classical
  let E := canonicalEdges S M u first
  have hinj : Set.InjOn label (Q : Set I) := by
    intro i hi j hj heq
    exact labels_injective_on_vertex paths label hd u (hu i hi) (hu j hj) heq
  have hne : E.Nonempty := ⟨(u, first), Finset.mem_insert_self _ _⟩
  have hw : ∀ i ∈ Q, ∃ e ∈ E, a ≤ value h (label i) e.1 e.2 := by
    intro i hi
    obtain hval | ⟨m, hm, hem, hval⟩ := canonical_value_alternative h (label i)
      S M u first (target i) ha (hgap i hi) hτ (hpath i hi) (hhalt i hi)
    · exact ⟨(u, first), Finset.mem_insert_self _ _, hval⟩
    · refine ⟨(first, m), Finset.mem_insert_of_mem ?_, hval⟩
      exact Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, hem⟩, rfl⟩
  obtain ⟨e, he, hlarge⟩ := exists_large_candidate Q E hne label hinj h a hw
  refine ⟨e.1, e.2, ?_, hlarge.trans ?_⟩
  · rcases Finset.mem_insert.mp he with he | he
    · cases he
      exact hfirst
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp he
      exact hS _ _ (Finset.mem_filter.mp hm).2
  · apply mul_le_mul_of_nonneg_right _
      (Finset.sum_nonneg (fun _ _ => value_nonneg ..))
    exact_mod_cast canonicalEdges_card S M u first


/-- Correct real-parameter rounding: a halted list has at most `2 * σ`
vertices. This does not use the false implication `c > σ → c - 1 ≥ σ`. -/
theorem halted_list_card_le_two_sigma (l : List V) (h : P → V → ℝ) (p : P)
    (R : V → V → Prop) (S : Finset (V × V)) (M : V → Finset V)
    {L σ τ : ℝ} (hL : 0 < L) (hσ : 1 ≤ σ) (hτ : 0 < τ)
    (hsmall : 2 * τ ≤ σ / L)
    (hs : l.Pairwise (fun x y => h p x + 1 / L ≤ h p y))
    (hf : l.Pairwise R)
    (htwo : ∀ x ∈ l, ∀ y ∈ l, R x y → TwoHop S (M x) x y)
    (hhalt : ∀ x ∈ l, ∀ e ∈ S, e.1 = x ∨ e.2 = x → value h p e.1 e.2 < τ) :
    (l.length : ℝ) ≤ 2 * σ := by
  by_cases hshort : l.length ≤ 1
  · have hshort' : (l.length : ℝ) ≤ 1 := by exact_mod_cast hshort
    linarith
  have hlen : 2 ≤ l.length := by omega
  have hzero : 0 < l.length := by omega
  have hlast : l.length - 1 < l.length := by omega
  let x := l[0]'hzero
  let y := l[l.length - 1]'hlast
  have hx : x ∈ l := List.getElem_mem hzero
  have hy : y ∈ l := List.getElem_mem hlast
  have hxy : R x y := List.pairwise_iff_getElem.mp hf 0 (l.length - 1)
    hzero hlast (by omega)
  have hval := halted_twoHop_value_lt h p S (M x) hτ (htwo x hx y hy hxy)
    (hhalt x hx) (hhalt y hy)
  have hgap := spaced_index_gap l (h p) (1 / L) hs 0 (l.length - 1) hlast (by omega)
  have hdiff := difference_le_value h p x y
  have hspan : ((l.length - 1 : ℕ) : ℝ) / L < σ / L := by
    dsimp [x, y] at hdiff hval
    simp only [Nat.sub_zero, mul_one_div] at hgap
    linarith
  have hcount : ((l.length - 1 : ℕ) : ℝ) < σ :=
    (div_lt_div_iff_of_pos_right hL).mp hspan
  rw [Nat.cast_sub (by omega : 1 ≤ l.length), Nat.cast_one] at hcount
  linarith

section SurvivingLists
variable [Fintype I] [Fintype V]

/-- Surviving suffixes keep the original order and are never recomputed. -/
def survivingList (paths : I → List V) (base : List V) (S : Finset (V × V))
    (h : P → V → ℝ) (label : I → P) (τ : ℝ) (i : I) : List V :=
  (quarterSuffix (paths i)).filter fun v => (i, v) ∈ surviving paths base S h label τ

@[simp] theorem mem_survivingList (paths : I → List V) (base : List V)
    (S : Finset (V × V)) (h : P → V → ℝ) (label : I → P) (τ : ℝ) (i : I) (v : V) :
    v ∈ survivingList paths base S h label τ i ↔
      (i, v) ∈ surviving paths base S h label τ := by
  simp only [survivingList, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hv
    refine ⟨?_, hv⟩
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2.1

theorem survivingList_sublist (paths : I → List V) (base : List V)
    (S : Finset (V × V)) (h : P → V → ℝ) (label : I → P) (τ : ℝ) (i : I) :
    (survivingList paths base S h label τ i).Sublist (paths i) :=
  (List.filter_sublist).trans (quarterSuffix_sublist _)

/-- The count bound is instantiated on the constructed, halted survivors,
using only genuine list spacing, ordered reachability, and the shortcut API. -/
theorem survivingList_length_le_two_sigma (paths : I → List V) (base : List V)
    (S : Finset (V × V)) (M : V → Finset V) (h : P → V → ℝ) (label : I → P)
    (R : V → V → Prop) {L σ τ : ℝ} (hL : 0 < L) (hσ : 1 ≤ σ) (hτ : 0 < τ)
    (hsmall : 2 * τ ≤ σ / L)
    (hs : ∀ i, (paths i).Pairwise (fun x y => h (label i) x + 1 / L ≤ h (label i) y))
    (hf : ∀ i, (paths i).Pairwise R)
    (htwo : ∀ x ∈ base, ∀ y ∈ base, R x y → TwoHop S (M x) x y) (i : I) :
    ((survivingList paths base S h label τ i).length : ℝ) ≤ 2 * σ := by
  have hsub := survivingList_sublist paths base S h label τ i
  apply halted_list_card_le_two_sigma _ h (label i) R S M hL hσ hτ hsmall
    ((hs i).sublist hsub) ((hf i).sublist hsub)
  · intro x hx y hy hxy
    have hx' := (mem_survivingList paths base S h label τ i x).mp hx
    have hy' := (mem_survivingList paths base S h label τ i y).mp hy
    exact htwo x ((Finset.mem_filter.mp (Finset.mem_sdiff.mp hx').1).2.2)
      y ((Finset.mem_filter.mp (Finset.mem_sdiff.mp hy').1).2.2) hxy
  · intro x hx e he hend
    apply surviving_halted ((mem_survivingList paths base S h label τ i x).mp hx) he
    exact hend.imp Eq.symm Eq.symm

end SurvivingLists


/-- Prefix/suffix membership yields an actual index gap of half the list
length, including the rounding of both frozen quarters. -/
theorem prefix_suffix_gap (l : List V) (h : P → V → ℝ) (p : P)
    (R : V → V → Prop) {L : ℝ} (hL : 0 < L)
    (hs : l.Pairwise (fun x y => h p x + 1 / L ≤ h p y)) (hf : l.Pairwise R)
    {u v : V} (hu : u ∈ quarterPrefix l) (hv : v ∈ quarterSuffix l) :
    R u v ∧ (l.length : ℝ) / (2 * L) ≤ value h p u v := by
  obtain ⟨i, hi, hiu⟩ := List.mem_take_iff_getElem.mp hu
  obtain ⟨j, hj, hjv⟩ := List.mem_drop_iff_getElem.mp hv
  have hi' : i < l.length / 4 := lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have hil : i < l.length := lt_of_lt_of_le hi (Nat.min_le_right _ _)
  have hjl : l.length - l.length / 4 + j < l.length := by omega
  have hij : i < l.length - l.length / 4 + j := by omega
  have hreach := List.pairwise_iff_getElem.mp hf i (l.length - l.length / 4 + j)
    hil hjl hij
  have hgap := spaced_index_gap l (h p) (1 / L) hs i
    (l.length - l.length / 4 + j) hjl hij.le
  rw [hiu, hjv] at hreach hgap
  refine ⟨hreach, ?_⟩
  have hsep := prefix_suffix_index_separation hi' (show l.length - l.length / 4 ≤
    l.length - l.length / 4 + j by omega)
  have hsep' : (l.length : ℝ) ≤ 2 * ((l.length - l.length / 4 + j - i : ℕ) : ℝ) :=
    by exact_mod_cast hsep
  calc
    (l.length : ℝ) / (2 * L) ≤ ((l.length - l.length / 4 + j - i : ℕ) : ℝ) / L := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * L) hL).mpr
      nlinarith
    _ ≤ h p v - h p u := by simpa only [mul_one_div] using hgap
    _ ≤ value h p u v := difference_le_value ..

section SurvivorCounting
variable [Fintype I] [Fintype V]

/-- Exact cardinality of one witness fiber, with list order discarded only
for counting and only after nodup has been proved. -/
theorem survivor_fiber_card (paths : I → List V) (base : List V) (S : Finset (V × V))
    (h : P → V → ℝ) (label : I → P) (τ : ℝ) (hn : ∀ i, (paths i).Nodup) (i : I) :
    ((surviving paths base S h label τ).filter fun a => a.1 = i).card =
      (survivingList paths base S h label τ i).length := by
  classical
  rw [← List.toFinset_card_of_nodup ((hn i).sublist (survivingList_sublist ..))]
  apply Finset.card_bij (fun a _ => a.2)
  · intro a ha
    obtain ⟨ha, hi⟩ := Finset.mem_filter.mp ha
    simp only [List.mem_toFinset, mem_survivingList]
    simpa only [← hi] using ha
  · intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
  · intro v hv
    refine ⟨(i, v), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨(mem_survivingList paths base S h label τ i v).mp
      (List.mem_toFinset.mp hv), rfl⟩

/-- The total surviving incidence is exactly the sum of actual list lengths. -/
theorem survivor_card_eq_sum (paths : I → List V) (base : List V) (S : Finset (V × V))
    (h : P → V → ℝ) (label : I → P) (τ : ℝ) (hn : ∀ i, (paths i).Nodup) :
    (surviving paths base S h label τ).card =
      ∑ i, (survivingList paths base S h label τ i).length := by
  classical
  have hf := Finset.card_eq_sum_card_fiberwise
    (s := surviving paths base S h label τ) (t := (Finset.univ : Finset I))
    (f := Prod.fst) (fun _ _ => Finset.mem_univ _)
  rw [hf]
  apply Finset.sum_congr rfl
  intro i _
  exact survivor_fiber_card paths base S h label τ hn i

/-- Witnesses retaining at least one original suffix/base occurrence. -/
def active (paths : I → List V) (base : List V) (S : Finset (V × V))
    (h : P → V → ℝ) (label : I → P) (τ : ℝ) : Finset I :=
  Finset.univ.filter fun i => survivingList paths base S h label τ i ≠ []

/-- The short-charge surviving incidence forces many active witnesses. -/
theorem survivor_card_le_active (paths : I → List V) (base : List V) (S : Finset (V × V))
    (h : P → V → ℝ) (label : I → P) (τ σ : ℝ) (hn : ∀ i, (paths i).Nodup)
    (hbound : ∀ i, ((survivingList paths base S h label τ i).length : ℝ) ≤ 2 * σ) :
    ((surviving paths base S h label τ).card : ℝ) ≤
      (active paths base S h label τ).card * (2 * σ) := by
  classical
  rw [survivor_card_eq_sum paths base S h label τ hn, Nat.cast_sum]
  have heq : (∑ i, ((survivingList paths base S h label τ i).length : ℝ)) =
      ∑ i ∈ active paths base S h label τ,
        ((survivingList paths base S h label τ i).length : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hz : survivingList paths base S h label τ i = [] := by
      simpa [active] using hi
    simp [hz]
  rw [heq]
  calc
    _ ≤ ∑ _i ∈ active paths base S h label τ, 2 * σ :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = _ := by simp

omit [Fintype I] in
/-- Averaging the actual frozen prefixes produces a common prefix vertex.
This constructs the fan family used in the short-charge argument. -/
theorem exists_prefix_fan [Nonempty V] (paths : I → List V) (A : Finset I)
    (hn : ∀ i, (paths i).Nodup) (ℓ : ℝ)
    (hmin : ∀ i ∈ A, ℓ ≤ ((quarterPrefix (paths i)).length : ℝ)) :
    ∃ u : V, A.card * ℓ ≤ (Fintype.card V : ℝ) *
      ((A.filter fun i => u ∈ quarterPrefix (paths i)).card : ℝ) := by
  classical
  let f := fun u : V => (A.filter fun i => u ∈ quarterPrefix (paths i)).card
  obtain ⟨u, _, hu⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨u, ?_⟩
  have hcount : (∑ v : V, f v) = ∑ i ∈ A, (quarterPrefix (paths i)).length := by
    simp only [f, Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← List.toFinset_card_of_nodup (quarterPrefix_nodup (hn i))]
    have hset : (Finset.univ.filter fun v : V => v ∈ quarterPrefix (paths i)) =
        (quarterPrefix (paths i)).toFinset := by ext v; simp
    simp only [Finset.sum_boole, Nat.cast_id, hset]
  have hcount' : (∑ v : V, (f v : ℝ)) =
      ∑ i ∈ A, ((quarterPrefix (paths i)).length : ℝ) := by exact_mod_cast hcount
  calc
    _ = ∑ _i ∈ A, ℓ := by simp
    _ ≤ ∑ i ∈ A, ((quarterPrefix (paths i)).length : ℝ) := Finset.sum_le_sum hmin
    _ = ∑ v : V, (f v : ℝ) := hcount'.symm
    _ ≤ ∑ _v : V, (f u : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      exact_mod_cast hu v (Finset.mem_univ v)
    _ = _ := by simp [f]

end SurvivorCounting


/-- Choosing an earliest target in the actual base order gives zero- or
forward-shortcut paths uniformly from that target to every other target. -/
theorem exists_first_target (Q : Finset I) (hne : Q.Nonempty) (target : I → V)
    (base : List V) (R : V → V → Prop) (S : Finset (V × V)) (M : V → Finset V)
    (hb : base.Pairwise R) (hmem : ∀ i ∈ Q, target i ∈ base)
    (htwo : ∀ x ∈ base, ∀ y ∈ base, R x y → TwoHop S (M x) x y) :
    ∃ i ∈ Q, ∀ j ∈ Q, TwoHop S (M (target i)) (target i) (target j) := by
  classical
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Q (fun i => base.idxOf (target i)) hne
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_cases heq : target i = target j
  · exact Or.inl heq
  have hlt : base.idxOf (target i) < base.idxOf (target j) := by
    have hle := hmin j hj
    have hne' : base.idxOf (target i) ≠ base.idxOf (target j) :=
      fun hh => heq ((List.idxOf_inj (hmem i hi)).mp hh)
    omega
  have hix := List.idxOf_lt_length_of_mem (hmem i hi)
  have hjx := List.idxOf_lt_length_of_mem (hmem j hj)
  have hR := List.pairwise_iff_getElem.mp hb _ _ hix hjx hlt
  rw [List.getElem_idxOf, List.getElem_idxOf] at hR
  exact htwo _ (hmem i hi) _ (hmem j hj) hR

section ConstructedShortCase
variable [Fintype I] [Fintype V] [Fintype P] [Nonempty V]

/-- Complete structural short-charge construction. The common prefix fan,
its distinct labels, its suffix targets, and its earliest base target are
all derived from the actual halted occurrence set. The bound is deliberately
denominator-free; `ℓ` is a proved lower bound on actual prefix lengths. -/
theorem exists_short_charge_edge (paths : I → List V) (base : List V)
    (S : Finset (V × V)) (M : V → Finset V) (h : P → V → ℝ) (label : I → P)
    (R : V → V → Prop) {L σ τ ℓ a : ℝ} {H : ℕ}
    (hL : 0 < L) (hσ : 1 ≤ σ) (hτ : 0 < τ) (hℓ : 0 < ℓ) (ha : 0 ≤ a)
    (hsmall : 2 * τ ≤ σ / L)
    (hn : ∀ i, (paths i).Nodup) (hd : LabelDisjoint paths label)
    (hs : ∀ i, (paths i).Pairwise (fun x y => h (label i) x + 1 / L ≤ h (label i) y))
    (hf : ∀ i, (paths i).Pairwise R) (hb : base.Pairwise R)
    (hS : ∀ x y, (x, y) ∈ S → R x y)
    (hM : ∀ x, (M x).card ≤ H)
    (htwo : ∀ x ∈ base, ∀ y ∈ base, R x y → TwoHop S (M x) x y)
    (hprefix : ∀ i, ℓ ≤ ((quarterPrefix (paths i)).length : ℝ))
    (hgap : ∀ i, 2 * a + τ ≤ (paths i).length / (2 * L))
    (hpositive : 0 < (surviving paths base S h label τ).card) :
    ∃ x y, R x y ∧
      (surviving paths base S h label τ).card * ℓ * a ≤
        2 * σ * Fintype.card V * (H + 1) * totalValue h x y := by
  classical
  let A := active paths base S h label τ
  have hbound := survivingList_length_le_two_sigma paths base S M h label R
    hL hσ hτ hsmall hs hf htwo
  have hactive := survivor_card_le_active paths base S h label τ σ hn hbound
  have hApos : 0 < A.card := by
    by_contra hz
    have he : A.card = 0 := by omega
    change ((surviving paths base S h label τ).card : ℝ) ≤ A.card * (2 * σ) at hactive
    rw [he, Nat.cast_zero, zero_mul] at hactive
    have hp : (0 : ℝ) < (surviving paths base S h label τ).card := by exact_mod_cast hpositive
    linarith
  obtain ⟨u, hfan⟩ := exists_prefix_fan paths A hn ℓ (fun i _ => hprefix i)
  let Q := A.filter fun i => u ∈ quarterPrefix (paths i)
  have hQpos : 0 < Q.card := by
    by_contra hz
    have he : Q.card = 0 := by omega
    change (A.card : ℝ) * ℓ ≤ (Fintype.card V : ℝ) * Q.card at hfan
    rw [he, Nat.cast_zero, mul_zero] at hfan
    have hp : (0 : ℝ) < A.card := by exact_mod_cast hApos
    have := mul_pos hp hℓ
    linarith
  have htarget : ∀ i : I, ∃ v : V, i ∈ Q → (i, v) ∈ surviving paths base S h label τ := by
    intro i
    by_cases hi : i ∈ Q
    · have hai : i ∈ A := (Finset.mem_filter.mp hi).1
      have hnlist : survivingList paths base S h label τ i ≠ [] := (Finset.mem_filter.mp hai).2
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hnlist
      exact ⟨v, fun _ => (mem_survivingList paths base S h label τ i v).mp hv⟩
    · exact ⟨u, fun hh => (hi hh).elim⟩
  choose target htarget using htarget
  have htargetBase : ∀ i ∈ Q, target i ∈ base := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (htarget i hi)).1).2.2
  obtain ⟨first, hfirst, hpaths⟩ := exists_first_target Q (Finset.card_pos.mp hQpos)
    target base R S M hb htargetBase htwo
  have hprefixQ : ∀ i ∈ Q, u ∈ quarterPrefix (paths i) :=
    fun i hi => (Finset.mem_filter.mp hi).2
  have hsuffixQ : ∀ i ∈ Q, target i ∈ quarterSuffix (paths i) := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (htarget i hi)).1).2.1
  have hpair : ∀ i ∈ Q, R u (target i) ∧
      (paths i).length / (2 * L) ≤ value h (label i) u (target i) :=
    fun i hi => prefix_suffix_gap (paths i) h (label i) R hL (hs i) (hf i)
      (hprefixQ i hi) (hsuffixQ i hi)
  have hhalt : ∀ i ∈ Q, ∀ e ∈ S, e.1 = target i ∨ e.2 = target i →
      value h (label i) e.1 e.2 < τ := by
    intro i hi e he hend
    exact surviving_halted (htarget i hi) he (hend.imp Eq.symm Eq.symm)
  obtain ⟨x, y, hR, hval⟩ := exists_canonical_value Q paths label hd h R S (M (target first))
    u (target first) target ha hτ.le
    (fun i hi => mem_of_mem_quarterPrefix (hprefixQ i hi)) (hpair first hfirst).1 hS
    (fun i hi => (hgap i).trans (hpair i hi).2) hpaths hhalt
  refine ⟨x, y, hR, ?_⟩
  have hval' : (Q.card : ℝ) * a ≤ (H + 1) * totalValue h x y := by
    refine hval.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun _ _ => value_nonneg ..)))
    exact_mod_cast Nat.add_le_add_right (hM (target first)) 1
  have hnV : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hσn : 0 ≤ 2 * σ := by linarith
  change (A.card : ℝ) * ℓ ≤ (Fintype.card V : ℝ) * Q.card at hfan
  change ((surviving paths base S h label τ).card : ℝ) ≤ A.card * (2 * σ) at hactive
  have h₁ := mul_le_mul_of_nonneg_right hactive (mul_nonneg hℓ.le ha)
  have h₂ := mul_le_mul_of_nonneg_right hfan (mul_nonneg hσn ha)
  have h₃ := mul_le_mul_of_nonneg_left hval' (mul_nonneg hσn hnV)
  nlinarith

end ConstructedShortCase


section ChargeDichotomy
variable [Fintype I] [Fintype V] [Fintype P] [Nonempty V]

omit [Nonempty V] in
/-- Exact double counting identifies the initial chargeable occurrence universe
with the base-path suffix-degree score, before any deletions. -/
theorem occurrences_card (paths : I → List V) (base : List V) :
    (occurrences paths base).card = ∑ v ∈ base.toFinset, suffixDegree paths v := by
  classical
  have hf := Finset.card_eq_sum_card_fiberwise
    (s := occurrences paths base) (t := base.toFinset) (f := Prod.snd)
    (fun a ha => List.mem_toFinset.mpr (Finset.mem_filter.mp ha).2.2)
  rw [hf]
  apply Finset.sum_congr rfl
  intro v hv
  rw [suffixDegree, degree_eq_card]
  apply Finset.card_bij (fun a _ => a.1)
  · intro a ha
    obtain ⟨ha, hav⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [← hav] using (Finset.mem_filter.mp ha).2.1
  · intro a ha b hb hab
    exact Prod.ext hab ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  · intro i hi
    refine ⟨(i, v), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hi).2, List.mem_toFinset.mp hv⟩, rfl⟩

/-- The actual terminating charge set gives the long/short alternative. Both
branches exhibit a genuinely reachable pair. Every structural input concerns
real lists or selected shortcuts, and the desired pair is never a premise. -/
theorem exists_charge_dichotomy (paths : I → List V) (base : List V)
    (S : Finset (V × V)) (M : V → Finset V) (h : P → V → ℝ) (label : I → P)
    (R : V → V → Prop) {L σ τ ℓ a : ℝ} {H : ℕ}
    (hL : 0 < L) (hσ : 1 ≤ σ) (hτ : 0 < τ) (hℓ : 0 < ℓ) (ha : 0 ≤ a)
    (hsmall : 2 * τ ≤ σ / L)
    (hn : ∀ i, (paths i).Nodup) (hd : LabelDisjoint paths label)
    (hs : ∀ i, (paths i).Pairwise (fun x y => h (label i) x + 1 / L ≤ h (label i) y))
    (hf : ∀ i, (paths i).Pairwise R) (hb : base.Pairwise R)
    (hS : ∀ x y, (x, y) ∈ S → R x y) (hM : ∀ x, (M x).card ≤ H)
    (htwo : ∀ x ∈ base, ∀ y ∈ base, R x y → TwoHop S (M x) x y)
    (hprefix : ∀ i, ℓ ≤ ((quarterPrefix (paths i)).length : ℝ))
    (hgap : ∀ i, 2 * a + τ ≤ (paths i).length / (2 * L))
    (hpositive : 0 < (occurrences paths base).card) :
    ∃ x y, R x y ∧
      (((occurrences paths base).card : ℝ) * τ ≤ 4 * S.card * totalValue h x y ∨
       ((occurrences paths base).card : ℝ) * ℓ * a ≤
         4 * σ * Fintype.card V * (H + 1) * totalValue h x y) := by
  have hpartition := charge_survivor_card paths base S h label τ
  by_cases hlong : (occurrences paths base).card ≤ 2 * (charged paths base S h label τ).card
  · have hcp : 0 < (charged paths base S h label τ).card := by omega
    have hcpp : (0 : ℝ) < (charged paths base S h label τ).card := by exact_mod_cast hcp
    obtain ⟨e, he, hval⟩ := exists_long_charge_edge paths base S h label τ hd (mul_pos hcpp hτ)
    refine ⟨e.1, e.2, hS _ _ he, Or.inl ?_⟩
    have hlong' : ((occurrences paths base).card : ℝ) ≤
        2 * ((charged paths base S h label τ).card : ℝ) := by exact_mod_cast hlong
    have := mul_le_mul_of_nonneg_right hlong' hτ.le
    nlinarith
  · have hsp : 0 < (surviving paths base S h label τ).card := by omega
    obtain ⟨x, y, hR, hval⟩ := exists_short_charge_edge paths base S M h label R
      hL hσ hτ hℓ ha hsmall hn hd hs hf hb hS hM htwo hprefix hgap hsp
    refine ⟨x, y, hR, Or.inr ?_⟩
    have hshort : (occurrences paths base).card ≤ 2 * (surviving paths base S h label τ).card :=
      by omega
    have hshort' : ((occurrences paths base).card : ℝ) ≤
        2 * ((surviving paths base S h label τ).card : ℝ) := by exact_mod_cast hshort
    have := mul_le_mul_of_nonneg_right hshort' (mul_nonneg hℓ.le ha)
    nlinarith

end ChargeDichotomy


/-- Explicit parameter inequalities used by both branches. -/
theorem charging_parameters {lam L σ : ℝ} (hlam : 4 ≤ lam) (hL : 0 < L)
    (hσ : 1 ≤ σ) (hσL : σ ≤ L) :
    0 < σ / (lam ^ 2 * L) ∧
      2 * (σ / (lam ^ 2 * L)) ≤ σ / L ∧
      2 * (1 / (8 * lam)) + σ / (lam ^ 2 * L) ≤ 1 / (2 * lam) := by
  have hlamp : 0 < lam := by linarith
  have hσp : 0 < σ := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · apply (le_div_iff₀ hL).mpr
    have heq : 2 * (σ / (lam ^ 2 * L)) * L = 2 * σ / lam ^ 2 := by field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < lam ^ 2)).mpr
    have hsq : 2 ≤ lam ^ 2 := by nlinarith
    calc
      2 * σ ≤ lam ^ 2 * σ := mul_le_mul_of_nonneg_right hsq hσp.le
      _ = σ * lam ^ 2 := mul_comm _ _
  · have ht : σ / (lam ^ 2 * L) ≤ 1 / lam ^ 2 := by
      apply (div_le_div_iff₀ (by positivity : 0 < lam ^ 2 * L) (by positivity : 0 < lam ^ 2)).mpr
      nlinarith
    have hlast : 2 * (1 / (8 * lam)) + 1 / lam ^ 2 ≤ 1 / (2 * lam) := by
      field_simp
      nlinarith
    calc
      _ ≤ 2 * (1 / (8 * lam)) + 1 / lam ^ 2 := by linarith
      _ ≤ _ := hlast


section WitnessGraphBridges
variable [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Full-deletion reachability is transitive via genuine path composition
and loop erasure, retaining containment in the two input vertex supports. -/
theorem levelResidualPath_trans {G : Digraph V} {X : Finset V} {u v z : V}
    (huv : LevelResidualPath G X u v) (hvz : LevelResidualPath G X v z) :
    LevelResidualPath G X u z := by
  obtain ⟨p, hp⟩ := huv
  obtain ⟨q, hq⟩ := hvz
  obtain ⟨r, hr⟩ := p.exists_composition q
  refine ⟨r, ?_⟩
  intro x hx
  rcases Finset.mem_union.mp (hr hx) with hx | hx
  · exact hp x hx
  · exact hq x hx

omit [Fintype V] in
/-- Lift an actual subtype residual path to the graph's full-deletion
relation. Every vertex, including both endpoints, carries its outside proof. -/
theorem levelResidualPath_of_residual {G : Digraph V} {X : Finset V} {u v : V}
    (hu : u ∉ X) (hv : v ∉ X)
    (q : SimplePath (WitnessPrefix.residualGraph G X) ⟨u, hu⟩ ⟨v, hv⟩) :
    LevelResidualPath G X u v := by
  let p : SimplePath G u v := {
    edgeLength := q.edgeLength
    vertex := fun i => (q.vertex i).val
    source_eq := congrArg Subtype.val q.source_eq
    target_eq := congrArg Subtype.val q.target_eq
    injective := fun a b hab => q.injective (Subtype.ext hab)
    adjacent := q.adjacent }
  refine ⟨p, ?_⟩
  intro z hz
  obtain ⟨i, rfl⟩ := (p.mem_vertices z).mp hz
  exact (q.vertex i).property

omit [Fintype V] in
/-- Ordered internal carrier certificates imply common-residual forward
reachability for the actual witness list. Original demand endpoints may be cut. -/
theorem certificate_forward {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {l : WitnessSystem.NodeList V}
    (hc : WitnessSystem.Certificate G w X s t L B l) :
    l.val.Pairwise (LevelResidualPath G X) := by
  obtain ⟨p, hp, indices, hord, hmap, hinternal⟩ := hc.ordered_carrier
  rw [← hmap, List.pairwise_map]
  apply hord.imp_of_mem
  intro i j hi hj hij
  obtain ⟨hi0, _hiLast⟩ := hinternal i hi
  obtain ⟨_hj0, hjLast⟩ := hinternal j hj
  exact levelResidualPath_of_residual _ _
    (WitnessPrefix.residualSegment p hp i j hi0 hij.le hjLast)

/-- Finite carrier reachability is explicitly checked before using toReal. -/
theorem certificate_distance_ne_top {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {l : WitnessSystem.NodeList V}
    (hc : WitnessSystem.Certificate G w X s t L B l) {v : V} (hv : v ∈ l.val) :
    vertexDistance G w s v ≠ ⊤ := by
  obtain ⟨p, _hp, indices, _hord, hmap, _hinternal⟩ := hc.ordered_carrier
  rw [← hmap] at hv
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hv
  exact (WitnessPrefix.distance_lt_top p w i).ne

/-- Below-one witness heights are unchanged by clipping; infinity cannot
pass this bridge because its exclusion was proved from the actual carrier. -/
theorem certificate_clipped_height {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {l : WitnessSystem.NodeList V}
    (hc : WitnessSystem.Certificate G w X s t L B l) {v : V} (hv : v ∈ l.val) :
    (min 1 (vertexDistance G w s v)).toReal = (vertexDistance G w s v).toReal := by
  have hfin := certificate_distance_ne_top hc hv
  have hbelow : vertexDistance G w s v < 1 :=
    (ENNReal.toReal_lt_toReal hfin (by simp)).mp (by simpa using hc.height_lt_one v hv)
  rw [min_eq_right hbelow.le]

/-- The real clipped heights required by charging are supplied by the
certified witnesses, rather than assumed separately at graph instantiation. -/
theorem certificate_clipped_separated {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {l : WitnessSystem.NodeList V}
    (hc : WitnessSystem.Certificate G w X s t L B l) :
    l.val.Pairwise (fun u v => (min 1 (vertexDistance G w s u)).toReal + 1 / L ≤
      (min 1 (vertexDistance G w s v)).toReal) := by
  apply hc.separated.imp_of_mem
  intro u v hu hv hsep
  rwa [certificate_clipped_height hc hu, certificate_clipped_height hc hv]

end WitnessGraphBridges


section ExplicitWitnessScale
variable [Fintype I] [Fintype V] [Fintype P] [Nonempty I] [Nonempty V]

/-- Finite form of the two charging bounds, with the corrected witness
constant `lam = 256 B` and an explicit logarithmic shortcut budget.
Everything quantified in this theorem is actual path-system data. -/
theorem exists_value_witness_scale (paths : I → List V) (label : I → P)
    (h : P → V → ℝ) (R : V → V → Prop)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    {B L σ : ℝ} (hB : 1 ≤ B) (hL : 64 * B ≤ L) (hσ : 1 ≤ σ) (hσL : σ ≤ L)
    (hn : ∀ i, (paths i).Nodup) (hd : LabelDisjoint paths label)
    (hs : ∀ i, (paths i).Pairwise (fun x y => h (label i) x + 1 / L ≤ h (label i) y))
    (hf : ∀ i, (paths i).Pairwise R)
    (hmin : ∀ i, L / (4 * B) ≤ ((paths i).length : ℝ))
    (hmax : ∀ i, ((paths i).length : ℝ) ≤ L + 1) :
    ∃ x y, R x y ∧
      min (σ * averageDegree paths /
        (16 * (256 * B) ^ 3 * L * (Nat.log2 (Fintype.card V) + 1)))
        (L ^ 2 * averageDegree paths /
        (256 * (256 * B) ^ 3 * σ * Fintype.card V * (Nat.log2 (Fintype.card V) + 2))) ≤
      totalValue h x y := by
  classical
  let lam : ℝ := 256 * B
  let H : ℕ := Nat.log2 (Fintype.card V) + 1
  let τ : ℝ := σ / (lam ^ 2 * L)
  let ℓ : ℝ := L / (8 * lam)
  let a : ℝ := 1 / (8 * lam)
  have hBp : 0 < B := by linarith
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hlamp : 0 < lam := by dsimp [lam]; positivity
  have hlam : 4 ≤ lam := by dsimp [lam]; linarith
  have hHp : (0 : ℝ) < H := by dsimp [H]; positivity
  have hHcast : (H : ℝ) = (Nat.log2 (Fintype.card V) : ℝ) + 1 := by simp [H]
  have hHcast2 : (H : ℝ) + 1 = (Nat.log2 (Fintype.card V) : ℝ) + 2 := by rw [hHcast]; ring
  have hnVp : (0 : ℝ) < Fintype.card V := by positivity
  have hσp : 0 < σ := by linarith
  obtain ⟨hτ, hsmall, hparam⟩ := charging_parameters hlam hLp hσ hσL
  have hlength : ∀ i, 8 ≤ (paths i).length := by
    intro i
    have hlow : (16 : ℝ) ≤ L / (4 * B) :=
      (le_div_iff₀ (by positivity : 0 < 4 * B)).mpr (by linarith)
    have hq : (8 : ℝ) ≤ (paths i).length := by linarith [hmin i]
    exact_mod_cast hq
  have hminWeak : ∀ i, L ≤ lam * (paths i).length := by
    intro i
    have hm := (div_le_iff₀ (by positivity : 0 < 4 * B)).mp (hmin i)
    have hq : (0 : ℝ) ≤ (paths i).length := by positivity
    dsimp [lam]
    nlinarith
  have hprefix : ∀ i, ℓ ≤ ((quarterPrefix (paths i)).length : ℝ) := by
    intro i
    have hq : ((paths i).length : ℝ) ≤ 8 * (quarterPrefix (paths i)).length :=
      by exact_mod_cast quarterPrefix_mass_lower_bound (hlength i)
    apply (div_le_iff₀ (by positivity : 0 < 8 * lam)).mpr
    have := mul_le_mul_of_nonneg_left hq hlamp.le
    nlinarith [hminWeak i]
  have hgap : ∀ i, 2 * a + τ ≤ (paths i).length / (2 * L) := by
    intro i
    refine hparam.trans ?_
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * lam) (by positivity : 0 < 2 * L)).mpr
    nlinarith [hminWeak i]
  obtain ⟨b, hb⟩ := exists_basePath_witness_scale paths hn hlength hBp hmin
  have hposInc : 0 < totalIncidence paths := by
    have hsingle : (paths b).length ≤ totalIncidence paths :=
      Finset.single_le_sum (f := fun i => (paths i).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    have := hlength b
    omega
  have hdp : 0 < averageDegree paths := by
    unfold averageDegree
    exact div_pos (by exact_mod_cast hposInc) hnVp
  have hscore : 0 < baseScore paths b := by
    have hp : 0 < L * averageDegree paths / (256 * B) := by positivity
    have hreal : (0 : ℝ) < baseScore paths b := lt_of_lt_of_le hp hb
    exact_mod_cast hreal
  obtain ⟨S, M, hSc, hSvalid, hMc, _hMmem, htwo⟩ := exists_shortcuts R htrans
    (paths b) (hn b) (hf b)
  have hlenV : (paths b).length ≤ Fintype.card V := by
    rw [← List.toFinset_card_of_nodup (hn b)]
    exact Finset.card_le_univ _
  have hlog : Nat.log2 (paths b).length + 1 ≤ H := by
    dsimp [H]
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.add_le_add_right (Nat.log_mono_right hlenV) 1
  have hM : ∀ x, (M x).card ≤ H := fun x => (hMc x).trans hlog
  have hSc' : (S.card : ℝ) ≤ 4 * L * H := by
    have hcard : S.card ≤ 2 * (paths b).length * H :=
      hSc.trans (Nat.mul_le_mul_left _ hlog)
    have hcard' : (S.card : ℝ) ≤ 2 * (paths b).length * H := by exact_mod_cast hcard
    have hq := hmax b
    have hle : ((paths b).length : ℝ) ≤ 2 * L := by linarith
    have := mul_le_mul_of_nonneg_right hle hHp.le
    nlinarith
  have hocc : (occurrences paths (paths b)).card = baseScore paths b := occurrences_card paths (paths b)
  obtain ⟨x, y, hR, hlong | hshort⟩ := exists_charge_dichotomy paths (paths b) S M h label R
    hLp hσ hτ (by dsimp [ℓ]; positivity) (by dsimp [a]; positivity)
    hsmall hn hd hs hf (hf b) (fun x y he => (hSvalid x y he).2.2.2) hM htwo
    hprefix hgap (by rw [hocc]; exact hscore)
  · refine ⟨x, y, hR, (min_le_left _ _).trans ?_⟩
    rw [← hHcast]
    change σ * averageDegree paths / (16 * lam ^ 3 * L * H) ≤ totalValue h x y
    rw [hocc] at hlong
    have hv : 0 ≤ totalValue h x y := Finset.sum_nonneg (fun _ _ => value_nonneg ..)
    have hupper := mul_le_mul_of_nonneg_right hSc'
      (show 0 ≤ 4 * totalValue h x y by positivity)
    have hlower := mul_le_mul_of_nonneg_right hb hτ.le
    change L * averageDegree paths / lam * τ ≤ (baseScore paths b : ℝ) * τ at hlower
    have hcombined : L * averageDegree paths / lam * τ ≤ 16 * L * H * totalValue h x y := by
      nlinarith
    dsimp [τ] at hcombined
    have hrewrite : L * averageDegree paths / lam * (σ / (lam ^ 2 * L)) =
        σ * averageDegree paths / lam ^ 3 := by field_simp
    rw [hrewrite] at hcombined
    have hmul := (div_le_iff₀ (by positivity : 0 < lam ^ 3)).mp hcombined
    apply (div_le_iff₀ (by positivity : 0 < 16 * lam ^ 3 * L * H)).mpr
    nlinarith
  · refine ⟨x, y, hR, (min_le_right _ _).trans ?_⟩
    rw [← hHcast2]
    change L ^ 2 * averageDegree paths /
      (256 * lam ^ 3 * σ * Fintype.card V * (H + 1)) ≤ totalValue h x y
    rw [hocc] at hshort
    have hℓa : 0 ≤ ℓ * a := by dsimp [ℓ, a]; positivity
    have hlower := mul_le_mul_of_nonneg_right hb hℓa
    change L * averageDegree paths / lam * (ℓ * a) ≤ (baseScore paths b : ℝ) * (ℓ * a) at hlower
    have hcombined : L * averageDegree paths / lam * (ℓ * a) ≤
        4 * σ * Fintype.card V * (H + 1) * totalValue h x y := by nlinarith
    have hrewrite : L * averageDegree paths / lam * (ℓ * a) =
        L ^ 2 * averageDegree paths / (64 * lam ^ 3) := by
      dsimp [ℓ, a]
      field_simp
      ring
    rw [hrewrite] at hcombined
    have hmul := (div_le_iff₀ (by positivity : 0 < 64 * lam ^ 3)).mp hcombined
    apply (div_le_iff₀ (by positivity : 0 < 256 * lam ^ 3 * σ * Fintype.card V * (H + 1))).mpr
    nlinarith

end ExplicitWitnessScale


section BalancedWitnessScale
variable [Fintype I] [Fintype V] [Fintype P] [Nonempty I] [Nonempty V]

/-- The balanced choice is real-valued. Its range is proved from the finite
hard-regime assumptions `L ≤ n ≤ L³`, so no integer rounding is hidden. -/
theorem balanced_parameter {L n : ℝ} (hL : 0 < L) (hn : 0 < n)
    (hLn : L ≤ n) (hnL : n ≤ L ^ 3) :
    1 ≤ L * Real.sqrt (L / n) ∧ L * Real.sqrt (L / n) ≤ L ∧
      (L * Real.sqrt (L / n)) ^ 2 * n = L ^ 3 := by
  have hratio : 0 ≤ L / n := by positivity
  have ht := Real.sqrt_nonneg (L / n)
  have htsq := Real.sq_sqrt hratio
  have hratioOne : L / n ≤ 1 := (div_le_one hn).mpr hLn
  have htOne : Real.sqrt (L / n) ≤ 1 := by nlinarith
  have hbal : (L * Real.sqrt (L / n)) ^ 2 * n = L ^ 3 := by
    rw [mul_pow, htsq]
    field_simp
  refine ⟨?_, ?_, hbal⟩
  · by_contra hbad
    have hσn : 0 ≤ L * Real.sqrt (L / n) := mul_nonneg hL.le ht
    have hsq : (L * Real.sqrt (L / n)) ^ 2 < 1 := by nlinarith
    have hh := mul_lt_mul_of_pos_right hsq hn
    nlinarith
  · nlinarith

/-- Exact elementary form of the three-halves power on the positive ratio. -/
theorem three_halves_power {z : ℝ} (hz : 0 < z) :
    z ^ (3 / 2 : ℝ) = z * Real.sqrt z := by
  rw [Real.sqrt_eq_rpow]
  have he : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
  rw [he, Real.rpow_add hz, Real.rpow_one]

/-- Explicit finite witness-system value lower bound. The stable mass enters
only through the proved witness-cardinality comparison; every chosen pair is
reachable in the supplied common residual relation. -/
theorem exists_balanced_value (paths : I → List V) (label : I → P)
    (h : P → V → ℝ) (R : V → V → Prop)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    {B L r mass : ℝ} (hB : 1 ≤ B) (hL : 64 * B ≤ L) (hr : 0 < r)
    (_hmass : 0 ≤ mass)
    (hcard : mass / (8 * B * r) ≤ Fintype.card I)
    (hLn : L ≤ Fintype.card V) (hnL : (Fintype.card V : ℝ) ≤ L ^ 3)
    (hn : ∀ i, (paths i).Nodup) (hd : LabelDisjoint paths label)
    (hs : ∀ i, (paths i).Pairwise (fun x y => h (label i) x + 1 / L ≤ h (label i) y))
    (hf : ∀ i, (paths i).Pairwise R)
    (hmin : ∀ i, L / (4 * B) ≤ ((paths i).length : ℝ))
    (hmax : ∀ i, ((paths i).length : ℝ) ≤ L + 1) :
    ∃ x y, R x y ∧ mass * (L / Fintype.card V) ^ (3 / 2 : ℝ) /
      (2048 * B * r * (256 * B) ^ 4 * (Nat.log2 (Fintype.card V) + 2)) ≤
        totalValue h x y := by
  let n : ℝ := Fintype.card V
  let lam : ℝ := 256 * B
  let H : ℝ := Nat.log2 (Fintype.card V) + 1
  let σ : ℝ := L * Real.sqrt (L / n)
  let d : ℝ := averageDegree paths
  have hnpos : 0 < n := by dsimp [n]; positivity
  have hBp : 0 < B := by linarith
  have hLp : 0 < L := by linarith
  have hlamp : 0 < lam := by dsimp [lam]; positivity
  have hHp : 0 < H := by dsimp [H]; positivity
  have hHcast2 : H + 1 = (Nat.log2 (Fintype.card V) : ℝ) + 2 := by dsimp [H]; ring
  have hdn : 0 ≤ d := by dsimp [d, averageDegree]; positivity
  obtain ⟨hσ, hσL, hbalance⟩ := balanced_parameter hLp hnpos hLn hnL
  have hσp : 0 < σ := by dsimp [σ]; positivity
  obtain ⟨x, y, hR, hval⟩ := exists_value_witness_scale paths label h R htrans
    hB hL hσ hσL hn hd hs hf hmin hmax
  refine ⟨x, y, hR, ?_⟩
  have hbound : d * σ / L / (256 * lam ^ 3 * (H + 1)) ≤ totalValue h x y := by
    apply le_trans _ hval
    apply le_min
    · change d * σ / L / (256 * lam ^ 3 * (H + 1)) ≤ σ * d / (16 * lam ^ 3 * L * H)
      have hnumer : 0 ≤ σ * d := mul_nonneg hσp.le hdn
      have hden : 16 * lam ^ 3 * L * H ≤ 256 * lam ^ 3 * L * (H + 1) := by
        have hp : 0 ≤ lam ^ 3 * L := by positivity
        have hpH := mul_nonneg hp hHp.le
        nlinarith
      have hc := div_le_div_of_nonneg_left hnumer
        (show 0 < 16 * lam ^ 3 * L * H by positivity) hden
      convert hc using 1
      field_simp
    · rw [← hHcast2]
      change d * σ / L / (256 * lam ^ 3 * (H + 1)) ≤
        L ^ 2 * d / (256 * lam ^ 3 * σ * n * (H + 1))
      apply le_of_eq
      have hb : d * (σ ^ 2 * n) = d * L ^ 3 := congrArg (fun z : ℝ => d * z) hbalance
      field_simp
      nlinarith only [hb]
  have hlen : ∀ i, L / lam ≤ ((paths i).length : ℝ) := by
    intro i
    have hm := (div_le_iff₀ (by positivity : 0 < 4 * B)).mp (hmin i)
    apply (div_le_iff₀ hlamp).mpr
    have hq : (0 : ℝ) ≤ (paths i).length := by positivity
    dsimp [lam]
    nlinarith
  have htotal : (Fintype.card I : ℝ) * (L / lam) ≤ totalIncidence paths := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => hlen i)
    simpa [totalIncidence, Nat.cast_sum] using hh
  have hdegree : (Fintype.card I : ℝ) * L / (lam * n) ≤ d := by
    dsimp [d, averageDegree]
    change (Fintype.card I : ℝ) * L / (lam * n) ≤ (totalIncidence paths : ℝ) / n
    have hh := div_le_div_of_nonneg_right htotal hnpos.le
    convert hh using 1
    field_simp
  have hdegreeMass : mass * L / (8 * B * r * lam * n) ≤ d := by
    have hm := mul_le_mul_of_nonneg_right hcard (show 0 ≤ L / (lam * n) by positivity)
    have hm' : mass * L / (8 * B * r * lam * n) ≤
        (Fintype.card I : ℝ) * L / (lam * n) := by
      convert hm using 1 <;> field_simp
    exact hm'.trans hdegree
  have hfactor : 0 ≤ σ / L / (256 * lam ^ 3 * (H + 1)) := by positivity
  have hfinal := mul_le_mul_of_nonneg_right hdegreeMass hfactor
  have hpow : (L / n) ^ (3 / 2 : ℝ) = L / n * Real.sqrt (L / n) :=
    three_halves_power (by positivity)
  have hid : mass * (L / n) ^ (3 / 2 : ℝ) /
      (2048 * B * r * lam ^ 4 * (H + 1)) =
        (mass * L / (8 * B * r * lam * n)) * (σ / L / (256 * lam ^ 3 * (H + 1))) := by
    rw [hpow]
    dsimp [σ]
    field_simp
    ring
  have hlower : mass * (L / n) ^ (3 / 2 : ℝ) /
      (2048 * B * r * lam ^ 4 * (H + 1)) ≤ d * σ / L / (256 * lam ^ 3 * (H + 1)) := by
    rw [hid]
    convert hfinal using 1
    ring
  have hh := hlower.trans hbound
  convert hh using 1
  dsimp [n, lam, H]
  ring

end BalancedWitnessScale


section StableGraphValue
variable [DecidableEq V] [Fintype V] [Fintype P] [Nonempty V]

/-- Corrected finite graph-value theorem (Lemma 17) at an actual stable
current state. Its witness system, shortcut set, charges, short-case fan and
final reachable pair are all constructed. The right side is the exact sum
of the existing frozen level-separation probabilities. This theorem concerns
positive current mass and the hard regime; it does not claim the stochastic
rounding schedule or the paper's full flow-cut theorem. -/
theorem exists_stable_graph_value (G : Digraph V) (demand : P → V × V)
    (w opt : P → V → ℝ≥0) (X : Finset V) {L B r : ℝ}
    (hB : 1 ≤ B) (hL : 64 * B ≤ L) (hr : 1 < r)
    (hLn : L ≤ Fintype.card V) (hnL : (Fintype.card V : ℝ) ≤ L ^ 3)
    (hcut : ∀ p, 1 ≤ vertexDistance G (w p) (demand p).1 (demand p).2)
    (hcap : ∀ p v, v ∉ X → (w p v : ℝ) ≤ B / L)
    (hopt : ∀ p z, CandidateOptimization.IsCandidate G {demand p} X
        ⟨4 * B / L, by
          have hLp : 0 < L := by linarith
          positivity⟩ z →
      CandidateOptimization.outsideMass X (opt p) ≤ CandidateOptimization.outsideMass X z)
    (hstable : (∑ p, (CandidateOptimization.outsideMass X (w p) : ℝ)) ≤
      r * ∑ p, (CandidateOptimization.outsideMass X (opt p) : ℝ))
    (hpositive : 0 < ∑ p, (CandidateOptimization.outsideMass X (w p) : ℝ)) :
    ∃ u v, LevelResidualPath G X u v ∧
      (∑ p, (CandidateOptimization.outsideMass X (w p) : ℝ)) *
        (L / Fintype.card V) ^ (3 / 2 : ℝ) /
        (2048 * B * r * (256 * B) ^ 4 * (Nat.log2 (Fintype.card V) + 2)) ≤
      ∑ p, (levelSeparationValue G (w p) (demand p).1 u v).toReal := by
  classical
  obtain ⟨F, hF, hmass⟩ := WitnessSystem.exists_system_of_stable G demand w opt X
    hB hL hr hcut hcap hopt hstable
  let J := WitnessSystem.Index F
  let paths : J → List V := WitnessSystem.indexedPath
  let labels : J → P := fun i => i.1
  let heights : P → V → ℝ := clippedHeight (fun p v => vertexDistance G (w p) (demand p).1 v)
  have hcard : (∑ p, (CandidateOptimization.outsideMass X (w p) : ℝ)) /
      (8 * B * r) ≤ (Fintype.card J : ℝ) := by
    simpa only [J, WitnessSystem.card_index, Nat.cast_sum] using hmass
  have hcardpos : 0 < Fintype.card J := by
    have hdiv : 0 < (∑ p, (CandidateOptimization.outsideMass X (w p) : ℝ)) / (8 * B * r) :=
      div_pos hpositive (by
        have hBp : 0 < B := by linarith
        have hrp : 0 < r := by linarith
        positivity)
    have hh : (0 : ℝ) < Fintype.card J := hdiv.trans_le hcard
    exact_mod_cast hh
  let : Nonempty J := Fintype.card_pos_iff.mp hcardpos
  have hcert : ∀ i : J, WitnessSystem.Certificate G (w i.1) X (demand i.1).1
      (demand i.1).2 L B i.2.val := fun i => (hF i.1).1.1 i.2.val i.2.property
  have hn : ∀ i, (paths i).Nodup := WitnessSystem.indexedPath_nodup
  have hd : LabelDisjoint paths labels := by
    intro i j hij hne
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    apply hne
    exact WitnessSystem.index_eq_of_same_label_of_shared (fun p => (hF p).1.2) hij
      (by simpa only [List.mem_toFinset] using hvi) (by simpa only [List.mem_toFinset] using hvj)
  have hs : ∀ i, (paths i).Pairwise (fun x y => heights (labels i) x + 1 / L ≤ heights (labels i) y) :=
    fun i => certificate_clipped_separated (hcert i)
  have hf : ∀ i, (paths i).Pairwise (LevelResidualPath G X) :=
    fun i => certificate_forward (hcert i)
  have hmin : ∀ i, L / (4 * B) ≤ ((paths i).length : ℝ) := by
    intro i
    exact (hcert i).length_lower.trans (by exact_mod_cast Nat.sub_le (paths i).length 1)
  have hmax : ∀ i, ((paths i).length : ℝ) ≤ L + 1 := fun i => (hcert i).length_upper
  obtain ⟨u, v, hR, hval⟩ := exists_balanced_value paths labels heights (LevelResidualPath G X)
    (fun hh₁ hh₂ => levelResidualPath_trans hh₁ hh₂) hB hL (by linarith : 0 < r)
    hpositive.le hcard hLn hnL hn hd hs hf hmin hmax
  refine ⟨u, v, hR, hval.trans_eq ?_⟩
  unfold totalValue
  apply Finset.sum_congr rfl
  intro p _
  exact value_eq_levelSeparationValue_toReal G w (fun p => (demand p).1) p u v

end StableGraphValue

end
end DirectedFlowCutGap.PathSystemCharging
