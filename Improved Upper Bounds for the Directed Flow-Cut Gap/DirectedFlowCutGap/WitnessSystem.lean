import DirectedFlowCutGap.WitnessPrefix
import DirectedFlowCutGap.CandidateOptimization
import Mathlib.Data.Fintype.List

/-!
# Finite maximal endpoint-aware witness families

The family is selected from the genuine finite type of lists with no repeated
vertices. A missing low-used-weight carrier supplies a new disjoint list via
`WitnessPrefix`, contradicting maximal cardinality. This constructs the
stopping-condition candidate rather than assuming a path-witness oracle.
-/

namespace DirectedFlowCutGap.WitnessSystem

noncomputable section
open scoped BigOperators NNReal ENNReal
open WitnessPrefix CandidateOptimization

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Lists retain their order; different labels will use separate family indices. -/
abbrev NodeList (V : Type*) := {l : List V // l.Nodup}

def support (l : NodeList V) : Finset V := l.val.toFinset

omit [Fintype V] in
@[simp] theorem mem_support (l : NodeList V) (v : V) : v ∈ support l ↔ v ∈ l.val := by
  simp [support]

omit [Fintype V] in
@[simp] theorem card_support (l : NodeList V) : (support l).card = l.val.length := by
  exact List.toFinset_card_of_nodup l.property

/-- A concrete ordered internal subsequence, with its source-labelled heights.
The source and target of the carrier are not required to lie outside `X`. -/
structure Certificate (G : Digraph V) (w : V → ℝ≥0) (X : Finset V)
    (s t : V) (L B : ℝ) (l : NodeList V) : Prop where
  nonempty : l.val ≠ []
  length_lower : L / (4 * B) ≤ ((l.val.length - 1 : ℕ) : ℝ)
  length_upper : (l.val.length : ℝ) ≤ L + 1
  outside : ∀ v ∈ l.val, v ∉ X
  ordered_carrier : ∃ p : SimplePath G s t, p.Avoids X ∧ ∃ indices : List ℕ,
    indices.Pairwise (· < ·) ∧ indices.map (vertex p) = l.val ∧
      ∀ i ∈ indices, 0 < i ∧ i < p.edgeLength
  separated : l.val.Pairwise (fun u v =>
    (vertexDistance G w s u).toReal + 1 / L ≤ (vertexDistance G w s v).toReal)
  height_lt_one : ∀ v ∈ l.val, (vertexDistance G w s v).toReal < 1

/-- A deficient actual carrier constructs a certified list avoiding all used
vertices. This is the concrete extension step for finite maximality. -/
theorem exists_fresh (G : Digraph V) (w : V → ℝ≥0) (X U : Finset V)
    {s t : V} (p : SimplePath G s t) (havoid : p.Avoids X)
    (hcut : 1 ≤ vertexDistance G w s t) {L B : ℝ}
    (hB : 1 ≤ B) (hL : 64 * B ≤ L)
    (hcap : ∀ v ∉ X, (w v : ℝ) ≤ B / L)
    (hused : (∑ v ∈ p.internalVertices ∩ U, (w v : ℝ)) < 1 / 4) :
    ∃ l : NodeList V, Certificate G w X s t L B l ∧
      Disjoint (support l) U := by
  obtain ⟨c⟩ := exists_firstCrossing p w hcut
  let l : NodeList V := ⟨c.selectedVertices U (1 / L), c.selectedVertices_nodup U (1 / L)⟩
  obtain ⟨hne, hlo, hhi⟩ := c.selectedVertices_bounds havoid hB hL hcap hused
  have hlen : 1 ≤ l.val.length := List.length_pos_iff_ne_nil.mpr hne
  have hcast : ((l.val.length - 1 : ℕ) : ℝ) = (l.val.length : ℝ) - 1 := by
    rw [Nat.cast_sub hlen, Nat.cast_one]
  have hLpos : 0 < L := by linarith
  refine ⟨l, ?_, ?_⟩
  · refine ⟨hne, hlo, ?_, ?_, ?_, ?_, ?_⟩
    · change ((l.val.length - 1 : ℕ) : ℝ) ≤ L at hhi
      rw [hcast] at hhi
      linarith
    · intro v hv
      exact (c.selectedVertices_internal havoid (1 / L) hv).2.1
    · refine ⟨p, havoid,
        (WitnessThinning.scan (height p w) (deleted p U) (1 / L) c.N).selected,
        WitnessThinning.selected_increasing _ _ _ _, rfl, ?_⟩
      intro i hi
      obtain ⟨hiN, hdel⟩ := WitnessThinning.selected_mem _ _ _ _ i hi
      have hiz : i ≠ 0 := fun hz => hdel (Or.inl hz)
      exact ⟨by omega, by have := c.before_target; omega⟩
    · exact c.selectedVertices_separated U (by positivity)
    · exact fun v hv => c.selectedVertices_height_lt_one U (1 / L) hv
  · apply Finset.disjoint_left.mpr
    intro v hv hU
    exact (c.selectedVertices_internal havoid (1 / L) ((mem_support l v).mp hv)).2.2 hU

def used (F : Finset (NodeList V)) : Finset V := F.biUnion support

omit [Fintype V] in
@[simp] theorem mem_used (F : Finset (NodeList V)) (v : V) :
    v ∈ used F ↔ ∃ l ∈ F, v ∈ support l := by simp [used]

def ValidFamily (G : Digraph V) (w : V → ℝ≥0) (X : Finset V)
    (s t : V) (L B : ℝ) (F : Finset (NodeList V)) : Prop :=
  (∀ l ∈ F, Certificate G w X s t L B l) ∧
    (F : Set (NodeList V)).PairwiseDisjoint support

omit [Fintype V] in
theorem valid_empty (G : Digraph V) (w : V → ℝ≥0) (X : Finset V)
    (s t : V) (L B : ℝ) : ValidFamily G w X s t L B ∅ := by
  simp [ValidFamily, Set.PairwiseDisjoint, Set.Pairwise]

omit [Fintype V] in
theorem used_outside {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {F : Finset (NodeList V)}
    (hF : ValidFamily G w X s t L B F) {v : V} (hv : v ∈ used F) : v ∉ X := by
  obtain ⟨l, hl, hvl⟩ := (mem_used F v).mp hv
  exact (hF.1 l hl).outside v ((mem_support l v).mp hvl)

omit [Fintype V] in
theorem fresh_not_mem {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {F : Finset (NodeList V)} {l : NodeList V}
    (hl : Certificate G w X s t L B l) (hfresh : Disjoint (support l) (used F)) :
    l ∉ F := by
  intro hlF
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil l.val hl.nonempty
  have hvs : v ∈ support l := (mem_support l v).mpr hv
  exact Finset.disjoint_left.mp hfresh hvs ((mem_used F v).mpr ⟨l, hlF, hvs⟩)

omit [Fintype V] in
theorem valid_insert {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {F : Finset (NodeList V)} {l : NodeList V}
    (hF : ValidFamily G w X s t L B F)
    (hl : Certificate G w X s t L B l) (hfresh : Disjoint (support l) (used F)) :
    ValidFamily G w X s t L B (insert l F) := by
  constructor
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hl
    · exact hF.1 q hq
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hae | haF
    · subst a
      apply Finset.disjoint_left.mpr
      intro v hva hvb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hab rfl
      · exact Finset.disjoint_left.mp hfresh hva ((mem_used F v).mpr ⟨b, hb, hvb⟩)
    · rcases Finset.mem_insert.mp hb with hbe | hbF
      · subst b
        apply Finset.disjoint_left.mpr
        intro v hva hvl
        exact Finset.disjoint_left.mp hfresh hvl ((mem_used F v).mpr ⟨a, haF, hva⟩)
      · exact hF.2 haF hbF hab

/-- The stopping condition quantifies every actual internally avoiding path. -/
def Covers (G : Digraph V) (w : V → ℝ≥0) (X : Finset V) (s t : V)
    (F : Finset (NodeList V)) : Prop :=
  ∀ p : SimplePath G s t, p.Avoids X →
    (1 : ℝ) / 4 ≤ ∑ v ∈ p.internalVertices ∩ used F, (w v : ℝ)

/-- Finite maximality gives a family with the genuine path-coverage stopping
condition; its existence is not assumed in the graph theorem. -/
theorem exists_maximal_family (G : Digraph V) (w : V → ℝ≥0) (X : Finset V)
    (s t : V) (hcut : 1 ≤ vertexDistance G w s t) {L B : ℝ}
    (hB : 1 ≤ B) (hL : 64 * B ≤ L)
    (hcap : ∀ v ∉ X, (w v : ℝ) ≤ B / L) :
    ∃ F : Finset (NodeList V), ValidFamily G w X s t L B F ∧ Covers G w X s t F := by
  classical
  let A : Finset (Finset (NodeList V)) := Finset.univ.filter (ValidFamily G w X s t L B)
  have hA : A.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, valid_empty _ _ _ _ _ _ _⟩⟩
  obtain ⟨F, hFA, hmax⟩ := Finset.exists_max_image A Finset.card hA
  have hF := (Finset.mem_filter.mp hFA).2
  refine ⟨F, hF, ?_⟩
  intro p havoid
  by_contra hcov
  obtain ⟨l, hl, hdisj⟩ := exists_fresh G w X (used F) p havoid hcut hB hL hcap
    (lt_of_not_ge hcov)
  have hnew : insert l F ∈ A := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, valid_insert hF hl hdisj⟩
  have hcard := hmax (insert l F) hnew
  rw [Finset.card_insert_of_notMem (fresh_not_mem hl hdisj)] at hcard
  omega

/-- The comparison cut is one on already cut vertices and four times the
frozen weight on retained witness vertices. -/
def comparison (w : V → ℝ≥0) (X : Finset V) (F : Finset (NodeList V)) (v : V) : ℝ≥0 :=
  if v ∈ X then 1 else if v ∈ used F then 4 * w v else 0

omit [Fintype V] in
/-- Deleted original demand endpoints do not enter the path case split. -/
theorem comparison_fractional {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {F : Finset (NodeList V)} (hcover : Covers G w X s t F) :
    1 ≤ vertexDistance G (comparison w X F) s t := by
  apply (coe_le_vertexDistance_iff G (comparison w X F) s t 1).mpr
  intro p
  by_cases hhit : ∃ v ∈ p.internalVertices, v ∈ X
  · obtain ⟨v, hv, hvX⟩ := hhit
    calc
      1 = comparison w X F v := by simp [comparison, hvX]
      _ ≤ p.weight (comparison w X F) := Finset.single_le_sum (fun _ _ => zero_le) hv
  · have havoid : p.Avoids X := fun v hv hvX => hhit ⟨v, hv, hvX⟩
    have hcov := hcover p havoid
    have hsum : (∑ v ∈ p.internalVertices ∩ used F, 4 * w v) ≤
        p.weight (comparison w X F) := by
      calc
        _ = ∑ v ∈ p.internalVertices ∩ used F, comparison w X F v := by
          apply Finset.sum_congr rfl
          intro v hv
          obtain ⟨hvi, hvU⟩ := Finset.mem_inter.mp hv
          simp [comparison, havoid v hvi, hvU]
        _ ≤ p.weight (comparison w X F) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (by intros; exact zero_le)
    apply NNReal.coe_le_coe.mp
    have hr := NNReal.coe_le_coe.mpr hsum
    simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_ofNat] at hr
    rw [← Finset.mul_sum] at hr
    change (1 : ℝ) ≤ (p.weight (comparison w X F) : ℝ)
    linarith

omit [Fintype V] in
theorem comparison_cap (w : V → ℝ≥0) (X : Finset V) (F : Finset (NodeList V))
    {L B : ℝ} (hB : 0 ≤ B) (hL : 0 < L)
    (hcap : ∀ v ∉ X, (w v : ℝ) ≤ B / L) {v : V} (hv : v ∉ X) :
    (comparison w X F v : ℝ) ≤ 4 * B / L := by
  by_cases hvU : v ∈ used F
  · have hw := hcap v hv
    simp only [comparison, ite_eq_right hv, ite_eq_left hvU, NNReal.coe_mul, NNReal.coe_ofNat]
    calc
      _ ≤ 4 * (B / L) := mul_le_mul_of_nonneg_left hw (by norm_num)
      _ = _ := by ring
  · simp [comparison, hv, hvU]
    positivity

omit [Fintype V] in
theorem comparison_isCandidate {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {F : Finset (NodeList V)} (hcover : Covers G w X s t F)
    {L B : ℝ} (hB : 0 ≤ B) (hL : 0 < L)
    (hcap : ∀ v ∉ X, (w v : ℝ) ≤ B / L) :
    IsCandidate G {(s, t)} X ⟨4 * B / L, by positivity⟩ (comparison w X F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp hab)
    exact comparison_fractional hcover
  · intro v hv
    simp [comparison, hv]
  · intro v hv
    exact NNReal.coe_le_coe.mp (comparison_cap w X F hB hL hcap hv)

omit [Fintype V] in
/-- Every witness has outside weight at most two cap factors. -/
theorem support_weight_le {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {l : NodeList V}
    (hl : Certificate G w X s t L B l) (hB : 0 ≤ B) (hL : 1 ≤ L)
    (hcap : ∀ v ∉ X, (w v : ℝ) ≤ B / L) :
    (∑ v ∈ support l, (w v : ℝ)) ≤ 2 * B := by
  have hLp : 0 < L := by linarith
  have hBL : 0 ≤ B / L := by positivity
  have hsum : (∑ v ∈ support l, (w v : ℝ)) ≤ (l.val.length : ℝ) * (B / L) := by
    calc
      _ ≤ ∑ _v ∈ support l, B / L := Finset.sum_le_sum fun v hv =>
        hcap v (hl.outside v ((mem_support l v).mp hv))
      _ = _ := by simp
  have hratio : (L + 1) * (B / L) ≤ 2 * B := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hLp).mpr
    nlinarith
  exact hsum.trans ((mul_le_mul_of_nonneg_right hl.length_upper hBL).trans hratio)

/-- Disjoint witness supports exactly partition the nonzero outside weights
of the explicit comparison candidate. -/
theorem comparison_outsideMass {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {F : Finset (NodeList V)}
    (hF : ValidFamily G w X s t L B F) :
    (outsideMass X (comparison w X F) : ℝ) =
      4 * ∑ l ∈ F, ∑ v ∈ support l, (w v : ℝ) := by
  have hfilter : (Finset.univ.filter (fun v => v ∉ X)).filter (fun v => v ∈ used F) = used F := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun hv => ⟨used_outside hF hv, hv⟩⟩
  have hm : outsideMass X (comparison w X F) = ∑ v ∈ used F, 4 * w v := by
    calc
      _ = ∑ v ∈ Finset.univ.filter (fun v => v ∉ X),
          if v ∈ used F then 4 * w v else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        simp only [comparison, ite_eq_right (Finset.mem_filter.mp hv).2]
      _ = ∑ v ∈ (Finset.univ.filter (fun v => v ∉ X)).filter (fun v => v ∈ used F),
          4 * w v := (Finset.sum_filter _ _).symm
      _ = _ := by rw [hfilter]
  rw [hm]
  simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_ofNat, ← Finset.mul_sum]
  rw [used, Finset.sum_biUnion hF.2]

theorem comparison_outsideMass_le {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {F : Finset (NodeList V)}
    (hF : ValidFamily G w X s t L B F) (hB : 0 ≤ B) (hL : 1 ≤ L)
    (hcap : ∀ v ∉ X, (w v : ℝ) ≤ B / L) :
    (outsideMass X (comparison w X F) : ℝ) ≤ 8 * B * (F.card : ℝ) := by
  rw [comparison_outsideMass hF]
  calc
    _ ≤ 4 * ∑ _l ∈ F, 2 * B := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun l hl => support_weight_le (hF.1 l hl) hB hL hcap) (by norm_num)
    _ = _ := by simp; ring

/-- Nonempty disjoint lists also give a direct finite progress bound. -/
theorem family_card_le_vertices {G : Digraph V} {w : V → ℝ≥0} {X : Finset V}
    {s t : V} {L B : ℝ} {F : Finset (NodeList V)}
    (hF : ValidFamily G w X s t L B F) : F.card ≤ Fintype.card V := by
  have hcount : F.card ≤ (used F).card := by
    rw [used, Finset.card_biUnion hF.2]
    calc
      F.card = ∑ _l ∈ F, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun l hl => by
        rw [card_support]
        exact List.length_pos_iff_ne_nil.mpr (hF.1 l hl).nonempty
  exact hcount.trans (Finset.card_le_univ _)

/-- Equal vertex lists under different demand labels remain distinct indices. -/
abbrev Index {P : Type*} (F : P → Finset (NodeList V)) :=
  Σ p, {l : NodeList V // l ∈ F p}

def indexedPath {P : Type*} {F : P → Finset (NodeList V)} (i : Index F) : List V :=
  i.2.val.val

omit [DecidableEq V] [Fintype V] in
theorem indexedPath_nodup {P : Type*} {F : P → Finset (NodeList V)} (i : Index F) :
    (indexedPath i).Nodup := i.2.val.property

omit [DecidableEq V] [Fintype V] in
theorem card_index {P : Type*} [Fintype P] (F : P → Finset (NodeList V)) :
    Fintype.card (Index F) = ∑ p, (F p).card := by
  simp only [Index, Fintype.card_sigma, Fintype.card_coe]

omit [Fintype V] in
/-- The exact per-label congestion-one statement needed by charging. -/
theorem index_eq_of_same_label_of_shared {P : Type*}
    {F : P → Finset (NodeList V)}
    (hdisj : ∀ p, (F p : Set (NodeList V)).PairwiseDisjoint support)
    {i j : Index F} (hlabel : i.1 = j.1) {v : V}
    (hi : v ∈ indexedPath i) (hj : v ∈ indexedPath j) : i = j := by
  rcases i with ⟨p, a⟩
  rcases j with ⟨q, b⟩
  change p = q at hlabel
  subst q
  have hab : a.val = b.val := by
    by_contra hne
    have hd := hdisj p a.property b.property hne
    exact Finset.disjoint_left.mp hd ((mem_support a.val v).mpr hi)
      ((mem_support b.val v).mpr hj)
  have he : a = b := Subtype.ext hab
  subst b
  rfl

/-- Aggregate candidate minimality plus the explicit stable gate gives the
source's system-size conclusion with a finite constant. Every family and
every comparison candidate in this theorem is actually constructed above. -/
theorem exists_system_of_stable {P : Type*} [Fintype P]
    (G : Digraph V) (label : P → V × V) (w opt : P → V → ℝ≥0) (X : Finset V)
    {L B r : ℝ} (hB : 1 ≤ B) (hL : 64 * B ≤ L) (hr : 1 < r)
    (hcut : ∀ p, 1 ≤ vertexDistance G (w p) (label p).1 (label p).2)
    (hcap : ∀ p v, v ∉ X → (w p v : ℝ) ≤ B / L)
    (hopt : ∀ p z, IsCandidate G {label p} X
        ⟨4 * B / L, by
          have hLp : 0 < L := by linarith
          positivity⟩ z →
      outsideMass X (opt p) ≤ outsideMass X z)
    (hstable : (∑ p, (outsideMass X (w p) : ℝ)) ≤
      r * ∑ p, (outsideMass X (opt p) : ℝ)) :
    ∃ F : P → Finset (NodeList V),
      (∀ p, ValidFamily G (w p) X (label p).1 (label p).2 L B (F p) ∧
        Covers G (w p) X (label p).1 (label p).2 (F p)) ∧
      (∑ p, (outsideMass X (w p) : ℝ)) / (8 * B * r) ≤
        ∑ p, ((F p).card : ℝ) := by
  classical
  choose F hF hcover using fun p =>
    exists_maximal_family G (w p) X (label p).1 (label p).2 (hcut p) hB hL (hcap p)
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hBn : 0 ≤ B := by linarith
  have hcmp : ∀ p, (outsideMass X (opt p) : ℝ) ≤
      8 * B * ((F p).card : ℝ) := by
    intro p
    have hc := comparison_isCandidate (hcover p) hBn hLp (hcap p)
    have hmin := hopt p (comparison (w p) X (F p)) hc
    exact (NNReal.coe_le_coe.mpr hmin).trans
      (comparison_outsideMass_le (hF p) hBn hLone (hcap p))
  have htotal : (∑ p, (outsideMass X (opt p) : ℝ)) ≤
      8 * B * ∑ p, ((F p).card : ℝ) := by
    calc
      _ ≤ ∑ p, 8 * B * ((F p).card : ℝ) := Finset.sum_le_sum fun p _ => hcmp p
      _ = _ := (Finset.mul_sum _ _ _).symm
  refine ⟨F, fun p => ⟨hF p, hcover p⟩, ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 8 * B * r)).mpr
  calc
    _ ≤ r * ∑ p, (outsideMass X (opt p) : ℝ) := hstable
    _ ≤ r * (8 * B * ∑ p, ((F p).card : ℝ)) :=
      mul_le_mul_of_nonneg_left htotal (by linarith)
    _ = _ := by ring

end

end DirectedFlowCutGap.WitnessSystem
