import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import Mathlib.Data.Prod.Lex
import OnlineReachabilityPreservers.CyclicIntersections

/-! Positive matching certificates give literal last-arc half-free path families. -/

namespace OnlineReachabilityPreservers

open Finset Sum3
open SimpleGraph.TripartiteFromTriangles
open scoped Prod.Lex
local notation "Before" => SourceAudit.BeforeIn

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- A triple viewed as a path on three disjoint copies of its vertex roles. -/
def tripartiteThreeRow {t : Finset (A × B × C)} (i : t) : List (A ⊕ B ⊕ C) :=
  [in₀ i.val.1,in₁ i.val.2.1,in₂ i.val.2.2]

private def triangleLayer : A ⊕ B ⊕ C → Fin 3
  | in₀ _ => 0
  | in₁ _ => 1
  | in₂ _ => 2

private theorem triangleRows_step_cases {t : Finset (A × B × C)} {i : t} {x y : A ⊕ B ⊕ C}
    (step : Before tripartiteThreeRow i x y) :
    (x = in₀ i.val.1 ∧ y = in₁ i.val.2.1) ∨ (x = in₀ i.val.1 ∧ y = in₂ i.val.2.2) ∨
      (x = in₁ i.val.2.1 ∧ y = in₂ i.val.2.2) := by
  have start : x = in₀ i.val.1 ∨ x = in₁ i.val.2.1 ∨ x = in₂ i.val.2.2 := by simpa [tripartiteThreeRow] using step.1
  have finish : y = in₀ i.val.1 ∨ y = in₁ i.val.2.1 ∨ y = in₂ i.val.2.2 := by simpa [tripartiteThreeRow] using step.2.1
  have order := step.2.2
  rcases start with rfl | rfl | rfl <;> rcases finish with rfl | rfl | rfl <;>
    simp [tripartiteThreeRow,in₀,in₁,in₂] at order ⊢

private theorem triangleRows_step_layer {t : Finset (A × B × C)} {i : t} {x y : A ⊕ B ⊕ C}
    (step : Before tripartiteThreeRow i x y) : triangleLayer x < triangleLayer y := by
  rcases triangleRows_step_cases step with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · change (0:Fin 3) < 1
    decide
  · change (0:Fin 3) < 2
    decide
  · change (1:Fin 3) < 2
    decide

private theorem same_triangle_row_of_step {t : Finset (A × B × C)} [ExplicitDisjoint t]
    {i j : t} {x y : A ⊕ B ⊕ C} (left : Before tripartiteThreeRow i x y)
    (right : Before tripartiteThreeRow j x y) : i = j := by
  by_contra different
  have iOn : toTriangle i.val ∈ t.map toTriangle := mem_map.mpr ⟨_,i.property,rfl⟩
  have jOn : toTriangle j.val ∈ t.map toTriangle := mem_map.mpr ⟨_,j.property,rfl⟩
  have apart := toTriangle.injective.ne (Subtype.val_injective.ne different)
  have subsingle := map_toTriangle_disjoint t iOn jOn apart
  exact listBefore_ne left (subsingle ⟨by simpa [tripartiteThreeRow,toTriangle_apply] using left.1,
    by simpa [tripartiteThreeRow,toTriangle_apply] using right.1⟩
    ⟨by simpa [tripartiteThreeRow,toTriangle_apply] using left.2.1,
      by simpa [tripartiteThreeRow,toTriangle_apply] using right.2.1⟩)

private theorem ordered_positive_triangle_rows_halfFree {t : Finset (A × B × C)} [ExplicitDisjoint t]
    [LinearOrder (↥t)] (left : C → A → ℝ) (right : C → B → ℝ)
    (positive : ∀ a b c, (∃ c', (a,b,c') ∈ t) → (0 < left c a+right c b ↔ (a,b,c) ∈ t))
    (arrives : ∀ {i j : t}, i.val.2.2 = j.val.2.2 → left i.val.2.2 i.val.1 < left j.val.2.2 j.val.1 → i < j)
    (cutoff : ℕ) : HalfBridgeFree (Before (tripartiteThreeRow (t := t))) cutoff := by
  intro d _ bridge earlier
  let layer := triangleLayer ∘ bridge.vertex
  have increasing : StrictMono layer := Fin.strictMono_iff_lt_succ.mpr (fun i => triangleRows_step_layer (bridge.arcStep i))
  have size : d+2 ≤ 3 := by simpa using Fintype.card_le_of_injective layer increasing.injective
  have one : d = 0 ∨ d = 1 := by omega
  rcases one with rfl | rfl
  · exact bridge.river_ne_arc 0 (same_triangle_row_of_step bridge.riverStep (bridge.arcStep 0))
  · have firstLayer := triangleRows_step_layer (bridge.arcStep 0)
    have lastLayer := triangleRows_step_layer (bridge.arcStep 1)
    change triangleLayer (bridge.vertex 0) < triangleLayer (bridge.vertex 1) at firstLayer
    change triangleLayer (bridge.vertex 1) < triangleLayer (bridge.vertex 2) at lastLayer
    have v0 : triangleLayer (bridge.vertex 0) = 0 := by rw [Fin.ext_iff]; omega
    have v1 : triangleLayer (bridge.vertex 1) = 1 := by rw [Fin.ext_iff]; omega
    have v2 : triangleLayer (bridge.vertex 2) = 2 := by rw [Fin.ext_iff]; omega
    let i := bridge.arc 0
    let j := bridge.arc 1
    let r := bridge.river
    have first : bridge.vertex 0 = in₀ i.val.1 ∧ bridge.vertex 1 = in₁ i.val.2.1 := by
      rcases triangleRows_step_cases (bridge.arcStep 0) with good | crossed | reversed
      · exact good
      · have equal := congrArg triangleLayer crossed.2
        change triangleLayer (bridge.vertex 1) = 2 at equal
        rw [v1] at equal
        exact (by decide : (1:Fin 3) ≠ 2) equal |>.elim
      · have equal := congrArg triangleLayer reversed.1
        change triangleLayer (bridge.vertex 0) = 1 at equal
        rw [v0] at equal
        exact (by decide : (0:Fin 3) ≠ 1) equal |>.elim
    have last : bridge.vertex 1 = in₁ j.val.2.1 ∧ bridge.vertex 2 = in₂ j.val.2.2 := by
      rcases triangleRows_step_cases (bridge.arcStep 1) with begins | crosses | good
      · have equal := congrArg triangleLayer begins.1
        change triangleLayer (bridge.vertex 1) = 0 at equal
        rw [v1] at equal
        exact (by decide : (1:Fin 3) ≠ 0) equal |>.elim
      · have equal := congrArg triangleLayer crosses.1
        change triangleLayer (bridge.vertex 1) = 0 at equal
        rw [v1] at equal
        exact (by decide : (1:Fin 3) ≠ 0) equal |>.elim
      · exact good
    have river : bridge.vertex 0 = in₀ r.val.1 ∧ bridge.vertex 2 = in₂ r.val.2.2 := by
      rcases triangleRows_step_cases bridge.riverStep with begins | good | ends
      · have equal := congrArg triangleLayer begins.2
        change triangleLayer (bridge.vertex 2) = 1 at equal
        rw [v2] at equal
        exact (by decide : (2:Fin 3) ≠ 1) equal |>.elim
      · exact good
      · have equal := congrArg triangleLayer ends.1
        rw [v0] at equal
        exact (by decide : (0:Fin 3) ≠ 1) equal |>.elim
    have start : r.val.1 = i.val.1 := by
      simpa only [in₀,Sum.inl.injEq] using river.1.symm.trans first.1
    have middle : j.val.2.1 = i.val.2.1 := by
      simpa only [in₁,Sum.inr.injEq,Sum.inl.injEq] using last.1.symm.trans first.2
    have endEq : r.val.2.2 = j.val.2.2 := by
      simpa only [in₂,Sum.inr.injEq] using river.2.symm.trans last.2
    let a := r.val.1
    let b := j.val.2.1
    let c := r.val.2.2
    have isEdge : ∃ c', (a,b,c') ∈ t := ⟨i.val.2.2,by dsimp only [a,b]; rw [start,middle]; exact i.property⟩
    have lastOn : (j.val.1,b,c) ∈ t := by dsimp only [b,c]; rw [endEq]; exact j.property
    have riverOn : (a,r.val.2.1,c) ∈ t := r.property
    have noMixed : (a,b,c) ∉ t := by
      intro on
      have aEq := ExplicitDisjoint.inj₀ on lastOn
      have bEq := ExplicitDisjoint.inj₁ on riverOn
      exact bridge.river_ne_arc 1 (Subtype.ext (Prod.ext aEq (Prod.ext bEq.symm endEq)))
    have weightA : left c a+right c b ≤ 0 := le_of_not_gt (fun pos => noMixed ((positive a b c isEdge).mp pos))
    have weightB : 0 < left c j.val.1+right c b := (positive j.val.1 b c ⟨c,lastOn⟩).mpr lastOn
    have order : r < j := arrives endEq (by rw [← endEq]; exact lt_of_le_of_lt weightA weightB |> lt_of_add_lt_add_right)
    exact (not_lt_of_gt order) earlier

/-- Positive bipartite matching fibers can be listed as length-three
rows with last-arc half-bridge exclusion at every size. The three vertex
roles are tagged, and the arrival order increases with the left weight
within each fiber. -/
theorem exists_halfFree_three_rows_of_positive_matchings (t : Finset (A × B × C)) [ExplicitDisjoint t]
    (left : C → A → ℝ) (right : C → B → ℝ)
    (positive : ∀ a b c, (∃ c', (a,b,c') ∈ t) → (0 < left c a+right c b ↔ (a,b,c) ∈ t)) :
    ∃ enumerate : Fin t.card ≃ t,
      let rows (i : Fin t.card) := tripartiteThreeRow (enumerate i)
      Function.Injective rows ∧ (∀ i, (rows i).Nodup ∧ (rows i).length = 3) ∧
        ∀ cutoff, HalfBridgeFree (Before rows) cutoff := by
  let base := Fintype.equivFinOfCardEq (Fintype.card_coe t)
  let rank (i : t) : ℝ ×ₗ Fin t.card := toLex (left i.val.2.2 i.val.1,base i)
  let : LinearOrder (↥t) := LinearOrder.lift' rank fun i j equal =>
    base.injective (congrArg (fun r => (ofLex r).2) equal)
  have sorts {i j : t} (_ : i.val.2.2 = j.val.2.2)
      (increases : left i.val.2.2 i.val.1 < left j.val.2.2 j.val.1) : i < j :=
    show rank i < rank j from Prod.Lex.toLex_lt_toLex.mpr (Or.inl increases)
  let order := Fintype.orderIsoFinOfCardEq (↥t) (Fintype.card_coe t)
  refine ⟨order.toEquiv,?_,?_,?_⟩
  · intro i j equal
    simp only [tripartiteThreeRow] at equal
    have same : (order i).val = (order j).val := by
      have coords := List.cons.inj equal
      have rest := List.cons.inj coords.2
      exact Prod.ext (Sum.inl.inj coords.1) (Prod.ext (Sum.inl.inj (Sum.inr.inj rest.1))
        (Sum.inr.inj (Sum.inr.inj (List.cons.inj rest.2).1)))
    exact order.injective (Subtype.ext same)
  · intro i
    simp [tripartiteThreeRow,in₀,in₁,in₂]
  · intro cutoff d enough bridge earlier
    apply ordered_positive_triangle_rows_halfFree left right positive (@sorts) cutoff enough
      (bridge.mapPaths order order.injective (fun _ _ _ step => step))
    exact order.strictMono earlier

private noncomputable def matchedRank {t : Finset (A × B × C)} (enumerate : Fin t.card ≃ t)
    (selects : t → Prop) : ℕ := by
  classical
  exact if found : ∃ i, selects (enumerate i) then (Classical.choose found).val+1 else 0

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
private theorem matchedRank_eq {t : Finset (A × B × C)} (enumerate : Fin t.card ≃ t)
    {selects : t → Prop} {i : Fin t.card} (found : selects (enumerate i))
    (unique : ∀ j, selects (enumerate j) → j = i) : matchedRank enumerate selects = i.val+1 := by
  classical
  unfold matchedRank
  split
  · next existsIndex => rw [unique _ (Classical.choose_spec existsIndex)]
  · next absent => exact (absent ⟨i,found⟩).elim

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
private theorem matchedRank_le {t : Finset (A × B × C)} (enumerate : Fin t.card ≃ t)
    (selects : t → Prop) : matchedRank enumerate selects ≤ t.card := by
  classical
  unfold matchedRank
  split
  · next found => exact (Classical.choose found).isLt
  · exact Nat.zero_le _

/-- The arrival order of a half-three-free tripartite family supplies
positive weights for the endpoint matching at each final vertex. -/
theorem positive_matchings_of_halfFree_three_rows {t : Finset (A × B × C)} [ExplicitDisjoint t]
    (enumerate : Fin t.card ≃ t)
    (free : HalfBridgeFree (Before (fun i => tripartiteThreeRow (enumerate i))) 3) :
    ∃ (left : C → A → ℝ) (right : C → B → ℝ),
      ∀ a b c, (∃ c', (a,b,c') ∈ t) → (0 < left c a+right c b ↔ (a,b,c) ∈ t) := by
  classical
  let val (i : Fin t.card) := (enumerate i).val
  have on (i : Fin t.card) : val i ∈ t := (enumerate i).property
  let leftOf (c : C) (a : A) (r : t) := r.val.1 = a ∧ r.val.2.2 = c
  let rightOf (c : C) (b : B) (r : t) := r.val.2.1 = b ∧ r.val.2.2 = c
  let rankL (c : C) (a : A) := matchedRank enumerate (leftOf c a)
  let rankR (c : C) (b : B) := matchedRank enumerate (rightOf c b)
  let left (c : C) (a : A) : ℝ := rankL c a
  let right (c : C) (b : B) : ℝ :=
    if rankR c b = 0 then -(t.card:ℝ)-1 else 1/2-(rankR c b:ℝ)
  have rankL_eq {c a i} (matchL : leftOf c a (enumerate i)) : rankL c a = i.val+1 := by
    apply matchedRank_eq enumerate matchL
    intro j also
    have onI : (a,(val i).2.1,c) ∈ t := by
      rw [← matchL.1,← matchL.2]
      exact on i
    have onJ : (a,(val j).2.1,c) ∈ t := by
      rw [← also.1,← also.2]
      exact on j
    exact enumerate.injective (Subtype.ext (Prod.ext (also.1.trans matchL.1.symm)
      (Prod.ext (ExplicitDisjoint.inj₁ onJ onI) (also.2.trans matchL.2.symm))))
  have rankR_eq {c b i} (matchR : rightOf c b (enumerate i)) : rankR c b = i.val+1 := by
    apply matchedRank_eq enumerate matchR
    intro j also
    have onI : ((val i).1,b,c) ∈ t := by
      rw [← matchR.1,← matchR.2]
      exact on i
    have onJ : ((val j).1,b,c) ∈ t := by
      rw [← also.1,← also.2]
      exact on j
    exact enumerate.injective (Subtype.ext (Prod.ext (ExplicitDisjoint.inj₀ onJ onI)
      (Prod.ext (also.1.trans matchR.1.symm) (also.2.trans matchR.2.symm))))
  refine ⟨left,right,?_⟩
  intro a b c edge
  by_cases matched : (a,b,c) ∈ t
  · let i := enumerate.symm ⟨(a,b,c),matched⟩
    have row : val i = (a,b,c) := congrArg Subtype.val (enumerate.apply_symm_apply ⟨_,matched⟩)
    have matchL : leftOf c a (enumerate i) := by change (val i).1 = a ∧ (val i).2.2 = c; simp [row]
    have matchR : rightOf c b (enumerate i) := by change (val i).2.1 = b ∧ (val i).2.2 = c; simp [row]
    have pos : 0 < left c a+right c b := by
      dsimp only [left,right]
      rw [rankL_eq matchL,rankR_eq matchR,ite_eq_right (Nat.succ_ne_zero _)]
      linarith
    exact iff_of_true pos matched
  apply iff_of_false _ matched
  apply not_lt.mpr
  by_cases hasRight : ∃ j, rightOf c b (enumerate j)
  swap
  · have zero : rankR c b = 0 := by simp [rankR,matchedRank,hasRight]
    have bound : (rankL c a:ℝ) ≤ t.card := by exact_mod_cast matchedRank_le enumerate (leftOf c a)
    dsimp only [left,right]
    rw [ite_eq_left zero]
    linarith only [bound]
  obtain ⟨j,matchR⟩ := hasRight
  have rightWeight : right c b = 1/2-((j.val+1:ℕ):ℝ) := by
    dsimp only [right]
    rw [rankR_eq matchR,ite_eq_right (Nat.succ_ne_zero _)]
  by_cases hasLeft : ∃ r, leftOf c a (enumerate r)
  swap
  · have zero : rankL c a = 0 := by simp [rankL,matchedRank,hasLeft]
    dsimp only [left]
    rw [zero,rightWeight]
    push_cast
    linarith only [Nat.cast_nonneg (α := ℝ) j.val]
  obtain ⟨r,matchL⟩ := hasLeft
  obtain ⟨c',edgeOn⟩ := edge
  let i := enumerate.symm ⟨(a,b,c'),edgeOn⟩
  have row : val i = (a,b,c') := congrArg Subtype.val (enumerate.apply_symm_apply ⟨_,edgeOn⟩)
  have firstAt : (val i).1 = a := congrArg Prod.fst row
  have middleAt : (val i).2.1 = b := congrArg (fun u => u.2.1) row
  have apart : r ≠ j := by
    intro equal
    have mix : val j = (a,b,c) := Prod.ext (equal ▸ matchL.1) (Prod.ext matchR.1 matchR.2)
    exact matched (mix ▸ on j)
  have firstLast : i ≠ j := by
    intro equal
    have mix : val j = (a,b,c) := Prod.ext (equal ▸ firstAt) (Prod.ext matchR.1 matchR.2)
    exact matched (mix ▸ on j)
  have riverFirst : r ≠ i := by
    intro equal
    have mix : val r = (a,b,c) := Prod.ext matchL.1 (Prod.ext (equal.symm ▸ middleAt) matchL.2)
    exact matched (mix ▸ on r)
  let rows (l : Fin t.card) := tripartiteThreeRow (enumerate l)
  have firstStep : Before rows i (in₀ a) (in₁ b) := by
    change Before (fun _ : Fin t.card => [in₀ (val i).1,in₁ (val i).2.1,in₂ (val i).2.2]) i (in₀ a) (in₁ b)
    simp [SourceAudit.BeforeIn,row,in₀,in₁,in₂]
  have lastStep : Before rows j (in₁ b) (in₂ c) := by
    change Before (fun _ : Fin t.card => [in₀ (val j).1,in₁ (val j).2.1,in₂ (val j).2.2]) j (in₁ b) (in₂ c)
    have bAt : (val j).2.1 = b := matchR.1
    have cAt : (val j).2.2 = c := matchR.2
    simp [SourceAudit.BeforeIn,bAt,cAt,in₀,in₁,in₂]
  have riverStep : Before rows r (in₀ a) (in₂ c) := by
    change Before (fun _ : Fin t.card => [in₀ (val r).1,in₁ (val r).2.1,in₂ (val r).2.2]) r (in₀ a) (in₂ c)
    have aAt : (val r).1 = a := matchL.1
    have cAt : (val r).2.2 = c := matchL.2
    simp [SourceAudit.BeforeIn,aAt,cAt,in₀,in₁,in₂]
  let bridge := threeListBridge firstLast riverFirst apart firstStep lastStep riverStep
  have noReverse : ¬ j < r := free (show 1+2 ≤ 3 by decide) bridge
  have earlier : r.val < j.val := (le_of_not_gt noReverse).lt_of_ne apart
  have sep : (r.val:ℝ)+1 ≤ j.val := by exact_mod_cast earlier
  dsimp only [left]
  rw [rankL_eq matchL,rightWeight]
  push_cast
  linarith only [sep]

/-- Taking the first three vertices of every long row in an arbitrary
last-arc half-three-free family gives positive bipartite matching fibers,
with one triple per long row. Roles are tagged when proving the bridge claim. -/
theorem first_three_vertices_positive_matchings {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) :
    ∃ t : Finset (Fin n × Fin n × Fin n), t.card = (univ.filter (fun i => 2 < (paths i).length)).card ∧
      ExplicitDisjoint t ∧ ∃ (left right : Fin n → Fin n → ℝ),
        ∀ a b c, (∃ c', (a,b,c') ∈ t) → (0 < left c a+right c b ↔ (a,b,c) ∈ t) := by
  classical
  let S := univ.filter (fun i : Fin p => 2 < (paths i).length)
  let arrival := Fintype.orderIsoFinOfCardEq (↥S) (Fintype.card_coe S)
  let old (i : Fin S.card) : Fin p := (arrival i).val
  have oldInjective : Function.Injective old := Subtype.val_injective.comp arrival.injective
  have oldMono : StrictMono old := fun _ _ earlier => arrival.strictMono earlier
  have long (i : Fin S.card) : 2 < (paths (old i)).length := (mem_filter.mp (arrival i).property).2
  let v (i : Fin S.card) (j : Fin 3) : Fin n :=
    (paths (old i))[j.val]'(by have := j.isLt; have := long i; omega)
  let tuple (i : Fin S.card) : Fin n × Fin n × Fin n := (v i 0,v i 1,v i 2)
  let t := univ.image tuple
  have step (i : Fin S.card) {a b : Fin 3} (before : a < b) : Before paths (old i) (v i a) (v i b) := by
    refine ⟨List.getElem_mem _,List.getElem_mem _,?_⟩
    dsimp only [v]
    rw [(simple (old i)).idxOf_getElem,(simple (old i)).idxOf_getElem]
    exact before
  have sameRow {i j : Fin S.card} {a b : Fin 3} (before : a < b)
      (x : v i a = v j a) (y : v i b = v j b) : i = j := by
    by_contra different
    exact no_parallel_list_steps free (by omega) (fun equal => different (oldInjective equal))
      (step i before) (x.symm ▸ y.symm ▸ step j before)
  have tupleInjective : Function.Injective tuple := fun i j equal =>
    sameRow (by decide : (0:Fin 3) < 1) (congrArg Prod.fst equal) (congrArg (fun x => x.2.1) equal)
  have count : t.card = S.card := by rw [show t = univ.image tuple from rfl,card_image_of_injective _ tupleInjective]; simp
  let through (i : Fin S.card) : t := ⟨tuple i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩
  have bijective : Function.Bijective through := by
    refine ⟨fun _ _ h => tupleInjective (congrArg Subtype.val h),?_⟩
    intro x
    obtain ⟨i,_,equal⟩ := mem_image.mp x.property
    exact ⟨i,Subtype.ext equal⟩
  let cast := finCongr count
  let enumerate := cast.trans (Equiv.ofBijective through bijective)
  have gives {a b c : Fin n} (on : (a,b,c) ∈ t) : ∃ i, v i 0 = a ∧ v i 1 = b ∧ v i 2 = c := by
    obtain ⟨i,_,equal⟩ := mem_image.mp on
    exact ⟨i,congrArg Prod.fst equal,congrArg (fun x => x.2.1) equal,congrArg (fun x => x.2.2) equal⟩
  let disjoint : ExplicitDisjoint t := by
    constructor
    · intro a b c a' first next
      obtain ⟨i,ai,bi,ci⟩ := gives first
      obtain ⟨j,aj,bj,cj⟩ := gives next
      obtain rfl := sameRow (by decide : (1:Fin 3) < 2) (bi.trans bj.symm) (ci.trans cj.symm)
      exact ai.symm.trans aj
    · intro a b c b' first next
      obtain ⟨i,ai,bi,ci⟩ := gives first
      obtain ⟨j,aj,bj,cj⟩ := gives next
      obtain rfl := sameRow (by decide : (0:Fin 3) < 2) (ai.trans aj.symm) (ci.trans cj.symm)
      exact bi.symm.trans bj
    · intro a b c c' first next
      obtain ⟨i,ai,bi,ci⟩ := gives first
      obtain ⟨j,aj,bj,cj⟩ := gives next
      obtain rfl := sameRow (by decide : (0:Fin 3) < 1) (ai.trans aj.symm) (bi.trans bj.symm)
      exact ci.symm.trans cj
  let rows (i : Fin t.card) := tripartiteThreeRow (enumerate i)
  let erase : Fin n ⊕ Fin n ⊕ Fin n → Fin n
    | in₀ x | in₁ x | in₂ x => x
  let place := old ∘ cast
  have placeInjective : Function.Injective place := oldInjective.comp cast.injective
  have placeMono : StrictMono place := fun _ _ h => oldMono h
  have project {i : Fin t.card} {x y : Fin n ⊕ Fin n ⊕ Fin n} (before : Before rows i x y) :
      Before paths (place i) (erase x) (erase y) := by
    rcases triangleRows_step_cases before with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact step (cast i) (by decide : (0:Fin 3) < 1)
    · exact step (cast i) (by decide : (0:Fin 3) < 2)
    · exact step (cast i) (by decide : (1:Fin 3) < 2)
  have taggedFree : HalfBridgeFree (Before rows) 3 := by
    intro d bound b earlier
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    · exact no_parallel_list_steps free (by omega)
        (fun equal => b.river_ne_arc 0 (placeInjective equal)) (project b.riverStep) (project (b.arcStep 0))
    · let projected := threeListBridge
        (fun equal => (by decide : (0:Fin 2) ≠ 1) (b.distinctArcs (placeInjective equal)))
        (fun equal => b.river_ne_arc 0 (placeInjective equal))
        (fun equal => b.river_ne_arc 1 (placeInjective equal))
        (project (b.arcStep 0)) (project (b.arcStep 1)) (project b.riverStep)
      exact free three projected (placeMono earlier)
  let : ExplicitDisjoint t := disjoint
  exact ⟨t,count,disjoint,positive_matchings_of_halfFree_three_rows enumerate taggedFree⟩

end OnlineReachabilityPreservers
