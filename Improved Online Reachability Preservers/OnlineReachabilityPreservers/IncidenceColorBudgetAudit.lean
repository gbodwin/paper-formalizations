import OnlineReachabilityPreservers.IncidenceColorCleaning

/-! A full-two path family beyond the support bounds for incidence coloring. -/

namespace OnlineReachabilityPreservers.IncidenceColorBudgetAudit

open Finset

local notation "Before" => SourceAudit.BeforeIn

abbrev V := Fin 64
def pairs : Finset (V ×ₗ V) := univ.filter fun e => (ofLex e).1 < (ofLex e).2
abbrev Pair := ↑pairs
abbrev Row := WithBot Pair

local instance : Fintype Row := inferInstanceAs (Fintype (Option Pair))

private def lo (e : Pair) : V := (ofLex e.val).1
private def hi (e : Pair) : V := (ofLex e.val).2

set_option maxRecDepth 30000 in
private theorem lo_lt_hi (e : Pair) : lo e < hi e := by
  have inside := e.property
  change e.val ∈ (univ : Finset (V ×ₗ V)).filter (fun e => (ofLex e).1 < (ofLex e).2) at inside
  exact (mem_filter.mp inside).2

/-- One ascending path on all vertices, and every two-vertex path in the
opposite direction. -/
def paths : Row → List V
  | none => List.finRange 64
  | some e => [hi e, lo e]

theorem paths_simple (i : Row) : (paths i).Nodup := by
  cases i with
  | none => exact List.nodup_finRange _
  | some e => simp [paths, (lo_lt_hi e).ne']

private theorem pairCount : Fintype.card Pair = 2016 := by
  have projected : pairs.map (ofLex : (V ×ₗ V) ≃ V × V).toEmbedding =
      ((univ : Finset V) ×ˢ univ).filter (fun e => e.1 < e.2) := by
    ext e
    simp only [mem_map, pairs, mem_filter, mem_univ, true_and, Equiv.toEmbedding_apply,
      mem_product, and_true]
    constructor
    · rintro ⟨r,ordered,rfl⟩
      exact ordered
    · intro ordered
      exact ⟨toLex e,ordered,rfl⟩
  rw [Fintype.card_coe, ← card_map (ofLex : (V ×ₗ V) ≃ V × V).toEmbedding,
    projected, card_product_filter_lt, card_univ, Fintype.card_fin]
  decide

private theorem pairs_card : pairs.card = 2016 := by
  simpa only [Fintype.card_coe] using pairCount

theorem rowCount : Fintype.card Row = 2017 := by
  change Fintype.card (Option Pair) = 2017
  rw [Fintype.card_option, pairCount]

theorem totalMass : (∑ i, (paths i).length) = 4096 := by
  change (∑ i : Option Pair, (paths i).length) = 4096
  rw [Fintype.sum_option]
  simp [paths, pairs_card]

private theorem pair_step {e : Pair} {x y : V} (step : Before paths (some e) x y) :
    x = hi e ∧ y = lo e := by
  have insideX : x = hi e ∨ x = lo e := by simpa [paths] using step.1
  have insideY : y = hi e ∨ y = lo e := by simpa [paths] using step.2.1
  have different := listBefore_ne step
  rcases insideX with rfl | rfl <;> rcases insideY with rfl | rfl
  · exact (different rfl).elim
  · exact ⟨rfl,rfl⟩
  · have order := step.2.2
    simp [paths, List.idxOf_cons] at order
  · exact (different rfl).elim

private theorem original_direction {x y : V} (step : Before paths none x y) : x < y := by
  simpa [paths] using step.2.2

theorem paths_full_two : BridgeFree (Before paths) 2 := by
  intro s within
  have zero : s = 0 := by omega
  subst s
  refine ⟨fun b => ?_⟩
  have x : Before paths b.river (b.vertex 0) (b.vertex 1) := b.riverStep
  have y : Before paths (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
  cases river : b.river <;> cases arc : b.arc 0
  · exact b.river_ne_arc 0 (river.trans arc.symm)
  · rename_i e
    obtain ⟨startEq,endEq⟩ := pair_step (arc ▸ y)
    have increasing := original_direction (river ▸ x)
    rw [startEq,endEq] at increasing
    exact increasing.asymm (lo_lt_hi e)
  · rename_i e
    obtain ⟨startEq,endEq⟩ := pair_step (river ▸ x)
    have increasing := original_direction (arc ▸ y)
    rw [startEq,endEq] at increasing
    exact increasing.asymm (lo_lt_hi e)
  · rename_i e f
    obtain ⟨first,second⟩ := pair_step (river ▸ x)
    obtain ⟨first',second'⟩ := pair_step (arc ▸ y)
    have same : e = f := Subtype.ext (ofLex.injective (Prod.ext
      (second.symm.trans second') (first.symm.trans first')))
    exact b.river_ne_arc 0 (river.trans ((congrArg some same).trans arc.symm))

variable {C : Type*} [LinearOrder C] [Fintype C]

set_option maxRecDepth 30000 in
/-- This fixed half-two family cannot satisfy the support and length
conditions of the incidence-color method. -/
theorem colors_exceed_some_budget (color : Row → V → C)
    (vertices : 3 * (activeListVertices (partitionListIncidencesByColor paths color)).card ≤ 4 * 64)
    (families : 3 * (activeListIndices (partitionListIncidencesByColor paths color)).card ≤ 4 * 2017)
    (width : ∀ i, (partitionListIncidencesByColor paths color i).length ≤ 8) : False := by
  let pieces := partitionListIncidencesByColor paths color
  let support := activeListVertices pieces
  let base (c : C) := (univ : Finset V).filter fun v => color none v = c
  let all (c : C) := (univ : Finset V).filter fun v => toLex (v,c) ∈ support
  let tag (w : V ×ₗ C) := (ofLex w).2
  have copyMem (r : Row) (v : V) (mem : v ∈ paths r) : toLex (v,color r v) ∈ support :=
    mem_biUnion.mpr ⟨toLex (r,color r v),mem_univ _,List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨v,List.mem_filter.mpr ⟨mem,decide_eq_true rfl⟩,rfl⟩)⟩
  have includes (c : C) : base c ⊆ all c := by
    intro v h
    have tagged := (mem_filter.mp h).2
    exact mem_filter.mpr ⟨mem_univ _,tagged ▸ copyMem none v (by simp [paths])⟩
  have baseCount (c : C) : (base c).card ≤ 8 := by
    have exactRow : (base c).card = (pieces (toLex (none,c))).length := by
      change (base c).card = (((List.finRange 64).filter fun v => decide (color none v = c)).map _).length
      rw [List.length_map, ← List.toFinset_card_of_nodup (List.filter_sublist.nodup (List.nodup_finRange _))]
      congr 1
      ext v
      simp [base]
    exact exactRow.trans_le (width (toLex (none,c)))
  have exactBase : (∑ c, (base c).card) = 64 := by
    unfold base
    rw [← card_eq_sum_card_fiberwise (f := color none) (t := (univ : Finset C)) (by simp),card_univ,Fintype.card_fin]
  have exactAll : (∑ c, (all c).card) = support.card := by
    rw [card_eq_sum_card_fiberwise (f := tag) (t := (univ : Finset C)) (by simp)]
    apply sum_congr rfl
    intro c _
    let embed : V ↪ (V ×ₗ C) := ⟨fun v => toLex (v,c),fun _ _ eq => congrArg (fun w => (ofLex w).1) eq⟩
    rw [← card_map embed]
    congr 1
    ext w
    simp only [all, mem_map, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨v,member,rfl⟩
      exact ⟨member,rfl⟩
    · rintro ⟨member,selected⟩
      have equal : embed (ofLex w).1 = w := ofLex.injective (Prod.ext rfl selected.symm)
      exact ⟨(ofLex w).1, equal ▸ member, equal⟩
  let extra (c : C) := (all c).card - (base c).card
  have extraTotal : (∑ c, extra c) + 64 = support.card := by
    rw [← exactBase,← sum_add_distrib,← exactAll]
    exact sum_congr rfl (fun c _ => Nat.sub_add_cancel (card_le_card (includes c)))
  have supportBudget : support.card ≤ 85 := by
    change 3*support.card ≤ 4*64 at vertices
    omega
  have size (c : C) : (all c).card ≤ 29 := by
    have h := single_le_sum (f := extra) (fun _ _ => Nat.zero_le _) (mem_univ c)
    have hc := Nat.sub_add_cancel (card_le_card (includes c))
    have baseCap := baseCount c
    change extra c + (base c).card = (all c).card at hc
    omega
  let paint (e : Pair) := color (some e) (lo e)
  let mono := (univ : Finset Pair).filter fun e => paint e = color (some e) (hi e)
  have countMono : mono.card ≤ 1190 := by
    have localBound (c : C) : (mono.filter fun e => paint e = c).card ≤ 14 * (all c).card := by
      have inject := card_le_card_of_injOn (f := fun e : Pair => ofLex e.val)
        (s := mono.filter fun e => paint e = c)
        (t := ((all c) ×ˢ all c).filter fun e => e.1 < e.2) (by
          intro e member
          obtain ⟨monoEdge,selected⟩ := mem_filter.mp member
          have aligned := (mem_filter.mp monoEdge).2
          have src : lo e ∈ all c :=
            mem_filter.mpr ⟨mem_univ _,selected ▸ copyMem (some e) (lo e) (by simp [paths])⟩
          have target : hi e ∈ all c := mem_filter.mpr ⟨mem_univ _,
            (aligned.symm.trans selected) ▸ copyMem (some e) (hi e) (by simp [paths])⟩
          exact mem_filter.mpr ⟨mem_product.mpr ⟨src,target⟩,lo_lt_hi e⟩)
        (fun e _ f _ eq => Subtype.ext (ofLex.injective eq))
      rw [card_product_filter_lt] at inject
      have choose := square_choose (all c).card
      rw [pow_two] at choose
      have square := Nat.mul_le_mul_left (all c).card (size c)
      omega
    rw [card_eq_sum_card_fiberwise (f := paint) (t := (univ : Finset C)) (by simp)]
    have bound : (∑ c, (mono.filter fun e => paint e = c).card) ≤ 14 * support.card := by
      rw [← exactAll,mul_sum]
      exact sum_le_sum fun c _ => localBound c
    omega
  have shortCount (e : Pair) : ((paths (some e)).toFinset.image (color (some e))).card =
      if e ∈ mono then 1 else 2 := by
    by_cases same : paint e = color (some e) (hi e)
    · simp [paths,mono,paint, same.symm]
    · simp [paths,mono,paint, same, Ne.symm same]
  have singleColor : (∑ e : Pair, if e ∈ mono then 1 else 0) = mono.card := by
    rw [← card_filter]
    congr 1
    ext e
    simp
  have shortTotal : (∑ e : Pair, ((paths (some e)).toFinset.image (color (some e))).card) + mono.card = 4032 := by
    rw [← singleColor, ← sum_add_distrib]
    calc
      _ = ∑ _ : Pair, 2 := by
        apply sum_congr rfl
        intro e _
        rw [shortCount]
        by_cases found : e ∈ mono <;> simp [found]
      _ = 4032 := by simp [pairs_card]
  rw [incidenceColors_activeIndices_card] at families
  change 3 * (∑ i : Option Pair, ((paths i).toFinset.image (color i)).card) ≤ 4 * 2017 at families
  rw [Fintype.sum_option] at families
  omega

/-- The support bounds fail at the length cap computed from the actual
incidence mass and row count of the full-two family. -/
theorem original_width_exceeds_some_budget (color : Row → V → C)
    (vertices : 3 * (activeListVertices (partitionListIncidencesByColor paths color)).card ≤ 4 * Fintype.card V)
    (families : 3 * (activeListIndices (partitionListIncidencesByColor paths color)).card ≤ 4 * Fintype.card Row)
    (width : ∀ i, (partitionListIncidencesByColor paths color i).length ≤
      4 * (∑ r, (paths r).length) / Fintype.card Row) : False := by
  apply colors_exceed_some_budget color (by simpa [Fintype.card_fin] using vertices) (by simpa only [rowCount] using families)
  intro i
  rw [totalMass, rowCount] at width
  exact width i

/-- This system's original dimensions and incidence mass admit a frozen
witness, including through the given cutoff of two. -/
theorem original_budget_witness (k : ℕ) :
    ∃ n' ≤ 64, ∃ p' ≤ 2017, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      4096 ≤ 8 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 4096 ∧
      frozenListCaps 64 2017 4096 clean :=
  full_frozen_cleaning_sparse_four (by decide) (by decide) (by decide) (by decide) (by decide)


end OnlineReachabilityPreservers.IncidenceColorBudgetAudit
