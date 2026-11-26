import OnlineReachabilityPreservers.IncidenceColorBudgetAudit
import Mathlib.Data.Sum.Order

/-! A common-order half-bridge-free family that exceeds the occupied-support
allowances for coloring all its incidences. -/

namespace OnlineReachabilityPreservers.LayeredIncidenceColorAudit

open Finset IncidenceColorBudgetAudit

local notation "Before" => SourceAudit.BeforeIn

abbrev Side := Fin 2
abbrev Position := Fin 64
abbrev V := Side ×ₗ Position
abbrev Edge := Position ×ₗ Position
abbrev Row := Lex (Edge ⊕ Side)

def point (s : Side) (i : Position) : V := toLex (s, i)
def short (e : Edge) : Row := toLex (Sum.inl e)
def long (s : Side) : Row := toLex (Sum.inr s)
def side (v : V) : Side := (ofLex v).1
def position (v : V) : Position := (ofLex v).2

def paths (r : Row) : List V := (ofLex r).elim
  (fun e => [point 0 (ofLex e).1, point 1 (ofLex e).2])
  (fun s => (List.finRange 64).map (point s))

private theorem cross_ne (a b : Position) : point 0 a ≠ point 1 b := fun eq =>
  (show (0 : Side) ≠ 1 by decide) (congrArg side eq)

theorem paths_simple (r : Row) : (paths r).Nodup := by
  cases label : ofLex r with
  | inl e => simp [paths,label,cross_ne]
  | inr s =>
    rw [paths,label]
    exact (List.nodup_finRange _).map (fun _ _ eq => congrArg position eq)

private theorem short_step {e : Edge} {v w : V} (step : Before paths (short e) v w) :
    v = point 0 (ofLex e).1 ∧ w = point 1 (ofLex e).2 := by
  have first : v = point 0 (ofLex e).1 ∨ v = point 1 (ofLex e).2 := by
    simpa [paths, short] using step.1
  have last : w = point 0 (ofLex e).1 ∨ w = point 1 (ofLex e).2 := by
    simpa [paths, short] using step.2.1
  have different := listBefore_ne step
  rcases first with rfl | rfl <;> rcases last with rfl | rfl
  · exact (different rfl).elim
  · exact ⟨rfl,rfl⟩
  · have order := step.2.2
    simp [paths,short, List.idxOf_cons] at order
  · exact (different rfl).elim

private theorem long_coords (s : Side) : (paths (long s)).map position = List.finRange 64 := by
  simp [paths,long, List.map_map, Function.comp_def, position, point]

private theorem long_step {s : Side} {v w : V} (step : Before paths (long s) v w) :
    side v = s ∧ side w = s ∧ position v < position w := by
  have first (v : V) (onRow : v ∈ paths (long s)) : side v = s := by
    have member : v ∈ (List.finRange 64).map (point s) := onRow
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
    rfl
  have nodup : ((paths (long s)).map position).Nodup := by
    rw [long_coords]
    exact List.nodup_finRange _
  have projected := (listBefore_map position nodup step).2.2
  change ((paths (long s)).map position).idxOf (position v) < ((paths (long s)).map position).idxOf (position w) at projected
  rw [long_coords] at projected
  exact ⟨first v step.1,first w step.2.1,by simpa using projected⟩

/-- All paths respect the common lexicographic order of the two vertex layers. -/
theorem step_increases {r : Row} {v w : V} (step : Before paths r v w) : v < w := by
  cases label : ofLex r with
  | inl e =>
    have eq : r = short e := ofLex.injective label
    obtain ⟨a,b⟩ := short_step (eq ▸ step)
    rw [a,b]
    exact Prod.Lex.lt_iff.mpr (Or.inl (by decide : (0 : Side) < 1))
  | inr s =>
    have eq : r = long s := ofLex.injective label
    obtain ⟨a,b,pos⟩ := long_step (eq ▸ step)
    exact Prod.Lex.lt_iff.mpr (Or.inr ⟨a.trans b.symm,pos⟩)

private theorem side_monotone : Monotone side := by
  intro a b order
  rcases Prod.Lex.le_iff.mp order with small | ⟨same, _⟩
  · exact small.le
  · exact same.le

/-- These rows exclude half-bridges through every cutoff. The cross rows
arrive by source position, before both rows within the two sides. -/
theorem paths_half_all (k : ℕ) : HalfBridgeFree (Before paths) k := by
  intro s _ b early
  have mono : StrictMono b.vertex := Fin.strictMono_iff_lt_succ.mpr fun i => step_increases (b.arcStep i)
  cases river : ofLex b.river with
  | inr a =>
    have riverEq : b.river = long a := ofLex.injective river
    obtain ⟨initial,terminal,_⟩ := long_step (riverEq ▸ b.riverStep)
    have lower := side_monotone (mono.monotone (Fin.zero_le (1 : Fin (s+2))))
    have upper := side_monotone (mono.monotone (Fin.le_last (1 : Fin (s+2))))
    rw [initial] at lower
    rw [terminal] at upper
    have second : side (b.vertex 1) = a := upper.antisymm lower
    have first : Before paths (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
    cases arc : ofLex (b.arc 0) with
    | inl e =>
      have arcEq : b.arc 0 = short e := ofLex.injective arc
      obtain ⟨x,y⟩ := short_step (arcEq ▸ first)
      have impossible : (0 : Side) = 1 := (congrArg side x).symm.trans (initial.trans (second.symm.trans (congrArg side y)))
      exact (by decide : (0 : Side) ≠ 1) impossible
    | inr c =>
      have arcEq : b.arc 0 = long c := ofLex.injective arc
      have same : a = c := initial.symm.trans (long_step (arcEq ▸ first)).1
      exact b.river_ne_arc 0 (riverEq.trans ((congrArg long same).trans arcEq.symm))
  | inl e =>
    have riverEq : b.river = short e := ofLex.injective river
    have ends := short_step (riverEq ▸ b.riverStep)
    cases last : ofLex (b.arc (Fin.last s)) with
    | inr a =>
      have lastEq : b.arc (Fin.last s) = long a := ofLex.injective last
      rw [lastEq,riverEq] at early
      exact (Sum.Lex.inl_lt_inr e a).asymm early
    | inl f =>
      have lastEq : b.arc (Fin.last s) = short f := ofLex.injective last
      have final := short_step (lastEq ▸ b.arcStep (Fin.last s))
      have order := mono.monotone (Fin.zero_le (Fin.last s).castSucc)
      rw [ends.1,final.1] at order
      have source : (ofLex e).1 ≤ (ofLex f).1 := by
        rcases Prod.Lex.le_iff.mp order with absurd | ⟨_,pos⟩
        · exact False.elim ((lt_irrefl (0 : Side)) absurd)
        · exact pos
      have target : (ofLex e).2 = (ofLex f).2 := congrArg position (ends.2.symm.trans final.2)
      have rowOrder : e ≤ f := by
        rcases lt_or_eq_of_le source with small | same
        · exact Prod.Lex.le_iff.mpr (Or.inl small)
        · exact Prod.Lex.le_iff.mpr (Or.inr ⟨same,target.le⟩)
      rw [lastEq,riverEq] at early
      exact (not_lt_of_ge (Sum.Lex.inl_le_inl_iff.mpr rowOrder)) early

theorem vertexCount : Fintype.card V = 128 := by simp [Fintype.card_lex, Fintype.card_prod]

theorem rowCount : Fintype.card Row = 4098 := by simp [Fintype.card_lex, Fintype.card_sum, Fintype.card_prod]

theorem totalMass : (∑ r, (paths r).length) = 8320 := by
  rw [← Equiv.sum_comp (toLex : (Edge ⊕ Side) ≃ Row), Fintype.sum_sum_type]
  simp [paths, Fintype.card_lex, Fintype.card_prod]

private def pointEmbed (s : Side) : Position ↪ V := ⟨point s,fun _ _ eq => congrArg position eq⟩

private theorem prod_of_small_sum {a b : ℕ} (cap : a + b ≤ 60) : a * b ≤ 15 * (a + b) := by
  have root : 4 * (a * b) ≤ (a + b)*(a + b) := by
    exact_mod_cast (show (4:ℤ)*((a:ℤ)*(b:ℤ)) ≤ ((a:ℤ)+(b:ℤ))*((a:ℤ)+(b:ℤ)) by
      nlinarith [sq_nonneg ((a:ℤ)-(b:ℤ))])
  have bound := Nat.mul_le_mul_left (a + b) cap
  omega

variable {C : Type*} [LinearOrder C] [Fintype C]

set_option maxRecDepth 30000 in
/-- The two layers also obstruct coloring all the incidences within the
original upper length cap and both support allowances. -/
theorem colors_exceed_some_budget (color : Row → V → C)
    (vertices : 3 * (activeListVertices (partitionListIncidencesByColor paths color)).card ≤ 4 * 128)
    (families : 3 * (activeListIndices (partitionListIncidencesByColor paths color)).card ≤ 4 * 4098)
    (width : ∀ i, (partitionListIncidencesByColor paths color i).length ≤ 8) : False := by
  let pieces := partitionListIncidencesByColor paths color
  let support := activeListVertices pieces
  let baseColor (v : V) := color (long (side v)) v
  let all := colorClassSupport support
  have copied (r : Row) (v : V) (h : v ∈ paths r) : toLex (v,color r v) ∈ support :=
    occupiedColorCopy_mem paths color r v h
  have basePresent (v : V) : toLex (v,baseColor v) ∈ support := by
    apply copied (long (side v)) v
    change v ∈ (List.finRange 64).map (point (side v))
    exact List.mem_map.mpr ⟨position v, by simp, ofLex.injective (Prod.ext rfl rfl)⟩
  have baseCount (c : C) : ((univ : Finset V).filter fun v => baseColor v = c).card ≤ 16 := by
    let base := (univ : Finset V).filter fun v => baseColor v = c
    let block (s : Side) := (univ : Finset Position).filter fun i => color (long s) (point s i) = c
    have bound (s : Side) : (block s).card ≤ 8 := by
      have length : (block s).card = (pieces (toLex (long s, c))).length := by
        change (block s).card = ((((List.finRange 64).map (point s)).filter
          fun v => decide (color (long s) v = c)).map (fun v => toLex (v, c))).length
        rw [List.length_map, List.filter_map, List.length_map,
          ← List.toFinset_card_of_nodup (List.filter_sublist.nodup (List.nodup_finRange _))]
        congr 1
        ext i
        simp [block]
      exact length.trans_le (width _)
    rw [card_eq_sum_card_fiberwise (f := side) (t := (univ : Finset Side)) (by simp)]
    have equal (s : Side) : base.filter (fun v => side v = s) = (block s).map (pointEmbed s) := by
      ext v
      simp only [base,block,mem_filter,mem_univ,true_and,mem_map]
      constructor
      · rintro ⟨tag,inSide⟩
        have eq : point s (position v) = v := ofLex.injective (Prod.ext inSide.symm rfl)
        exact ⟨position v,by rw [eq,← inSide]; exact tag,eq⟩
      · rintro ⟨i,tag,rfl⟩
        exact ⟨tag,rfl⟩
    change (∑ s, (base.filter fun v => side v = s).card) ≤ 16
    simp only [equal,card_map]
    calc
      _ ≤ ∑ _ : Side, 8 := sum_le_sum fun s _ => bound s
      _ = 16 := by simp
  have supportBudget : support.card ≤ 170 := by
    change 3 * support.card ≤ 4 * 128 at vertices
    omega
  obtain ⟨allCount,each⟩ := colorClassSupport_bounds support baseColor (extras := 42)
    basePresent baseCount (by rw [vertexCount]; exact supportBudget)
  let paint (e : Edge) := color (short e) (point 0 (ofLex e).1)
  let mono := (univ : Finset Edge).filter fun e => paint e = color (short e) (point 1 (ofLex e).2)
  have monoBound : mono.card ≤ 2550 := by
    have localBound (c : C) : (mono.filter fun e => paint e = c).card ≤ 15 * (all c).card := by
      let left := (univ : Finset Position).filter fun i => point 0 i ∈ all c
      let right := (univ : Finset Position).filter fun i => point 1 i ∈ all c
      have disjoint : Disjoint (left.map (pointEmbed 0)) (right.map (pointEmbed 1)) := by
        rw [disjoint_left]
        intro v a b
        obtain ⟨i,_,eq⟩ := mem_map.mp a
        obtain ⟨j,_,eq'⟩ := mem_map.mp b
        exact cross_ne i j (eq.trans eq'.symm)
      have subset : left.map (pointEmbed 0) ∪ right.map (pointEmbed 1) ⊆ all c := by
        intro v h
        rcases mem_union.mp h with a | b
        · obtain ⟨i,onLeft,rfl⟩ := mem_map.mp a
          exact (mem_filter.mp onLeft).2
        · obtain ⟨i,onRight,rfl⟩ := mem_map.mp b
          exact (mem_filter.mp onRight).2
      have sumCap := card_le_card subset
      rw [card_union_of_disjoint disjoint,card_map,card_map] at sumCap
      have inject := card_le_card_of_injOn (fun e : Edge => ofLex e)
        (s := mono.filter fun e => paint e = c) (t := left ×ˢ right) (by
          intro e member
          obtain ⟨matched,assigned⟩ := mem_filter.mp member
          have common := (mem_filter.mp matched).2
          have x : point 0 (ofLex e).1 ∈ all c := mem_filter.mpr ⟨mem_univ _,
            assigned ▸ copied (short e) (point 0 (ofLex e).1) (by simp [paths, short])⟩
          have y : point 1 (ofLex e).2 ∈ all c := mem_filter.mpr ⟨mem_univ _,
            (common.symm.trans assigned) ▸ copied (short e) (point 1 (ofLex e).2) (by simp [paths, short])⟩
          exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,x⟩,mem_filter.mpr ⟨mem_univ _,y⟩⟩)
        (fun _ _ _ _ eq => ofLex.injective eq)
      rw [card_product] at inject
      have bound : left.card + right.card ≤ 60 := sumCap.trans ((each c).trans (by decide))
      exact inject.trans ((prod_of_small_sum bound).trans (Nat.mul_le_mul_left _ sumCap))
    rw [card_eq_sum_card_fiberwise (f := paint) (t := (univ : Finset C)) (by simp)]
    have total : (∑ c, (mono.filter fun e => paint e = c).card) ≤ 15*support.card := by
      rw [← allCount,mul_sum]
      exact sum_le_sum fun c _ => localBound c
    omega
  have shortCount (e : Edge) : ((paths (short e)).toFinset.image (color (short e))).card =
      if e ∈ mono then 1 else 2 := by
    rw [show paths (short e) = [point 0 (ofLex e).1, point 1 (ofLex e).2] from rfl]
    by_cases same : paint e = color (short e) (point 1 (ofLex e).2)
    · simp [mono,paint,same.symm]
    · simp [mono,paint,same]
  have sameColor : (∑ e : Edge, if e ∈ mono then 1 else 0) = mono.card := by
    rw [← card_filter]
    congr 1
    ext e
    simp
  have shortTotal : (∑ e : Edge, ((paths (short e)).toFinset.image (color (short e))).card) + mono.card = 8192 := by
    rw [← sameColor,← sum_add_distrib]
    calc
      _ = ∑ _ : Edge, 2 := by
        apply sum_congr rfl
        intro e _
        rw [shortCount]
        by_cases found : e ∈ mono <;> simp [found]
      _ = 8192 := by simp
  rw [incidenceColors_activeIndices_card, ← Equiv.sum_comp (toLex : (Edge ⊕ Side) ≃ Row), Fintype.sum_sum_type] at families
  change 3 * ((∑ e : Edge, ((paths (short e)).toFinset.image (color (short e))).card) + _) ≤ 4 * 4098 at families
  omega

/-- For this family, the support requirements fail at the cap determined
by the original mass and path budget. -/
theorem original_width_exceeds_some_budget (color : Row → V → C)
    (vertices : 3 * (activeListVertices (partitionListIncidencesByColor paths color)).card ≤ 4 * Fintype.card V)
    (families : 3 * (activeListIndices (partitionListIncidencesByColor paths color)).card ≤ 4 * Fintype.card Row)
    (width : ∀ i, (partitionListIncidencesByColor paths color i).length ≤
      4 * (∑ r, (paths r).length) / Fintype.card Row) : False := by
  apply colors_exceed_some_budget color (by simpa only [vertexCount] using vertices)
    (by simpa only [rowCount] using families)
  intro i
  rw [totalMass,rowCount] at width
  exact width i

/-- The frozen-average existential conclusion holds for these budgets and this
mass, with a different family excluding full bridges through any cutoff. -/
theorem original_budget_witness (k : ℕ) :
    ∃ n' ≤ 128, ∃ p' ≤ 4098, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      8320 ≤ 8 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 8320 ∧
      frozenListCaps 128 4098 8320 clean :=
  full_frozen_cleaning_sparse_four (by decide) (by decide) (by decide) (by decide) (by decide)

end OnlineReachabilityPreservers.LayeredIncidenceColorAudit
