import OnlineReachabilityPreservers.HalfFourLiteralCapacity

/-! A terminal reciprocal pair extends the increasing pairs at every half cutoff. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Prod.Lex
local notation "Before" => SourceAudit.BeforeIn

private def highest (m : ℕ) : Fin (m+2) := Fin.last (m+1)
private def nextHighest (m : ℕ) : Fin (m+2) := (Fin.last m).castSucc

private theorem final_vertices_distinct (m : ℕ) : highest m ≠ nextHighest m := by
  intro eq
  have vals := congrArg Fin.val eq
  change m+1 = m at vals
  omega

private def increasingOrSingle (m : ℕ) : Finset (Fin (m+2) ×ₗ Fin (m+2)) :=
  univ.filter fun e => (ofLex e).1 ≤ (ofLex e).2

private def terminalPairLabels (m : ℕ) : Finset (Fin (m+2) ×ₗ Fin (m+2)) :=
  insert (toLex (highest m,nextHighest m)) (increasingOrSingle m)

abbrev TerminalPairLabel (m : ℕ) := ↑(terminalPairLabels m)

private theorem terminalPairLabel_shape {m : ℕ} (i : TerminalPairLabel m) :
    (ofLex i.val).1 ≤ (ofLex i.val).2 ∨
      ((ofLex i.val).1 = highest m ∧ (ofLex i.val).2 = nextHighest m) := by
  rcases mem_insert.mp i.property with reverse | forward
  · right
    exact Prod.mk.inj (congrArg ofLex reverse)
  · exact Or.inl (mem_filter.mp forward).2

/-- The diagonal labels give singletons. Off the diagonal each pair is
increasing except for the reverse of the pair of top vertices. -/
def terminalPairRows (m : ℕ) (i : TerminalPairLabel m) : List (Fin (m+2)) :=
  let e := ofLex i.val
  if e.1 = e.2 then [e.1] else [e.1,e.2]

theorem terminalPairRows_valid {m : ℕ} (i : TerminalPairLabel m) :
    terminalPairRows m i ≠ [] ∧ (terminalPairRows m i).Nodup := by
  by_cases same : (ofLex i.val).1 = (ofLex i.val).2 <;> simp [terminalPairRows,same]

theorem terminalPairRows_injective (m : ℕ) : Function.Injective (terminalPairRows m) := by
  intro a b same
  have equal : (ofLex a.val).1 = (ofLex b.val).1 ∧ (ofLex a.val).2 = (ofLex b.val).2 := by
    by_cases left : (ofLex a.val).1 = (ofLex a.val).2
    · by_cases right : (ofLex b.val).1 = (ofLex b.val).2
      · have head : (ofLex a.val).1 = (ofLex b.val).1 := by
          simpa [terminalPairRows,left,right] using same
        exact ⟨head,left.symm.trans (head.trans right)⟩
      · simp [terminalPairRows,left,right] at same
    · by_cases right : (ofLex b.val).1 = (ofLex b.val).2
      · simp [terminalPairRows,left,right] at same
      · simpa [terminalPairRows,left,right] using same
  exact Subtype.ext (ofLex.injective (Prod.ext equal.1 equal.2))

private theorem terminalPairRows_step {m : ℕ} {i : TerminalPairLabel m} {x y : Fin (m+2)}
    (step : Before (terminalPairRows m) i x y) :
    x = (ofLex i.val).1 ∧ y = (ofLex i.val).2 ∧
      (x < y ∨ x = highest m ∧ y = nextHighest m) := by
  have different : (ofLex i.val).1 ≠ (ofLex i.val).2 := by
    intro same
    have singleton : terminalPairRows m i = [(ofLex i.val).1] := by simp [terminalPairRows,same]
    have start : x = (ofLex i.val).1 := by simpa [singleton] using step.1
    have finish : y = (ofLex i.val).1 := by simpa [singleton] using step.2.1
    exact listBefore_ne step (start.trans finish.symm)
  let u := (ofLex i.val).1
  let v := (ofLex i.val).2
  have pair : terminalPairRows m i = [u,v] := by simp [terminalPairRows,u,v,different]
  have start : x = u ∨ x = v := by simpa [pair] using step.1
  have finish : y = u ∨ y = v := by simpa [pair] using step.2.1
  have shape : u < v ∨ u = highest m ∧ v = nextHighest m :=
    (terminalPairLabel_shape i).imp (fun le => lt_of_le_of_ne le different) id
  rcases start with rfl | rfl <;> rcases finish with rfl | rfl
  · exact (listBefore_ne step rfl).elim
  · exact ⟨rfl,rfl,shape⟩
  · have order := step.2.2
    rw [pair] at order
    simp [u,v] at order
  · exact (listBefore_ne step rfl).elim

private def terminalPairRank {m : ℕ} (x : Fin (m+2)) : ℕ := min x.val m

private theorem terminalPairRows_rank {m : ℕ} {i : TerminalPairLabel m} {x y : Fin (m+2)}
    (step : Before (terminalPairRows m) i x y) :
    terminalPairRank x ≤ terminalPairRank y ∧ (x.val < m → terminalPairRank x < terminalPairRank y) := by
  obtain ⟨_,_,inc | ⟨rfl,rfl⟩⟩ := terminalPairRows_step step
  · change x.val < y.val at inc
    constructor
    · exact min_le_min_right m inc.le
    · intro low
      unfold terminalPairRank
      rw [min_eq_left low.le]
      exact lt_min inc low
  · change min (m+1) m ≤ min m m ∧ (m+1 < m → min (m+1) m < min m m)
    simp

/-- Pair labels arrive in their lexicographic order. Every step weakly
increases the rank that identifies the two highest vertices. A detour
with at least two steps either increases the source rank or repeats
one of the two highest vertices. -/
theorem terminalPairRows_halfFree (m k : ℕ) :
    HalfBridgeFree (Before (terminalPairRows m)) k := by
  intro d _ b earlier
  have river := terminalPairRows_step b.riverStep
  cases d with
  | zero =>
    have arc := terminalPairRows_step (b.arcStep 0)
    apply b.river_ne_arc 0
    apply Subtype.ext
    apply ofLex.injective
    exact Prod.ext (river.1.symm.trans arc.1) (river.2.1.symm.trans arc.2.1)
  | succ d =>
    have along : Monotone (fun j => terminalPairRank (b.vertex j)) :=
      Fin.monotone_iff_le_succ.mpr (fun j => (terminalPairRows_rank (b.arcStep j)).1)
    let last := Fin.last (d+1)
    by_cases low : (b.vertex 0).val < m
    · have one := (terminalPairRows_rank (b.arcStep 0)).2 low
      have after : (1 : Fin (d+3)) ≤ last.castSucc := by
        change 1 ≤ d+1
        omega
      have higher : terminalPairRank (b.vertex 0) < terminalPairRank (b.vertex last.castSucc) :=
        one.trans_le (along after)
      have firstSource := (terminalPairRows_step (b.arcStep last)).1
      have sourceLt : b.vertex 0 < b.vertex last.castSucc := by
        apply lt_of_not_ge
        intro wrong
        exact not_lt_of_ge (min_le_min_right m wrong) higher
      have arrival : b.river < b.arc last := by
        change (b.river).val < (b.arc last).val
        apply Prod.Lex.lt_iff.mpr
        exact Or.inl (river.1 ▸ firstSource ▸ sourceLt)
      exact earlier.asymm arrival
    · have top (j : Fin (d+3)) : m ≤ (b.vertex j).val := by
        have ranks := along (Fin.zero_le j)
        change min (b.vertex 0).val m ≤ min (b.vertex j).val m at ranks
        rw [min_eq_right (by omega : m ≤ (b.vertex 0).val)] at ranks
        exact ranks.trans (min_le_left _ _)
      let one : Fin (d+3) := ⟨1,by omega⟩
      let two : Fin (d+3) := ⟨2,by omega⟩
      have a01 : (b.vertex 0).val ≠ (b.vertex one).val := fun eq => by
        have indices := b.distinctVertices (Fin.ext eq)
        have vals := congrArg Fin.val indices
        change 0 = 1 at vals
        omega
      have a02 : (b.vertex 0).val ≠ (b.vertex two).val := fun eq => by
        have indices := b.distinctVertices (Fin.ext eq)
        have vals := congrArg Fin.val indices
        change 0 = 2 at vals
        omega
      have a12 : (b.vertex one).val ≠ (b.vertex two).val := fun eq => by
        have indices := b.distinctVertices (Fin.ext eq)
        have vals := congrArg Fin.val indices
        change 1 = 2 at vals
        omega
      have hi0 := (b.vertex 0).isLt
      have hi1 := (b.vertex one).isLt
      have hi2 := (b.vertex two).isLt
      have lo0 := top 0
      have lo1 := top one
      have lo2 := top two
      omega

theorem terminalPairLabel_card (m : ℕ) :
    Fintype.card (TerminalPairLabel m) = (m+2)+(m+2).choose 2+1 := by
  let V := Fin (m+2)
  let inc := (univ : Finset (V ×ₗ V)).filter (fun e => (ofLex e).1 < (ofLex e).2)
  let diagonal := (univ : Finset V).map ⟨fun v => toLex (v,v),fun _ _ eq => congrArg (Prod.fst ∘ ofLex) eq⟩
  have diagMem {e : V ×ₗ V} : e ∈ diagonal ↔ (ofLex e).1 = (ofLex e).2 := by
    unfold diagonal
    simp only [mem_map,mem_univ,true_and]
    constructor
    · rintro ⟨x,rfl⟩
      rfl
    · intro eq
      exact ⟨(ofLex e).1,ofLex.injective (Prod.ext rfl eq)⟩
  have balance (e : V ×ₗ V) : e ∈ inc ↔ (ofLex e).1 < (ofLex e).2 := by simp [inc]
  have middle : increasingOrSingle m = diagonal ∪ inc := by
    ext e
    simp only [increasingOrSingle,mem_filter,mem_univ,true_and,mem_union,diagMem,balance,
      le_iff_lt_or_eq,or_comm]
  have sep : Disjoint diagonal inc := disjoint_left.mpr fun e on closer =>
    (balance e).mp closer |>.ne (diagMem.mp on)
  have forwardCards : inc.card = (m+2).choose 2 := by
    let plain := (univ : Finset (V × V)).filter (fun e => e.1 < e.2)
    have mapped : inc.map (ofLex : V ×ₗ V ≃ V × V).toEmbedding = plain := by
      ext e
      simp only [mem_map,Equiv.coe_toEmbedding,mem_filter,mem_univ,true_and,plain,balance]
      constructor
      · rintro ⟨a,ordered,rfl⟩
        exact ordered
      · intro ordered
        exact ⟨toLex e,ordered,rfl⟩
    rw [← card_map (f := (ofLex : V ×ₗ V ≃ V × V).toEmbedding),mapped]
    simpa only [plain,V,Fintype.card_fin] using (Fintype.card_product_filter_lt (α := V))
  have reversed : toLex (highest m,nextHighest m) ∉ increasingOrSingle m := by
    intro on
    have ordered := (mem_filter.mp on).2
    change m+1 ≤ m at ordered
    omega
  calc
    Fintype.card (TerminalPairLabel m) = (terminalPairLabels m).card := Fintype.card_coe _
    _ = (insert (toLex (highest m,nextHighest m)) (increasingOrSingle m)).card := rfl
    _ = _ := by
      rw [card_insert_of_notMem reversed,middle,card_union_of_disjoint sep,forwardCards]
      simp [diagonal,V]

/-- Any initial segment of this ordered literal family is a feasible
family at every half cutoff. -/
theorem literal_half_all_of_choose_budget_succ {m p : ℕ}
    (budget : p ≤ (m+2)+(m+2).choose 2+1) :
    ∃ rows : Fin p → List (Fin (m+2)), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ ∀ k, HalfBridgeFree (Before rows) k := by
  let order := Fintype.orderIsoFinOfCardEq (TerminalPairLabel m) (terminalPairLabel_card m)
  let label (i : Fin p) := order (Fin.castLE budget i)
  have inc : StrictMono label := fun _ _ lt => order.strictMono lt
  refine ⟨fun i => terminalPairRows m (label i),(terminalPairRows_injective m).comp inc.injective,
    fun i => terminalPairRows_valid (label i),?_⟩
  intro k d limit b earlier
  exact terminalPairRows_halfFree m k limit
    (b.mapPaths label inc.injective (fun _ _ _ step => step)) (inc earlier)

/-- Below the exact capacity, one literal family excludes half-bridges
of every size. For zero or one available vertex only singletons are used. -/
theorem literal_half_all_of_choose_budget {n p : ℕ}
    (budget : p ≤ n+n.choose 2+(if 2 ≤ n then 1 else 0)) :
    ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ ∀ k, HalfBridgeFree (Before rows) k := by
  by_cases large : 2 ≤ n
  · rw [ite_eq_left large] at budget
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le' large
    exact literal_half_all_of_choose_budget_succ budget
  · have small : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have fits : p ≤ n := by simpa [small,large] using budget
    let rows (i : Fin p) : List (Fin n) := [Fin.castLE fits i]
    have unique : Function.Injective rows := by
      intro i j same
      exact Fin.castLE_injective fits (by simpa [rows] using same)
    refine ⟨rows,unique,fun i => by simp [rows],?_⟩
    intro k d limit bridge earlier
    have start : bridge.vertex 0 = Fin.castLE fits bridge.river := by
      simpa [rows] using bridge.riverStep.1
    have endAt : bridge.vertex (Fin.last (d+1)) = Fin.castLE fits bridge.river := by
      simpa [rows] using bridge.riverStep.2.1
    exact listBefore_ne bridge.riverStep (start.trans endAt.symm)

/-- From half cutoff four onward the exact feasibility region is the
same as for exclusion of all half-bridges. -/
theorem literal_half_feasible_iff_of_four_le {n p k : ℕ} (four : 4 ≤ k) :
    (∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) k) ↔
    p ≤ n+n.choose 2+(if 2 ≤ n then 1 else 0) := by
  constructor
  · rintro ⟨rows,distinct,valid,free⟩
    by_cases large : 2 ≤ n
    · simpa only [ite_eq_left large] using literal_half_four_path_count_le_choose_add_one distinct valid free four
    · have small : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have none (i : Fin p) : (rows i).length-1 = 0 := by
        have fit : (rows i).length ≤ n := by
          rw [← List.toFinset_card_of_nodup (valid i).2]
          simpa only [Fintype.card_fin] using card_le_univ (rows i).toFinset
        omega
      have count := literal_path_count_le_vertices_add_gaps distinct (fun i => (valid i).1)
      simpa [small,large,none] using count
  · intro bound
    obtain ⟨rows,distinct,valid,all⟩ := literal_half_all_of_choose_budget bound
    exact ⟨rows,distinct,valid,all k⟩

theorem literal_half_all_feasible_iff {n p : ℕ} :
    (∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ ∀ k, HalfBridgeFree (Before rows) k) ↔
    p ≤ n+n.choose 2+(if 2 ≤ n then 1 else 0) := by
  constructor
  · rintro ⟨rows,distinct,valid,all⟩
    exact (literal_half_feasible_iff_of_four_le le_rfl).mp ⟨rows,distinct,valid,all 4⟩
  · exact literal_half_all_of_choose_budget

/-- Every literal half family at the saturated count has the same mass.
For at least two vertices this count is feasible at every half cutoff. -/
theorem literal_half_mass_at_saturated_four_budget {n k : ℕ}
    {rows : Fin (n+n.choose 2+1) → List (Fin n)} (distinct : Function.Injective rows)
    (valid : ∀ i, rows i ≠ [] ∧ (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) k) (four : 4 ≤ k) :
    (∑ i, (rows i).length) = n+2*(n.choose 2+1) := by
  have count := literal_path_count_le_vertices_add_gaps distinct (fun i => (valid i).1)
  have mass := rowMass_eq_gaps_add_count (fun i => (valid i).1)
  rw [Fintype.card_fin] at mass
  have upper := halfFour_mass_le_paths_add_choose_add_one valid free four
  omega

end OnlineReachabilityPreservers
