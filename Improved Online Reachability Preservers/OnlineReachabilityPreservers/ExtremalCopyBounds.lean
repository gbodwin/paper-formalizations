import OnlineReachabilityPreservers.IncidenceColorCleaning

/-! Disjoint copies, padding, and rectangular restrictions of extremal systems. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

section Copies

variable {I V C : Type*} [LinearOrder I] [LinearOrder V] [LinearOrder C]

def disjointListFamilies (paths : C → I → List V) (i : I ×ₗ C) : List (V ×ₗ C) :=
  (paths (ofLex i).2 (ofLex i).1).map fun x => toLex (x,(ofLex i).2)

omit [LinearOrder I] [LinearOrder V] [LinearOrder C] in
theorem disjointListFamilies_simple (paths : C → I → List V) (simple : ∀ c i, (paths c i).Nodup)
    (i : I ×ₗ C) : (disjointListFamilies paths i).Nodup :=
  (simple (ofLex i).2 (ofLex i).1).map fun _ _ eq => congrArg (fun w => (ofLex w).1) eq

theorem disjointListFamilies_admissible (paths : C → I → List V) (simple : ∀ c i, (paths c i).Nodup)
    {half : Bool} {k : ℕ} (allowed : ∀ c, localOrderAdmissible half k (paths c)) :
    localOrderAdmissible half k (disjointListFamilies paths) := by
  let pieces := disjointListFamilies paths
  let parent (i : I ×ₗ C) := (ofLex i).1
  let rowColor (i : I ×ₗ C) := (ofLex i).2
  let untag (v : V ×ₗ C) := (ofLex v).1
  let vertexColor (v : V ×ₗ C) := (ofLex v).2
  have tagged {i : I ×ₗ C} {v : V ×ₗ C} (member : v ∈ pieces i) : vertexColor v = rowColor i := by
    obtain ⟨old,_,equal⟩ := List.mem_map.mp member
    exact (congrArg vertexColor equal).symm
  have project (i : I ×ₗ C) : (pieces i).map untag = paths (rowColor i) (parent i) := by
    simp [pieces, disjointListFamilies, untag, rowColor, parent, List.map_map, Function.comp_def]
  have step {i x y} (before : Before pieces i x y) :
      Before (paths (rowColor i)) (parent i) (untag x) (untag y) := by
    have mapped := listBefore_map untag ((project i).symm ▸ simple (rowColor i) (parent i)) before
    unfold SourceAudit.BeforeIn at mapped ⊢
    simpa only [project i] using mapped
  exact localOrderAdmissible_of_tagged_steps paths pieces tagged step allowed

variable [Fintype I] [Fintype C]

omit [LinearOrder I] [LinearOrder V] [LinearOrder C] in
theorem disjointListFamilies_mass (paths : C → I → List V) :
    (∑ i, (disjointListFamilies paths i).length) = ∑ c, ∑ i, (paths c i).length := by
  calc
    _ = ∑ j : I × C, (disjointListFamilies paths (toLex j)).length :=
      (Equiv.sum_comp (toLex : (I × C) ≃ (I ×ₗ C)) _).symm
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]; simp [disjointListFamilies]

end Copies

/-- A tagged vertex has exactly the degree it had in its own family. -/
theorem disjointListFamilies_degree {I V C : Type*} [LinearOrder I] [Fintype I] [LinearOrder V]
    [LinearOrder C] [Fintype C] (paths : C → I → List V) (v : V ×ₗ C) :
    (occurrences (fun i => (disjointListFamilies paths i).toFinset) v).card =
      (occurrences (fun i => (paths (ofLex v).2 i).toFinset) (ofLex v).1).card := by
  let embed : I ↪ I ×ₗ C := ⟨fun i => toLex (i,(ofLex v).2),fun _ _ eq => congrArg (fun i => (ofLex i).1) eq⟩
  let localRows := fun i : I => (paths (ofLex v).2 i).toFinset
  let old := occurrences localRows (ofLex v).1
  have exactRows : occurrences (fun i => (disjointListFamilies paths i).toFinset) v = old.map embed := by
    ext i
    simp only [mem_occurrences,List.mem_toFinset,mem_map]
    constructor
    · intro member
      obtain ⟨u,on,eq⟩ := List.mem_map.mp member
      have vertex : u = (ofLex v).1 := congrArg (fun z : V ×ₗ C => (ofLex z).1) eq
      have color : (ofLex i).2 = (ofLex v).2 := congrArg (fun z : V ×ₗ C => (ofLex z).2) eq
      change u ∈ paths (ofLex i).2 (ofLex i).1 at on
      rw [vertex,color] at on
      exact ⟨(ofLex i).1,mem_occurrences.mpr (List.mem_toFinset.mpr on),
        ofLex.injective (Prod.ext rfl color.symm)⟩
    · rintro ⟨j,on,rfl⟩
      have vertex : (ofLex v).1 ∈ paths (ofLex v).2 j :=
        List.mem_toFinset.mp ((mem_occurrences (marks := localRows)).mp on)
      exact List.mem_map.mpr ⟨(ofLex v).1,vertex,ofLex.injective rfl⟩
  rw [exactRows,card_map]

private def padListFamily {n p N P : ℕ} (paths : Fin p → List (Fin n)) (budget : n ≤ N)
    (i : Fin P) : List (Fin N) :=
  if h : i.val < p then (paths ⟨i.val,h⟩).map (Fin.castLE budget) else []

private theorem padListFamily_membership {n p N P : ℕ} {paths : Fin p → List (Fin n)}
    {budget : n ≤ N} {i : Fin P} {v : Fin N} (member : v ∈ padListFamily paths budget i) :
    i.val < p ∧ v.val < n := by
  unfold padListFamily at member
  split at member
  · rename_i h
    obtain ⟨old,_,rfl⟩ := List.mem_map.mp member
    exact ⟨h,old.isLt⟩
  · simp at member

private theorem padListFamily_step {n p N P : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) {budget : n ≤ N} {i : Fin P} {x y : Fin N}
    (hi : i.val < p) (hx : x.val < n) (hy : y.val < n)
    (step : Before (padListFamily paths budget) i x y) :
    Before paths ⟨i.val,hi⟩ ⟨x.val,hx⟩ ⟨y.val,hy⟩ := by
  let project (v : Fin N) : Fin n := ⟨v.val % n,Nat.mod_lt _ (Nat.zero_lt_of_lt hx)⟩
  have mapRow : (padListFamily paths budget i).map project = paths ⟨i.val,hi⟩ := by
    rw [padListFamily, dite_eq_left hi, List.map_map]
    have inverse : project ∘ Fin.castLE budget = id := by
      funext v
      exact Fin.ext (Nat.mod_eq_of_lt v.isLt)
    rw [inverse,List.map_id]
  have forward := listBefore_map project (mapRow.symm ▸ simple ⟨i.val,hi⟩) step
  have left : project x = (⟨x.val,hx⟩ : Fin n) := Fin.ext (Nat.mod_eq_of_lt hx)
  have right : project y = (⟨y.val,hy⟩ : Fin n) := Fin.ext (Nat.mod_eq_of_lt hy)
  unfold SourceAudit.BeforeIn at forward ⊢
  simpa only [mapRow,left,right] using forward

private theorem padListFamily_admissible {n p N P : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) {half : Bool} {k : ℕ}
    (allowed : localOrderAdmissible half k paths) (budget : n ≤ N) :
    localOrderAdmissible half k (padListFamily (P := P) paths budget) := by
  have project {s : ℕ} (b : Bridge (Before (padListFamily (P := P) paths budget)) s) :
      ∃ old : Bridge (Before paths) s, old.river.val = b.river.val ∧
        ∀ i, (old.arc i).val = (b.arc i).val := by
    have vInside (i : Fin (s+2)) : (b.vertex i).val < n := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact (padListFamily_membership b.riverStep.2.1).2
      · exact (padListFamily_membership (b.arcStep j).1).2
    let vertices (i : Fin (s+2)) : Fin n := ⟨(b.vertex i).val,vInside i⟩
    let arcs (i : Fin (s+1)) : Fin p := ⟨(b.arc i).val,(padListFamily_membership (b.arcStep i).1).1⟩
    let river : Fin p := ⟨b.river.val,(padListFamily_membership b.riverStep.1).1⟩
    let old : Bridge (Before paths) s :=
      ⟨vertices,arcs,river,
        fun _ _ equal => b.distinctVertices (Fin.ext (congrArg (@Fin.val n) equal)),
        fun _ _ equal => b.distinctArcs (Fin.ext (congrArg (@Fin.val p) equal)),
        fun i equal => b.river_ne_arc i (Fin.ext (congrArg (@Fin.val p) equal)),
        padListFamily_step simple river.isLt (vInside 0) (vInside (Fin.last (s+1))) b.riverStep,
        fun i => padListFamily_step simple (arcs i).isLt (vInside i.castSucc) (vInside i.succ) (b.arcStep i)⟩
    exact ⟨old,rfl,fun _ => rfl⟩
  cases half
  · intro s hs
    exact ⟨fun b => (allowed hs).false (project b).choose⟩
  · intro s hs b comesFirst
    obtain ⟨old,river,arcs⟩ := project b
    apply allowed hs old
    change (old.arc (Fin.last s)).val < old.river.val
    rw [river,arcs]
    exact comesFirst

private theorem padListFamily_spec {n p N P : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) {half : Bool} {k : ℕ}
    (allowed : localOrderAdmissible half k paths) (vBudget : n ≤ N) (pBudget : p ≤ P) :
    (∀ i : Fin P, (padListFamily paths vBudget i).Nodup) ∧
      localOrderAdmissible half k (padListFamily (P := P) paths vBudget) ∧
      (∑ i : Fin P, (padListFamily paths vBudget i).length) = ∑ i, (paths i).length := by
  refine ⟨?_,padListFamily_admissible paths simple allowed vBudget,?_⟩
  · intro i
    unfold padListFamily
    split
    · exact (simple _).map (Fin.castLE_injective _)
    · simp
  · let embed := Fin.castLEEmb pBudget
    have active {i : Fin P} (hi : i.val < p) : i ∈ (univ : Finset (Fin p)).map embed := by
      exact mem_map.mpr ⟨⟨i.val,hi⟩,mem_univ _,Fin.ext rfl⟩
    rw [← sum_subset (subset_univ ((univ : Finset (Fin p)).map embed)) (f := fun i => (padListFamily paths vBudget i).length)]
    · rw [sum_map]
      apply sum_congr rfl
      intro i _
      have bound : (embed i).val < p := i.isLt
      rw [padListFamily,dite_eq_left bound,List.length_map]
      rfl
    · intro i _ outside
      rw [padListFamily,dite_eq_right (fun bound => outside (active bound)),List.length_nil]

/-- Disjoint copies preserve either bridge condition and multiply the path mass. -/
theorem exists_disjoint_copies_with_budgets {n p N P t : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) {half : Bool} {k : ℕ}
    (allowed : localOrderAdmissible half k paths) (nBudget : t*n ≤ N) (pBudget : t*p ≤ P) :
    ∃ bigger : Fin P → List (Fin N), (∀ i, (bigger i).Nodup) ∧ localOrderAdmissible half k bigger ∧
      (∑ i, (bigger i).length) = t * (∑ i, (paths i).length) := by
  let copies (c : Fin t) := paths
  let family := disjointListFamilies copies
  have vCard : Fintype.card (Fin n ×ₗ Fin t) = t*n := by
    rw [← Fintype.card_congr (toLex : Fin n × Fin t ≃ Fin n ×ₗ Fin t), Fintype.card_prod]
    simp only [Fintype.card_fin, Nat.mul_comm]
  have pCard : Fintype.card (Fin p ×ₗ Fin t) = t*p := by
    rw [← Fintype.card_congr (toLex : Fin p × Fin t ≃ Fin p ×ₗ Fin t), Fintype.card_prod]
    simp only [Fintype.card_fin, Nat.mul_comm]
  obtain ⟨simple',allowed',renumberedMass,_,_⟩ := relabelListPathsFin_spec family
    (disjointListFamilies_simple copies (fun _ => simple))
    (disjointListFamilies_admissible copies (fun _ => simple) (fun _ => allowed))
  let clean := relabelListPathsFin family
  let vFit := vCard.trans_le nBudget
  let pFit := pCard.trans_le pBudget
  obtain ⟨finalSimple,finalAllowed,finalMass⟩ := padListFamily_spec clean simple' allowed' vFit pFit
  refine ⟨padListFamily clean vFit, finalSimple, finalAllowed, ?_⟩
  rw [finalMass,renumberedMass,disjointListFamilies_mass]
  simp [copies]

/-- A rectangle in a maximizing system cannot be heavier than its copies
would allow under the original budgets. -/
theorem localOrderMaximizer_rectangle_mass_mul_le {n p k t : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (maximal : ∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
      (∑ i, (other i).length) ≤ ∑ i, (paths i).length)
    (A : Finset (Fin n)) (B : Finset (Fin p)) (vFit : t*A.card ≤ n) (pFit : t*B.card ≤ p) :
    t*(∑ i : B, (restrictListPaths paths A B i).length) ≤ ∑ i, (paths i).length := by
  let cut := restrictListPaths paths A B
  have cutSimple (i : B) : (cut i).Nodup := restrictListPath_nodup (simple i.val) A
  have cutAllowed : localOrderAdmissible half k cut := by
    cases half
    · exact restrictListPaths_fullFree simple allowed A B
    · exact restrictListPaths_halfFree simple allowed A B
  obtain ⟨smallSimple,smallAllowed,smallMass,_,_⟩ := relabelListPathsFin_spec cut cutSimple cutAllowed
  obtain ⟨bigger,bSimple,bAllowed,bMass⟩ := exists_disjoint_copies_with_budgets (relabelListPathsFin cut)
    smallSimple smallAllowed (by simpa only [Fintype.card_coe] using vFit)
    (by simpa only [Fintype.card_coe] using pFit)
  rw [smallMass] at bMass
  rw [← bMass]
  exact maximal bigger bSimple bAllowed

private theorem four_mul_card_above_mean_le {A : Type*} [Fintype A] (weight : A → ℕ)
    (nonempty : 0 < Fintype.card A) :
    let M := ∑ a, weight a
    let q := Fintype.card A
    4*(univ.filter fun a => 4*M/q < weight a).card ≤ q := by
  let M := ∑ a, weight a
  let q := Fintype.card A
  let width := 4*M/q
  let large := univ.filter fun a => width < weight a
  change 4*large.card ≤ q
  by_cases positive : 0 < M
  · have perItem : (width+1)*large.card ≤ M := calc
      _ = ∑ _ ∈ large, (width+1) := by simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ large, weight a := sum_le_sum
        (fun a inside => Nat.succ_le_of_lt (mem_filter.mp inside).2)
      _ ≤ _ := sum_le_sum_of_subset (subset_univ _)
    have scaled : (4*large.card)*M ≤ q*M := calc
      _ = (4*M)*large.card := by ring
      _ ≤ (q*(width+1))*large.card := Nat.mul_le_mul_right _ (Nat.lt_mul_div_succ _ nonempty).le
      _ = q*((width+1)*large.card) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ perItem
    exact Nat.le_of_mul_le_mul_right scaled positive
  · have zero : M = 0 := by omega
    have summed : ∑ a, weight a = 0 := zero
    have everyZero : ∀ a, weight a = 0 := fun a => (sum_eq_zero_iff.mp summed) a (mem_univ a)
    simp [large,everyZero]

/-- At most a quarter of the mass of a maximizing family lies in the
intersection of rows and vertices above their original upper caps. -/
theorem localOrderMaximizer_overloaded_rectangle_mass_le {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (maximal : ∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
      (∑ i, (other i).length) ≤ ∑ i, (paths i).length)
    (hn : 0 < n) (hp : 0 < p) :
    let M := ∑ i, (paths i).length
    let A := univ.filter fun v => 4*M/n < (occurrences (fun i => (paths i).toFinset) v).card
    let B := univ.filter fun i => 4*M/p < (paths i).length
    4*(∑ i : B, (restrictListPaths paths A B i).length) ≤ M := by
  let M := ∑ i, (paths i).length
  let degree := fun v => (occurrences (fun i => (paths i).toFinset) v).card
  have vertexMass : (∑ v, degree v) = M := by
    rw [sum_occurrences]
    exact sum_congr rfl fun i _ => List.toFinset_card_of_nodup (simple i)
  have vertexCount := four_mul_card_above_mean_le degree (by simpa only [Fintype.card_fin] using hn)
  have rowCount := four_mul_card_above_mean_le (fun i => (paths i).length)
    (by simpa only [Fintype.card_fin] using hp)
  dsimp only at vertexCount rowCount
  rw [vertexMass,Fintype.card_fin] at vertexCount
  rw [Fintype.card_fin] at rowCount
  exact localOrderMaximizer_rectangle_mass_mul_le paths simple allowed maximal _ _ vertexCount rowCount

end OnlineReachabilityPreservers
