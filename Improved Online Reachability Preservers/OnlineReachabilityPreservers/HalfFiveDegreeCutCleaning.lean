import OnlineReachabilityPreservers.HalfFivePathCleaning

/-! Repair only opposite comparisons crossing an actual degree cut. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

/-- The two retained incidences of a reversed comparison sit at different
arrival blocks of the same original vertex. -/
def OppositeDegreeCutConflict {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ)
    (a b : Fin p × ListVertexBlockIndex paths D) : Prop :=
  a.2 ∈ splitListVertices paths D a.1 ∧ b.2 ∈ splitListVertices paths D b.1 ∧
    a.2.fst = b.2.fst ∧ a.2.snd.val ≠ b.2.snd.val ∧
    LaterReversePartner paths a.2.fst a.1 b.1

/-- Mark exactly the copied incidences with a reverse partner across an
arrival block at their original vertex. -/
noncomputable def halfFiveDegreeCutAffected {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ) :
    Finset (Fin p × ListVertexBlockIndex paths D) := by
  classical
  exact univ.filter fun a =>
    (∃ b, OppositeDegreeCutConflict paths D a b) ∨ (∃ b, OppositeDegreeCutConflict paths D b a)

/-- Remove one original reverse-partner color on the crossed degree
comparisons. -/
noncomputable def halfFiveDegreeCutDeletion {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ) (c : Bool) :
    Finset (Fin p × ListVertexBlockIndex paths D) :=
  (halfFiveDegreeCutAffected paths D).filter fun a => reversePartnerColor paths a.2.fst a.1 = c

theorem halfFiveDegreeCutAffected_subset {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ) :
    halfFiveDegreeCutAffected paths D ⊆ pieceIncidences (splitListVertices paths D) univ := by
  classical
  intro a member
  rcases (mem_filter.mp member).2 with ⟨_,edge⟩ | ⟨_,edge⟩
  · exact mem_pieceIncidences.mpr ⟨mem_univ _,edge.1⟩
  · exact mem_pieceIncidences.mpr ⟨mem_univ _,edge.2.1⟩

theorem halfFiveDegreeCutDeletion_covers {n p : ℕ} {paths : Fin p → List (Fin n)}
    (free : HalfBridgeFree (Before paths) 5) {D : ℕ} {a b : Fin p × ListVertexBlockIndex paths D}
    (edge : OppositeDegreeCutConflict paths D a b) (c : Bool) :
    a ∈ halfFiveDegreeCutDeletion paths D c ∨ b ∈ halfFiveDegreeCutDeletion paths D c := by
  classical
  have markedA : a ∈ halfFiveDegreeCutAffected paths D :=
    mem_filter.mpr ⟨mem_univ _,Or.inl ⟨b,edge⟩⟩
  have markedB : b ∈ halfFiveDegreeCutAffected paths D :=
    mem_filter.mpr ⟨mem_univ _,Or.inr ⟨a,edge⟩⟩
  let colorA := reversePartnerColor paths a.2.fst a.1
  let colorB := reversePartnerColor paths b.2.fst b.1
  have opposite : colorA ≠ colorB := by
    change reversePartnerColor paths a.2.fst a.1 ≠ reversePartnerColor paths b.2.fst b.1
    rw [← edge.2.2.1]
    exact reversePartnerColor_ne free (by decide) edge.2.2.2.2
  have choose {x y c : Bool} (ne : x ≠ y) : x = c ∨ y = c := by
    cases x <;> cases y <;> cases c <;> simp_all
  have hits : colorA = c ∨ colorB = c := choose opposite
  exact hits.imp (fun eq => mem_filter.mpr ⟨markedA,eq⟩) (fun eq => mem_filter.mpr ⟨markedB,eq⟩)

/-- Given the consecutive degree blocks, only an older row ending a
retained reverse comparison can create a terminal copy collision. -/
theorem eraseDegreeBlocks_halfFive_of_no_live_return {n p : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5) (D : ℕ)
    (deleted : Finset (Fin p × ListVertexBlockIndex paths D))
    (safe : let rows := erasePieceIncidences (splitListVertices paths D) deleted
      ∀ {a b : Fin p} {v w x : ListVertexBlockIndex paths D}, a < b → v.fst = w.fst →
        Before rows a x v → Before rows b w x → v = w) :
    HalfBridgeFree (Before (erasePieceIncidences (splitListVertices paths D) deleted)) 5 := by
  let copies := splitListVertices paths D
  let rows := erasePieceIncidences copies deleted
  let project (v : ListVertexBlockIndex paths D) := v.fst
  have step {i x y} (found : Before rows i x y) : Before paths i (project x) (project y) :=
    splitListVertices_step (simple i)
      (listBefore_of_sublist (splitListVertices_simple paths D i (simple i))
        (erasePieceIncidences_sublist copies deleted i) found)
  intro d cutoff bridge earlier
  by_cases short : d ≤ 2
  · have input : HalfBridgeFree (Before paths) 4 := fun _ bound => free (bound.trans (by decide))
    exact input.split_list_vertices_short le_rfl project (fun {_ _ _} => step) (by omega) bridge earlier
  have size : d = 3 := by omega
  subst d
  obtain ⟨same,riverBefore⟩ :=
    free.project_half_five_terminal_collision project (fun {_ _ _} => step) bridge earlier
  change (bridge.vertex 2).fst = (bridge.vertex 4).fst at same
  have onReturn := (mem_erasePieceIncidences.mp (bridge.arcStep 2).1).1
  have atRiver := (mem_erasePieceIncidences.mp bridge.riverStep.2.1).1
  have atSecond := (mem_erasePieceIncidences.mp (bridge.arcStep 1).2.1).1
  have vNe : bridge.vertex 4 ≠ bridge.vertex 2 := fun h =>
    (by decide : (4:Fin 5) ≠ 2) (bridge.distinctVertices h)
  have blocksLE := splitListVertices_block_mono same.symm riverBefore.le atRiver atSecond
  have blocksLT := blocksLE.lt_of_ne (fun h => vNe (vertexBlock_eq_of_same_label same.symm h))
  have riverBeforeReturn : bridge.river < bridge.arc 2 := lt_of_not_ge fun closer =>
    blocksLT.not_ge (splitListVertices_block_mono same closer onReturn atRiver)
  exact vNe (safe (earlier.trans riverBeforeReturn) same.symm (bridge.arcStep 3) (bridge.arcStep 2))

/-- In the degree-first order, covering all actual crossed comparisons
preserves half-five exclusion even with additional deletions. -/
theorem eraseDegreeCutConflicts_halfFree {n p : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5) (D : ℕ)
    (deleted : Finset (Fin p × ListVertexBlockIndex paths D))
    (cover : ∀ {a b}, OppositeDegreeCutConflict paths D a b → a ∈ deleted ∨ b ∈ deleted) :
    HalfBridgeFree (Before (erasePieceIncidences (splitListVertices paths D) deleted)) 5 := by
  refine eraseDegreeBlocks_halfFive_of_no_live_return simple free D deleted ?_
  dsimp only
  intro a b v w x arrives same forward backward
  by_contra! distinct
  let copies := splitListVertices paths D
  let rows := erasePieceIncidences copies deleted
  have step {i u z} (found : Before rows i u z) : Before paths i u.fst z.fst :=
    splitListVertices_step (simple i)
      (listBefore_of_sublist (splitListVertices_simple paths D i (simple i))
        (erasePieceIncidences_sublist copies deleted i) found)
  have vOn := mem_erasePieceIncidences.mp forward.2.1
  have wOn := mem_erasePieceIncidences.mp backward.1
  have different : v.snd.val ≠ w.snd.val := fun eq => distinct (vertexBlock_eq_of_same_label same eq)
  have edge : OppositeDegreeCutConflict paths D (a,v) (b,w) :=
    ⟨vOn.1,wOn.1,same,different,arrives,x.fst,step forward,same.symm ▸ step backward⟩
  exact (cover edge).elim vOn.2 wOn.2

theorem halfFiveDegreeCutRepair_halfFree {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5) (D : ℕ) (c : Bool) :
    HalfBridgeFree (Before (erasePieceIncidences (splitListVertices paths D) (halfFiveDegreeCutDeletion paths D c))) 5 :=
  eraseDegreeCutConflicts_halfFree simple free D _ (fun {_ _} edge => halfFiveDegreeCutDeletion_covers free edge c)

private theorem crossedDegree_retained_mass {M W R Y C : ℕ}
    (positive : 0 < M) (wLow : 27*M ≤ 25*W) (wHigh : W ≤ 2*M)
    (capacity : 31*M ≤ 8*C) (loss : 4*C*Y ≤ W^2)
    (choose : W ≤ 2*R+Y) : 251*M ≤ 500*R := by
  have charge : 31*M*Y ≤ 2*W^2 := calc
    _ ≤ (8*C)*Y := Nat.mul_le_mul_right _ capacity
    _ = 2*(4*C*Y) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ loss
  have paid : 31*M*W ≤ 62*M*R+2*W^2 := calc
    _ ≤ (31*M)*(2*R+Y) := Nat.mul_le_mul_left _ choose
    _ = 62*M*R+31*M*Y := by ring
    _ ≤ _ := Nat.add_le_add_left charge _
  have paidReal : 31*(M:ℝ)*W ≤ 62*(M:ℝ)*R+2*(W:ℝ)^2 := by exact_mod_cast paid
  have low : (27/25)*(M:ℝ) ≤ W := by
    have h : 27*(M:ℝ) ≤ 25*(W:ℝ) := by exact_mod_cast wLow
    linarith
  have high : (W:ℝ) ≤ 2*(M:ℝ) := by exact_mod_cast wHigh
  have monotone := mul_nonneg (sub_nonneg.mpr low)
    (show 0 ≤ 31*(M:ℝ)-2*((W:ℝ)+(27/25)*(M:ℝ)) by linarith)
  have enough : (251*(M:ℝ))*M ≤ (500*(R:ℝ))*M := by
    nlinarith only [paidReal,monotone,sq_nonneg (M:ℝ)]
  apply (Nat.mul_le_mul_right_iff positive).mp
  exact_mod_cast enough

/-- When the path lengths already meet the original cap, count only
the reversed comparisons that cross the actual degree cuts. The bound
charges two units for each incidence missing from the benchmark mass. -/
theorem regularization_list_frozen_half_five_of_degree_cut_mass {n p M : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : 8*n ≤ M) (long : p ≤ M)
    (lengthCap : ∀ i, (paths i).length ≤ 4*M/p) (upper : (∑ i, (paths i).length) ≤ M)
    (gain : 27*M+25*(halfFiveDegreeCutAffected paths (4*M/n)).card ≤ 50*(∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let D := 4*M/n
  let V := ListVertexBlockIndex paths D
  let copies := splitListVertices paths D
  let affected := halfFiveDegreeCutAffected paths D
  let deleted := halfFiveDegreeCutDeletion paths D
  let rows (c : Bool) := erasePieceIncidences copies (deleted c)
  let degree (c : Bool) (v : V) := (occurrences (fun i => (rows c i).toFinset) v).card
  let weight (v : V) := degree false v+degree true v
  let W := ∑ v : V, weight v
  let K := ∑ i, (paths i).length
  have nBound : n ≤ M := by omega
  have mPos := hn.trans_le nBound
  have dPos : 0 < D := (four_average_width hn nBound).1
  have capacity : 31*M ≤ 8*(D*n) := by
    have floor := four_average_width_product hn (M := M)
    change 4*M < D*n+n at floor
    omega
  have copySimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have rowSimple (c : Bool) (i : Fin p) : (rows c i).Nodup :=
    (erasePieceIncidences_sublist copies (deleted c) i).nodup (copySimple i)
  have massCopies : (∑ i, (copies i).length) = K :=
    sum_congr rfl (fun i _ => splitListVertices_length paths D i)
  have dSubset (c : Bool) : deleted c ⊆ pieceIncidences copies univ :=
    (filter_subset _ _).trans (halfFiveDegreeCutAffected_subset paths D)
  have union : deleted false ∪ deleted true = affected := by
    ext a
    cases eq : reversePartnerColor paths a.2.fst a.1 <;>
      simp [deleted,affected,halfFiveDegreeCutDeletion,eq]
  have separate : Disjoint (deleted false) (deleted true) := by
    apply disjoint_left.mpr
    intro a left right
    exact Bool.false_ne_true ((mem_filter.mp left).2.symm.trans (mem_filter.mp right).2)
  have balance (c : Bool) : (∑ i, (rows c i).length)+(deleted c).card = K := by
    have count := erasePieceIncidences_mass_add_loss copySimple (univ : Finset (Fin p)) (deleted c)
    change (∑ i, (rows c i).length)+(pieceIncidences copies univ ∩ deleted c).card =
      (∑ i, (copies i).length) at count
    rw [inter_eq_right.mpr (dSubset c),massCopies] at count
    exact count
  have tally (c : Bool) : (∑ v : V, degree c v) = ∑ i, (rows c i).length :=
    (sum_occurrences (fun i => (rows c i).toFinset)).trans
      (sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (rowSimple c i)))
  have weightMass : W = (∑ i, (rows false i).length)+(∑ i, (rows true i).length) := by
    change (∑ v : V, (degree false v+degree true v)) = _
    rw [sum_add_distrib,tally false,tally true]
  have exactW : W+affected.card = 2*K := calc
    _ = ((∑ i, (rows false i).length)+(deleted false).card)+
        ((∑ i, (rows true i).length)+(deleted true).card) := by
      rw [← union,card_union_of_disjoint separate,weightMass]
      exact add_add_add_comm _ _ _ _
    _ = _ := by rw [balance false,balance true,Nat.two_mul]
  have weightLower (v : V) : (occurrences (fun i => (copies i).toFinset) v).card ≤ weight v := by
    have exactUnion :
        occurrences (fun i => (rows false i).toFinset) v ∪ occurrences (fun i => (rows true i).toFinset) v =
          occurrences (fun i => (copies i).toFinset) v := by
      ext i
      simp only [mem_union,mem_occurrences,List.mem_toFinset]
      change (v ∈ erasePieceIncidences copies (deleted false) i ∨ v ∈ erasePieceIncidences copies (deleted true) i) ↔ _
      simp only [mem_erasePieceIncidences]
      constructor
      · rintro (left | right) <;> exact (by assumption : _ ∧ _).1
      · intro on
        by_cases removed : (i,v) ∈ deleted false
        · exact Or.inr ⟨on,fun other => disjoint_left.mp separate removed other⟩
        · exact Or.inl ⟨on,removed⟩
    rw [← exactUnion]
    exact card_union_le _ _
  change 27*M+25*affected.card ≤ 50*K at gain
  change K ≤ M at upper
  have lowerW : 27*M ≤ 25*W := by omega
  have upperW : W ≤ 2*M := by omega
  obtain ⟨full,filled,remainder⟩ := splitListVertices_full_block_profile paths dPos
  have rest : (univ \ full).card ≤ n := by simpa only [Fintype.card_fin] using remainder.le
  have room : W ≤ D*n := by omega
  obtain ⟨kept,budget,trim⟩ := trim_full_weight_blocks_quadratic_of_lower_bound weight full dPos
    (fun v on => (filled v on).ge.trans (weightLower v)) rest room
  let Y := ∑ v ∈ univ \ kept, weight v
  have loss : 4*(D*n)*Y ≤ W^2 := trim
  have keptWeight : Y+((∑ v ∈ kept, degree false v)+(∑ v ∈ kept, degree true v)) = W := by
    have exactMass : Y+(∑ v ∈ kept, weight v) = W := sum_sdiff (subset_univ kept)
    rw [show (∑ v ∈ kept, weight v) =
      (∑ v ∈ kept, degree false v)+(∑ v ∈ kept, degree true v) from sum_add_distrib] at exactMass
    exact exactMass
  obtain ⟨c,selected⟩ : ∃ c : Bool, W ≤ 2*(∑ v ∈ kept, degree c v)+Y := by
    rcases le_total (∑ v ∈ kept, degree false v) (∑ v ∈ kept, degree true v) with h | h
    · exact ⟨true,by omega⟩
    · exact ⟨false,by omega⟩
  let R := ∑ v ∈ kept, degree c v
  have enough : 251*M ≤ 500*R := crossedDegree_retained_mass mPos lowerW upperW capacity loss selected
  have rowFree : HalfBridgeFree (Before (rows c)) 5 := halfFiveDegreeCutRepair_halfFree paths simple free D c
  have rowLength (i : Fin p) : (rows c i).length ≤ 4*M/p :=
    (erasePieceIncidences_sublist copies (deleted c) i).length_le.trans
      ((splitListVertices_length paths D i).trans_le (lengthCap i))
  have rawDegree (v : V) : (occurrences (fun i => (copies i).toFinset) v).card ≤ D := by
    rw [show (fun i => (copies i).toFinset) = splitVertices (fun i => (paths i).toFinset) D from
      funext (splitListVertices_toFinset paths D)]
    exact splitVertices_degree _ dPos v
  have rowDegree (v : V) : degree c v ≤ D := by
    refine (card_le_card ?_).trans (rawDegree v)
    intro i onRow
    have present : v ∈ rows c i :=
      List.mem_toFinset.mp ((mem_occurrences (marks := fun j => (rows c j).toFinset)).mp onRow)
    exact mem_occurrences.mpr (List.mem_toFinset.mpr
      (mem_erasePieceIncidences.mp present).1)
  have massUpper : (∑ i, (rows c i).length) ≤ M :=
    (sum_le_sum fun i _ => (erasePieceIncidences_sublist copies (deleted c) i).length_le).trans
      (massCopies.trans_le upper)
  refine regularization_list_frozen_after_kept_vertices (half := true) (k := 5) (retention := 5000)
    (rows c) (rowSimple c) rowFree hn hp nBound long (by decide) kept budget
    (by rw [Fintype.card_fin]) rowLength rowDegree massUpper ?_
  change (M:ℝ)/5000 ≤ (R:ℝ)-(M:ℝ)/(4*(n:ℝ))*(kept.card:ℝ)-
    (M:ℝ)/(4*(p:ℝ))*(Fintype.card (Fin p):ℝ)
  rw [Fintype.card_fin]
  have feeV : (M:ℝ)/(4*(n:ℝ))*(kept.card:ℝ) ≤ (M:ℝ)/4 := calc
    _ ≤ (M:ℝ)/(4*(n:ℝ))*(n:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr budget) (by positivity)
    _ = _ := by field_simp [show (n:ℝ) ≠ 0 by exact_mod_cast hn.ne']
  have feeP : (M:ℝ)/(4*(p:ℝ))*(p:ℝ) = (M:ℝ)/4 := by
    field_simp [show (p:ℝ) ≠ 0 by exact_mod_cast hp.ne']
  have real : 251*(M:ℝ) ≤ 500*(R:ℝ) := by exact_mod_cast enough
  linarith only [feeV,feeP,real,Nat.cast_nonneg (α := ℝ) M]

/-- Clip at the original length width, then count only the reverse comparisons
across degree cuts of the clipped rows. This preserves both original budgets. -/
theorem regularization_list_frozen_half_five_of_degree_cut_after_clipping {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (gain : let M := ∑ i, (paths i).length
      let clipped (i : Fin p) := (paths i).take (4*M/p)
      27*M+25*(halfFiveDegreeCutAffected clipped (4*M/n)).card ≤ 50*(∑ i, (clipped i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vBudget,q,qBudget,clean,cleanSimple,legal,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨v,vBudget,q,qBudget,clean,cleanSimple,fun _ small b _ => (legal small).false b,
      mass.trans (Nat.mul_le_mul_right _ (by decide)),upper,caps⟩
  let clipped (i : Fin p) := (paths i).take (4*M/p)
  have sub (i : Fin p) : (clipped i).Sublist (paths i) := List.take_sublist _ _
  have legal : HalfBridgeFree (Before clipped) 5 := by
    intro k small bridge earlier
    exact free small (bridge.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step)) earlier
  have big : 8*n ≤ M := (Nat.mul_le_mul_left _ (le_max_left _ _)).trans (lt_of_not_ge low).le
  exact regularization_list_frozen_half_five_of_degree_cut_mass clipped (fun i => (sub i).nodup (simple i))
    legal hn hp big long (fun i => List.length_take_le _ _) (sum_le_sum fun i _ => (sub i).length_le) gain

end OnlineReachabilityPreservers
