import OnlineReachabilityPreservers.HalfFiveDegreeCutCleaning
import OnlineReachabilityPreservers.LocalSourceCounting

/-! Joint repair of the actual cuts in the degree-first width split. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

/-- Mark the actual degree-cut conflicts and the path-cut conflicts of the
copied rows, each recorded at its path-piece incidence. -/
noncomputable def halfFiveDegreeFirstAffected {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ) :
    Finset (ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D) :=
  let copies := splitListVertices paths D
  let raw := listRegularizedPaths paths D L
  oppositeWidthConflictIncidences copies raw Sigma.fst ∪
    (pieceIncidences raw univ).filter fun a => (a.1.fst,a.2) ∈ halfFiveDegreeCutAffected paths D

/-- Remove one original reverse-partner color on the two actual cut sets. -/
noncomputable def halfFiveDegreeFirstDeletion {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ) (c : Bool) :
    Finset (ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D) :=
  (halfFiveDegreeFirstAffected paths D L).filter fun a =>
    reversePartnerColor paths a.2.fst a.1.fst = c

theorem halfFiveDegreeFirstAffected_subset {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ) :
    halfFiveDegreeFirstAffected paths D L ⊆ pieceIncidences (listRegularizedPaths paths D L) univ := by
  classical
  intro a member
  rcases mem_union.mp member with path | degree
  · rcases (mem_filter.mp path).2 with ⟨_,edge⟩ | ⟨_,edge⟩
    · exact mem_pieceIncidences.mpr ⟨mem_univ _,edge.left_mem⟩
    · exact mem_pieceIncidences.mpr ⟨mem_univ _,edge.right_mem⟩
  · exact (mem_filter.mp degree).1

/-- An edge records an actual crossed path comparison on copied vertices,
or an actual crossed degree comparison at two raw piece incidences. -/
def DegreeFirstCutConflict {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ)
    (a b : ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D) : Prop :=
  let raw := listRegularizedPaths paths D L
  OppositeWidthConflict (splitListVertices paths D) raw Sigma.fst a b ∨
    (a.2 ∈ raw a.1 ∧ b.2 ∈ raw b.1 ∧
      OppositeDegreeCutConflict paths D (a.1.fst,a.2) (b.1.fst,b.2))

theorem DegreeFirstCutConflict.left_mem {n p : ℕ} {paths : Fin p → List (Fin n)} {D L : ℕ}
    {a b} (edge : DegreeFirstCutConflict paths D L a b) : a.2 ∈ listRegularizedPaths paths D L a.1 := by
  rcases edge with path | degree
  · exact path.left_mem
  · exact degree.1

theorem DegreeFirstCutConflict.right_mem {n p : ℕ} {paths : Fin p → List (Fin n)} {D L : ℕ}
    {a b} (edge : DegreeFirstCutConflict paths D L a b) : b.2 ∈ listRegularizedPaths paths D L b.1 := by
  rcases edge with path | degree
  · exact path.right_mem
  · exact degree.2.1

theorem DegreeFirstCutConflict.original_corner {n p : ℕ} {paths : Fin p → List (Fin n)} {D L : ℕ}
    {a b} (edge : DegreeFirstCutConflict paths D L a b) : a.2.fst = b.2.fst := by
  rcases edge with path | degree
  · exact congrArg Sigma.fst path.1
  · exact degree.2.2.2.2.1

theorem DegreeFirstCutConflict.partner {n p : ℕ} {paths : Fin p → List (Fin n)} {D L : ℕ}
    (simple : ∀ i, (paths i).Nodup) {a b} (edge : DegreeFirstCutConflict paths D L a b) :
    LaterReversePartner paths a.2.fst a.1.fst b.1.fst := by
  rcases edge with path | degree
  · let copies := splitListVertices paths D
    let raw := listRegularizedPaths paths D L
    let J := ListBlockIndex copies L
    let parent (j : J) := j.fst
    have rawSub (i : J) : (raw i).Sublist (copies (parent i)) := List.filter_sublist
    have steps {i : J} {x y : ListVertexBlockIndex paths D}
        (h : Before raw i x y) : Before copies (parent i) x y :=
      listBefore_of_sublist (paths := fun j : J => copies (parent j)) (cut := raw)
        (splitListVertices_simple paths D (parent i) (simple (parent i))) (rawSub i) h
    obtain ⟨arrives,x,forward,backward⟩ := path.partner (fun {_ _ _} => steps)
    exact ⟨arrives,x.fst,splitListVertices_step (simple a.1.fst) forward,
      splitListVertices_step (simple b.1.fst) backward⟩
  · exact degree.2.2.2.2.2.2

theorem DegreeFirstCutConflict.out_unique {n p : ℕ} {paths : Fin p → List (Fin n)} {D L : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    {a b c} (ab : DegreeFirstCutConflict paths D L a b) (ac : DegreeFirstCutConflict paths D L a c) :
    b = c := by
  have parent : b.1.fst = c.1.fst :=
    laterReversePartner_unique free (by decide) (ab.partner simple) (ac.partner simple)
  have original : b.2.fst = c.2.fst := ab.original_corner.symm.trans ac.original_corner
  have bOn := (mem_localPathBlock.mp ab.right_mem).1
  have cOn := (mem_localPathBlock.mp ac.right_mem).1
  have cOnSame : c.2 ∈ splitListVertices paths D b.1.fst := parent.symm ▸ cOn
  have copied : b.2 = c.2 := vertexBlock_eq_of_same_label original
    (le_antisymm (splitListVertices_block_mono original le_rfl bOn cOnSame)
      (splitListVertices_block_mono original.symm le_rfl cOnSame bOn))
  have piece : b.1 = c.1 := by
    by_contra different
    exact splitListPaths_disjoint different parent ab.right_mem (copied.symm ▸ ac.right_mem)
  exact Prod.ext piece copied

/-- Every original incidence belongs to a width block of its row. -/
theorem list_mem_has_path_block {I V : Type*} [LinearOrder V] {paths : I → List V}
    {i : I} {v : V} (simple : (paths i).Nodup) (onRow : v ∈ paths i) (L : ℕ) :
    ∃ j : ListBlockIndex paths L, j.fst = i ∧ v ∈ splitListPaths paths L j := by
  let block : ListBlockIndex paths L := ⟨i,⟨(paths i).idxOf v/L,by
    unfold blockCount
    rw [List.toFinset_card_of_nodup simple]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (List.idxOf_lt_length_of_mem onRow).le)⟩⟩
  exact ⟨block,rfl,mem_localPathBlock.mpr ⟨onRow,rfl⟩⟩

private theorem one_of_opposite_colors {a b c : Bool} (different : a ≠ b) : a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

set_option maxHeartbeats 800000 in
/-- Any deletion covering the two actual cut relations preserves half-five
exclusion when degrees are split before paths. -/
theorem eraseDegreeFirstConflicts_halfFree {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5) (D L : ℕ)
    (deleted : Finset (ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D))
    (deletedRaw : deleted ⊆ pieceIncidences (listRegularizedPaths paths D L) univ)
    (cover : ∀ {a b}, DegreeFirstCutConflict paths D L a b → a ∈ deleted ∨ b ∈ deleted) :
    HalfBridgeFree (Before (erasePieceIncidences (listRegularizedPaths paths D L) deleted)) 5 := by
  classical
  let copies := splitListVertices paths D
  let raw := listRegularizedPaths paths D L
  let J := ListBlockIndex copies L
  let V := ListVertexBlockIndex paths D
  let parent (j : J) := j.fst
  let project (a : J × V) := (parent a.1,a.2)
  let degreeDeleted := deleted.image project
  let degreeRows := erasePieceIncidences copies degreeDeleted
  let clean := erasePieceIncidences raw deleted
  have copySimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have rawSimple (i : J) : (raw i).Nodup := listRegularizedPaths_simple paths simple D L i
  have cleanSimple (i : J) : (clean i).Nodup :=
    (erasePieceIncidences_sublist raw deleted i).nodup (rawSimple i)
  have rawSub (i : J) : (raw i).Sublist (copies (parent i)) := List.filter_sublist
  have rawStep {i x y} (step : Before raw i x y) : Before copies (parent i) x y :=
    listBefore_of_sublist (paths := fun j : J => copies (parent j)) (copySimple (parent i)) (rawSub i) step
  have cleanStep {i x y} (step : Before clean i x y) : Before raw i x y :=
    listBefore_of_sublist (rawSimple i) (erasePieceIncidences_sublist raw deleted i) step
  have liftDegree {a b : Fin p × V} (edge : OppositeDegreeCutConflict paths D a b) :
      a ∈ degreeDeleted ∨ b ∈ degreeDeleted := by
    obtain ⟨j,jParent,inA⟩ := list_mem_has_path_block (copySimple a.1) edge.1 L
    obtain ⟨k,kParent,inB⟩ := list_mem_has_path_block (copySimple b.1) edge.2.1 L
    have aEq : project (j,a.2) = a := Prod.ext jParent rfl
    have bEq : project (k,b.2) = b := Prod.ext kParent rfl
    have lifted : DegreeFirstCutConflict paths D L (j,a.2) (k,b.2) := by
      apply Or.inr
      refine ⟨inA,inB,?_⟩
      change OppositeDegreeCutConflict paths D (project (j,a.2)) (project (k,b.2))
      rwa [aEq,bEq]
    exact (cover lifted).imp (fun h => mem_image.mpr ⟨_,h,aEq⟩) (fun h => mem_image.mpr ⟨_,h,bEq⟩)
  have rowFree : HalfBridgeFree (Before degreeRows) 5 :=
    eraseDegreeCutConflicts_halfFree simple free D degreeDeleted (fun {_ _} => liftDegree)
  have keepParent {j : J} {x : V} (present : x ∈ clean j) : x ∈ degreeRows (parent j) := by
    obtain ⟨onRaw,kept⟩ := mem_erasePieceIncidences.mp present
    refine mem_erasePieceIncidences.mpr ⟨(rawSub j).subset onRaw,?_⟩
    intro removed
    obtain ⟨b,bRemoved,same⟩ := mem_image.mp removed
    have sameVertex : b.2 = x := congrArg Prod.snd same
    have sameParent : parent b.1 = parent j := congrArg Prod.fst same
    have bRaw : x ∈ raw b.1 := sameVertex ▸ (mem_pieceIncidences.mp (deletedRaw bRemoved)).2
    have samePiece : b.1 = j := by
      by_contra different
      exact splitListPaths_disjoint different sameParent bRaw onRaw
    exact kept ((Prod.ext samePiece sameVertex : b = (j,x)) ▸ bRemoved)
  have parentStep {i x y} (step : Before clean i x y) : Before degreeRows (parent i) x y :=
    (listBefore_sublist_iff (copySimple (parent i)) (erasePieceIncidences_sublist copies degreeDeleted (parent i))
      (keepParent step.1) (keepParent step.2.1)).mpr (rawStep (cleanStep step))
  have liftRowStep {i x y} (step : Before degreeRows i x y) : Before copies i x y :=
    listBefore_of_sublist (copySimple i) (erasePieceIncidences_sublist copies degreeDeleted i) step
  have apart {i j : J} {x : V}
      (diff : i ≠ j) (same : parent i = parent j) (left : x ∈ clean i) (right : x ∈ clean j) : False :=
    splitListPaths_disjoint diff same (mem_erasePieceIncidences.mp left).1 (mem_erasePieceIncidences.mp right).1
  have noConflict {a b : J × V} (edge : OppositeWidthConflict degreeRows clean parent a b) : False := by
    have lift : OppositeWidthConflict copies raw parent a b := by
      rcases edge with ⟨same,older,x,⟨j,diff,pSame,xEarly,on,xy,yx⟩ | ⟨j,diff,pSame,xLate,on,xy,yx⟩⟩
      · exact ⟨same,older,x,Or.inl ⟨j,diff,pSame,(mem_erasePieceIncidences.mp xEarly).1,
          (mem_erasePieceIncidences.mp on).1,liftRowStep xy,cleanStep yx⟩⟩
      · exact ⟨same,older,x,Or.inr ⟨j,diff,pSame,(mem_erasePieceIncidences.mp xLate).1,
          (mem_erasePieceIncidences.mp on).1,cleanStep xy,liftRowStep yx⟩⟩
    exact (cover (Or.inl lift)).elim (mem_erasePieceIncidences.mp edge.left_mem).2 (mem_erasePieceIncidences.mp edge.right_mem).2
  have monotone : Monotone parent := block_parent_mono (fun i => (copies i).toFinset) L
  have keptFree := eraseOppositeWidthConflicts_halfFree rowFree cleanSimple monotone
    (fun {_ _ _} => parentStep) (fun {_ _ _} => apart) (∅ : Finset (J × V))
    (fun {_ _} edge => (noConflict edge).elim)
  have noDeletion : erasePieceIncidences clean (∅ : Finset (J × V)) = clean := by
    funext i
    unfold erasePieceIncidences
    simp
  rw [noDeletion] at keptFree
  exact keptFree

/-- One original reverse-partner color covers both actual cut sets. -/
theorem halfFiveDegreeFirstDeletion_covers {n p : ℕ} {paths : Fin p → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    {D L : ℕ} {a b} (edge : DegreeFirstCutConflict paths D L a b) (c : Bool) :
    a ∈ halfFiveDegreeFirstDeletion paths D L c ∨ b ∈ halfFiveDegreeFirstDeletion paths D L c := by
  classical
  have mark : a ∈ halfFiveDegreeFirstAffected paths D L ∧ b ∈ halfFiveDegreeFirstAffected paths D L := by
    rcases edge with path | ⟨aOn,bOn,degree⟩
    · exact ⟨mem_union_left _ (mem_filter.mpr ⟨mem_univ _,Or.inl ⟨b,path⟩⟩),
        mem_union_left _ (mem_filter.mpr ⟨mem_univ _,Or.inr ⟨a,path⟩⟩)⟩
    · exact ⟨mem_union_right _ (mem_filter.mpr ⟨mem_pieceIncidences.mpr ⟨mem_univ _,aOn⟩,
          mem_filter.mpr ⟨mem_univ _,Or.inl ⟨(b.1.fst,b.2),degree⟩⟩⟩),
        mem_union_right _ (mem_filter.mpr ⟨mem_pieceIncidences.mpr ⟨mem_univ _,bOn⟩,
          mem_filter.mpr ⟨mem_univ _,Or.inr ⟨(a.1.fst,a.2),degree⟩⟩⟩)⟩
  have different : reversePartnerColor paths a.2.fst a.1.fst ≠ reversePartnerColor paths b.2.fst b.1.fst := by
    rw [← edge.original_corner]
    exact reversePartnerColor_ne free (by decide) (edge.partner simple)
  exact (one_of_opposite_colors (c := c) different).imp
    (fun h => mem_filter.mpr ⟨mark.1,h⟩) (fun h => mem_filter.mpr ⟨mark.2,h⟩)

/-- One original color covers both sets of actual conflicts when the
degree width split precedes the path width split. -/
theorem halfFiveDegreeFirstRepair_halfFree {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5) (D L : ℕ) (c : Bool) :
    HalfBridgeFree (Before (erasePieceIncidences
      (listRegularizedPaths paths D L) (halfFiveDegreeFirstDeletion paths D L c))) 5 :=
  eraseDegreeFirstConflicts_halfFree paths simple free D L _
    ((filter_subset _ _).trans (halfFiveDegreeFirstAffected_subset paths D L))
    (fun {_ _} edge => halfFiveDegreeFirstDeletion_covers simple free edge c)

private theorem mass_le_rectangle_add_losses {I V : Type*} [LinearOrder I] [Fintype I]
    [LinearOrder V] [Fintype V] (rows : I → List V) (simple : ∀ i, (rows i).Nodup)
    (A : Finset V) (B : Finset I) :
    (∑ i, (rows i).length) ≤
      (∑ i : B, (restrictListPaths rows A B i).length) +
      (∑ i ∈ univ \ B, (rows i).length) +
      (∑ v ∈ univ \ A, (occurrences (fun i => (rows i).toFinset) v).card) := by
  classical
  let sets (i : I) := (rows i).toFinset
  let R := ∑ i : B, (restrictListPaths rows A B i).length
  have rowParts : (∑ i ∈ univ \ B, (rows i).length)+(∑ i ∈ B, (rows i).length) =
      ∑ i, (rows i).length := sum_sdiff (subset_univ B)
  have chosen : R = ∑ i ∈ B, (sets i ∩ A).card := calc
    _ = ∑ i : B, (sets i.val ∩ A).card := sum_congr rfl
      (fun i _ => restrictListPath_length (simple i.val) A)
    _ = _ := sum_attach B (fun i => (sets i ∩ A).card)
  have rowVertices : (∑ i ∈ B, (rows i).length) = R+(∑ i ∈ B, (sets i \ A).card) := by
    rw [chosen,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [Nat.add_comm,card_sdiff_add_card_inter]
    exact (List.toFinset_card_of_nodup (simple i)).symm
  have complement : (∑ i, (sets i \ A).card) =
      ∑ v ∈ univ \ A, (occurrences sets v).card := calc
    _ = ∑ v, (occurrences (fun i => sets i \ A) v).card := (sum_occurrences _).symm
    _ = ∑ v, if v ∉ A then (occurrences sets v).card else 0 := by
      apply sum_congr rfl
      intro v _
      by_cases outside : v ∉ A
      · rw [ite_eq_left outside]
        apply congrArg Finset.card
        ext i
        simp [mem_occurrences,Finset.mem_sdiff,outside]
      · rw [ite_eq_right outside,card_eq_zero]
        ext i
        simp [mem_occurrences,Finset.mem_sdiff,outside]
    _ = _ := by
      rw [← sum_filter]
      congr 1
      ext v
      simp
  have loss : (∑ i ∈ B, (sets i \ A).card) ≤ ∑ v ∈ univ \ A, (occurrences sets v).card :=
    (sum_le_sum_of_subset (subset_univ B)).trans_eq complement
  change (∑ i, (rows i).length) ≤ R+(∑ i ∈ univ \ B, (rows i).length)+
    (∑ v ∈ univ \ A, (occurrences sets v).card)
  omega

private theorem degreeFirst_retained_mass {M W R X Y C D : ℕ}
    (positive : 0 < M) (wLow : 119*M ≤ 100*W) (wHigh : W ≤ 2*M)
    (vertexCap : 31*M ≤ 8*C) (pathCap : 31*M ≤ 8*D)
    (vertexLoss : 4*C*X ≤ W^2) (pathLoss : 4*D*Y ≤ W^2)
    (retained : W ≤ 2*R+X+Y) : 251*M ≤ 500*R := by
  have charge {S Z : ℕ} (capacity : 31*M ≤ 8*S) (loss : 4*S*Z ≤ W^2) :
      31*M*Z ≤ 2*W^2 := calc
    _ ≤ (8*S)*Z := Nat.mul_le_mul_right _ capacity
    _ = 2*(4*S*Z) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ loss
  have paid : 31*M*W ≤ 62*M*R+4*W^2 := calc
    _ ≤ (31*M)*(2*R+X+Y) := Nat.mul_le_mul_left _ retained
    _ = 62*M*R+31*M*X+31*M*Y := by ring
    _ ≤ 62*M*R+2*W^2+2*W^2 :=
      Nat.add_le_add (Nat.add_le_add_left (charge vertexCap vertexLoss) _) (charge pathCap pathLoss)
    _ = _ := by ring
  have paidReal : 31*(M:ℝ)*W ≤ 62*(M:ℝ)*R+4*(W:ℝ)^2 := by exact_mod_cast paid
  have low : (119/100)*(M:ℝ) ≤ W := by
    have h : 119*(M:ℝ) ≤ 100*(W:ℝ) := by exact_mod_cast wLow
    linarith
  have high : (W:ℝ) ≤ 2*(M:ℝ) := by exact_mod_cast wHigh
  have monotone := mul_nonneg (sub_nonneg.mpr low)
    (show 0 ≤ 31*(M:ℝ)-4*((W:ℝ)+(119/100)*(M:ℝ)) by linarith)
  have enough : (251*(M:ℝ))*M ≤ (500*(R:ℝ))*M := by
    nlinarith only [paidReal,monotone,sq_nonneg (M:ℝ)]
  apply (Nat.mul_le_mul_right_iff positive).mp
  exact_mod_cast enough

set_option maxHeartbeats 1200000 in
/-- If the actual crossed comparisons of the degree-first split mark at
most 81 percent of the incidences, the witness fits both original
budgets and all four frozen caps with at least one 5000th of the mass. -/
theorem regularization_list_frozen_half_five_of_degree_first_cut_budget {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (bound : let M := ∑ i, (paths i).length
      100*(halfFiveDegreeFirstAffected paths (4*M/n) (4*M/p)).card ≤ 81*M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vBudget,q,qBudget,clean,cleanSimple,legal,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨v,vBudget,q,qBudget,clean,cleanSimple,fun _ small b _ => (legal small).false b,
      mass.trans (Nat.mul_le_mul_right _ (by decide)),upper,caps⟩
  let D := 4*M/n
  let L := 4*M/p
  let J := ListBlockIndex (splitListVertices paths D) L
  let V := ListVertexBlockIndex paths D
  let raw := listRegularizedPaths paths D L
  let affected := halfFiveDegreeFirstAffected paths D L
  let deleted := halfFiveDegreeFirstDeletion paths D L
  let repaired (c : Bool) := erasePieceIncidences raw (deleted c)
  let degree (c : Bool) (v : V) := (occurrences (fun j => (repaired c j).toFinset) v).card
  let rowWeight (j : J) := (repaired false j).length+(repaired true j).length
  let vertexWeight (v : V) := degree false v+degree true v
  let W := ∑ j : J, rowWeight j
  have nDense : 8*n ≤ M := by have maxN := le_max_left n p; omega
  have pDense : 8*p ≤ M := by have maxP := le_max_right n p; omega
  have dPos : 0 < D := (four_average_width hn dense).1
  have lPos : 0 < L := (four_average_width hp long).1
  have vertexCapacity : 31*M ≤ 8*(D*n) := by
    have floor := four_average_width_product hn (M := M)
    change 4*M < D*n+n at floor
    omega
  have pathCapacity : 31*M ≤ 8*(L*p) := by
    have floor := four_average_width_product hp (M := M)
    change 4*M < L*p+p at floor
    omega
  obtain ⟨rawMass,rawLength,rawDegree⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  have rawSimple (j : J) : (raw j).Nodup := listRegularizedPaths_simple paths simple D L j
  have repairedSimple (c : Bool) (j : J) : (repaired c j).Nodup :=
    (erasePieceIncidences_sublist raw (deleted c) j).nodup (rawSimple j)
  have union : deleted false ∪ deleted true = affected := by
    ext a
    cases eq : reversePartnerColor paths a.2.fst a.1.fst <;>
      simp [deleted,affected,halfFiveDegreeFirstDeletion,eq]
  have separate : Disjoint (deleted false) (deleted true) := by
    apply disjoint_left.mpr
    intro a left right
    exact Bool.false_ne_true ((mem_filter.mp left).2.symm.trans (mem_filter.mp right).2)
  have sumWeight : W = (∑ j : J, (repaired false j).length)+(∑ j : J, (repaired true j).length) :=
    sum_add_distrib
  have count (c : Bool) : (∑ j : J, (repaired c j).length)+(deleted c).card = M := by
    have info := erasePieceIncidences_mass_add_loss rawSimple (univ : Finset J) (deleted c)
    change (∑ j : J, (repaired c j).length)+(pieceIncidences raw univ ∩ deleted c).card =
      (∑ j : J, (raw j).length) at info
    have sub : deleted c ⊆ pieceIncidences raw univ :=
      (filter_subset _ _).trans (halfFiveDegreeFirstAffected_subset paths D L)
    rw [inter_eq_right.mpr sub,show (∑ j : J, (raw j).length) = M from rawMass] at info
    exact info
  have exactW : W+affected.card = 2*M := calc
    _ = ((∑ j : J, (repaired false j).length)+(deleted false).card)+
        ((∑ j : J, (repaired true j).length)+(deleted true).card) := by
      rw [← union,card_union_of_disjoint separate,sumWeight]
      exact add_add_add_comm _ _ _ _
    _ = _ := by rw [count false,count true,Nat.two_mul]
  change 100*affected.card ≤ 81*M at bound
  have lowerW : 119*M ≤ 100*W := by omega
  have upperW : W ≤ 2*M := by omega
  have degreeTally (c : Bool) : (∑ v : V, degree c v) = ∑ j : J, (repaired c j).length :=
    (sum_occurrences (fun j => (repaired c j).toFinset)).trans
      (sum_congr rfl (fun j _ => List.toFinset_card_of_nodup (repairedSimple c j)))
  have vertexWeightSum : (∑ v : V, vertexWeight v) = W := by
    change (∑ v : V, (degree false v+degree true v)) = W
    rw [sum_add_distrib,degreeTally false,degreeTally true,← sumWeight]
  have stays {j : J} {v : V} : v ∈ repaired false j ∨ v ∈ repaired true j ↔ v ∈ raw j := by
    change (v ∈ erasePieceIncidences raw (deleted false) j ∨ v ∈ erasePieceIncidences raw (deleted true) j) ↔ _
    simp only [mem_erasePieceIncidences]
    constructor
    · rintro (one | two)
      · exact one.1
      · exact two.1
    · intro here
      by_cases removed : (j,v) ∈ deleted false
      · exact Or.inr ⟨here,fun other => disjoint_left.mp separate removed other⟩
      · exact Or.inl ⟨here,removed⟩
  have rowLower (j : J) : (raw j).length ≤ rowWeight j := by
    have cover : (repaired false j).toFinset ∪ (repaired true j).toFinset = (raw j).toFinset := by
      ext v
      simpa only [mem_union,List.mem_toFinset] using (stays (j := j) (v := v))
    calc
      _ = (raw j).toFinset.card := (List.toFinset_card_of_nodup (rawSimple j)).symm
      _ ≤ (repaired false j).toFinset.card+(repaired true j).toFinset.card := by rw [← cover]; exact card_union_le _ _
      _ = _ := by rw [List.toFinset_card_of_nodup (repairedSimple false j),
        List.toFinset_card_of_nodup (repairedSimple true j)]
  have vertexLower (v : V) : (occurrences (fun j => (raw j).toFinset) v).card ≤ vertexWeight v := by
    have cover : occurrences (fun j => (repaired false j).toFinset) v ∪
        occurrences (fun j => (repaired true j).toFinset) v = occurrences (fun j => (raw j).toFinset) v := by
      ext j
      simpa only [mem_union,mem_occurrences,List.mem_toFinset] using (stays (j := j) (v := v))
    rw [← cover]
    exact card_union_le _ _
  obtain ⟨fullV,fullJ,filledV,remainderV,filledJ,remainderJ⟩ :=
    listRegularizedPaths_full_block_profiles paths simple dPos lPos
  have remV : (univ \ fullV).card ≤ n := by simpa only [Fintype.card_fin] using remainderV.le
  have remJ : (univ \ fullJ).card ≤ p := by simpa only [Fintype.card_fin] using remainderJ.le
  obtain ⟨A,vBudget,trimV⟩ := trim_full_weight_blocks_quadratic_of_lower_bound vertexWeight fullV dPos
    (fun v h => (filledV v h).ge.trans (vertexLower v)) remV (by rw [vertexWeightSum]; omega)
  obtain ⟨B,pBudget,trimJ⟩ := trim_full_weight_blocks_quadratic_of_lower_bound rowWeight fullJ lPos
    (fun j h => (filledJ j h).ge.trans (rowLower j)) remJ (by change W ≤ L*p; omega)
  let X := ∑ v ∈ univ \ A, vertexWeight v
  let Y := ∑ j ∈ univ \ B, rowWeight j
  let kept (c : Bool) := restrictListPaths (repaired c) A B
  let mass (c : Bool) := ∑ j : B, (kept c j).length
  have vertexLoss : 4*(D*n)*X ≤ W^2 := by rw [← vertexWeightSum]; exact trimV
  have pathLoss : 4*(L*p)*Y ≤ W^2 := trimJ
  have retainedBoth : W ≤ mass false+mass true+X+Y := by
    have first := mass_le_rectangle_add_losses (repaired false) (repairedSimple false) A B
    have second := mass_le_rectangle_add_losses (repaired true) (repairedSimple true) A B
    change (∑ j : J, (repaired false j).length) ≤ mass false+
      (∑ j ∈ univ \ B, (repaired false j).length)+(∑ v ∈ univ \ A, degree false v) at first
    change (∑ j : J, (repaired true j).length) ≤ mass true+
      (∑ j ∈ univ \ B, (repaired true j).length)+(∑ v ∈ univ \ A, degree true v) at second
    have xEq : X = (∑ v ∈ univ \ A, degree false v)+(∑ v ∈ univ \ A, degree true v) := sum_add_distrib
    have yEq : Y = (∑ j ∈ univ \ B, (repaired false j).length)+(∑ j ∈ univ \ B, (repaired true j).length) :=
      sum_add_distrib
    omega
  obtain ⟨c,retained⟩ : ∃ c : Bool, W ≤ 2*mass c+X+Y := by
    rcases le_total (mass false) (mass true) with h | h
    · exact ⟨true,by omega⟩
    · exact ⟨false,by omega⟩
  have enough : 251*M ≤ 500*mass c :=
    degreeFirst_retained_mass (hn.trans_le dense) lowerW upperW vertexCapacity pathCapacity vertexLoss pathLoss retained
  let marks := fun j => (repaired c j).toFinset
  have legal : HalfBridgeFree (Before (kept c)) 5 :=
    restrictListPaths_halfFree (repairedSimple c) (halfFiveDegreeFirstRepair_halfFree paths simple free D L c) A B
  have keptSimple (j : B) : (kept c j).Nodup := restrictListPath_nodup (repairedSimple c j.val) A
  have length (j : B) : (kept c j).length ≤ L := by
    rw [show (kept c j).length = (marks j.val ∩ A).card from restrictListPath_length (repairedSimple c j.val) A]
    exact (card_le_card inter_subset_left).trans ((List.toFinset_card_le _).trans
      ((erasePieceIncidences_sublist raw (deleted c) j.val).length_le.trans (rawLength j.val)))
  have originalDegree (v : V) : degree c v ≤ D := by
    refine (card_le_card ?_).trans (rawDegree v)
    intro j hj
    have on : v ∈ repaired c j := List.mem_toFinset.mp ((mem_occurrences (marks := marks)).mp hj)
    exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_erasePieceIncidences.mp on).1)
  have keptDegree (v : A) : (occurrences (fun j => (kept c j).toFinset) v).card ≤ D := by
    rw [show (fun j => (kept c j).toFinset) = rectanglePaths marks A B from
      funext (restrictListPaths_toFinset (repaired c) A B)]
    exact (rectanglePaths_degree_le marks A B v).trans (originalDegree v.val)
  have upper : mass c ≤ M := calc
    _ = ∑ j : B, (rectanglePaths marks A B j).card :=
      sum_congr rfl (fun j _ => (List.toFinset_card_of_nodup (keptSimple j)).symm.trans
        (congrArg Finset.card (restrictListPaths_toFinset (repaired c) A B j)))
    _ ≤ ∑ j : J, (marks j).card := rectanglePaths_mass_le marks A B
    _ ≤ ∑ j : J, (raw j).length := sum_le_sum (fun j _ => (List.toFinset_card_le _).trans
      (erasePieceIncidences_sublist raw (deleted c) j).length_le)
    _ = _ := rawMass
  refine regularization_list_frozen_after_caps_with_ratios_of_mass (half := true) (k := 5)
    (retention := 5000) (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1)
    (kept c) keptSimple legal hn hp dense long (by decide) (by decide) le_rfl le_rfl
    (by simpa only [one_mul,Fintype.card_coe] using vBudget)
    (by simpa only [one_mul,Fintype.card_coe] using pBudget) length keptDegree upper ?_
  change 5002*M ≤ 10000*mass c
  omega

private theorem original_width_trim_loss {M C X : ℕ} (positive : 0 < M)
    (capacity : 31*M ≤ 8*C) (trim : 4*C*X ≤ M^2) : 31*X ≤ 2*M := by
  apply (Nat.mul_le_mul_left_iff positive).mp
  calc
    _ = (31*M)*X := by ring
    _ ≤ (8*C)*X := Nat.mul_le_mul_right _ capacity
    _ = 2*(4*C*X) := by ring
    _ ≤ 2*M^2 := Nat.mul_le_mul_left _ trim
    _ = _ := by ring

set_option maxHeartbeats 1200000 in
/-- A cover of the actual degree-first cut conflicts suffices whenever
it removes at most 37 percent of the original incidences. -/
theorem regularization_list_frozen_half_five_of_degree_first_cover {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (certificate : let M := ∑ i, (paths i).length
      let D := 4*M/n
      let L := 4*M/p
      ∃ deleted : Finset (ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D),
        deleted ⊆ pieceIncidences (listRegularizedPaths paths D L) univ ∧
        100*deleted.card ≤ 37*M ∧
        (∀ {a b}, DegreeFirstCutConflict paths D L a b → a ∈ deleted ∨ b ∈ deleted)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vBudget,q,qBudget,clean,cleanSimple,legal,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨v,vBudget,q,qBudget,clean,cleanSimple,fun _ small b _ => (legal small).false b,
      mass.trans (Nat.mul_le_mul_right _ (by decide)),upper,caps⟩
  let D := 4*M/n
  let L := 4*M/p
  let J := ListBlockIndex (splitListVertices paths D) L
  let V := ListVertexBlockIndex paths D
  let raw := listRegularizedPaths paths D L
  obtain ⟨deleted,deletedSub,deletedCount,cover⟩ := certificate
  let repaired := erasePieceIncidences raw deleted
  let rawSets (j : J) := (raw j).toFinset
  let rawWeight (v : V) := (occurrences rawSets v).card
  have nDense : 8*n ≤ M := by have maxN := le_max_left n p; omega
  have pDense : 8*p ≤ M := by have maxP := le_max_right n p; omega
  have dPos : 0 < D := (four_average_width hn dense).1
  have lPos : 0 < L := (four_average_width hp long).1
  have vertexCapacity : 31*M ≤ 8*(D*n) := by
    have floor := four_average_width_product hn (M := M)
    change 4*M < D*n+n at floor
    omega
  have pathCapacity : 31*M ≤ 8*(L*p) := by
    have floor := four_average_width_product hp (M := M)
    change 4*M < L*p+p at floor
    omega
  obtain ⟨rawMass,rawLength,rawDegree⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  have rawMass' : (∑ j : J, (raw j).length) = M := rawMass
  have rawSimple (j : J) : (raw j).Nodup := listRegularizedPaths_simple paths simple D L j
  have repairedSimple (j : J) : (repaired j).Nodup :=
    (erasePieceIncidences_sublist raw deleted j).nodup (rawSimple j)
  have degreeMass : (∑ v : V, rawWeight v) = M := calc
    _ = ∑ j : J, (rawSets j).card := sum_occurrences rawSets
    _ = ∑ j : J, (raw j).length := sum_congr rfl (fun j _ => List.toFinset_card_of_nodup (rawSimple j))
    _ = _ := rawMass
  obtain ⟨fullV,fullJ,filledV,remainderV,filledJ,remainderJ⟩ :=
    listRegularizedPaths_full_block_profiles paths simple dPos lPos
  have remV : (univ \ fullV).card ≤ n := by simpa only [Fintype.card_fin] using remainderV.le
  have remJ : (univ \ fullJ).card ≤ p := by simpa only [Fintype.card_fin] using remainderJ.le
  obtain ⟨A,vertexBudget,trimV⟩ := trim_full_weight_blocks_quadratic rawWeight fullV dPos filledV remV
    (by rw [degreeMass]; omega)
  obtain ⟨B,pathBudget,trimJ⟩ := trim_full_weight_blocks_quadratic (fun j => (raw j).length) fullJ
    lPos filledJ remJ (by rw [rawMass']; omega)
  let X := ∑ v ∈ univ \ A, rawWeight v
  let Y := ∑ j ∈ univ \ B, (raw j).length
  let kept := restrictListPaths repaired A B
  let R := ∑ j : B, (kept j).length
  have vertexTrim : 4*(D*n)*X ≤ M^2 := by rw [← degreeMass]; exact trimV
  have pathTrim : 4*(L*p)*Y ≤ M^2 := by rw [← rawMass']; exact trimJ
  have massPos := hn.trans_le dense
  have vertexLoss : 31*X ≤ 2*M := original_width_trim_loss massPos vertexCapacity vertexTrim
  have pathLoss : 31*Y ≤ 2*M := original_width_trim_loss massPos pathCapacity pathTrim
  have retained : (∑ j : J, (repaired j).length)+deleted.card = M := by
    have tally := erasePieceIncidences_mass_add_loss rawSimple (univ : Finset J) deleted
    change (∑ j : J, (repaired j).length)+(pieceIncidences raw univ ∩ deleted).card =
      (∑ j : J, (raw j).length) at tally
    rw [inter_eq_right.mpr deletedSub,rawMass'] at tally
    exact tally
  let marks (j : J) := (repaired j).toFinset
  have degreeMonotone (v : V) : (occurrences marks v).card ≤ rawWeight v := by
    apply card_le_card
    intro j on
    have occurrence : v ∈ repaired j := List.mem_toFinset.mp ((mem_occurrences (marks := marks)).mp on)
    exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_erasePieceIncidences.mp occurrence).1)
  have lengthMonotone (j : J) : (repaired j).length ≤ (raw j).length :=
    (erasePieceIncidences_sublist raw deleted j).length_le
  have lostV : (∑ v ∈ univ \ A, (occurrences marks v).card) ≤ X := sum_le_sum fun v _ => degreeMonotone v
  have lostJ : (∑ j ∈ univ \ B, (repaired j).length) ≤ Y := sum_le_sum fun j _ => lengthMonotone j
  have loss := mass_le_rectangle_add_losses repaired repairedSimple A B
  change (∑ j : J, (repaired j).length) ≤ R+(∑ j ∈ univ \ B, (repaired j).length)+
    (∑ v ∈ univ \ A, (occurrences marks v).card) at loss
  have enough : 5002*M ≤ 10000*R := by
    change 100*deleted.card ≤ 37*M at deletedCount
    omega
  have repairedFree : HalfBridgeFree (Before repaired) 5 :=
    eraseDegreeFirstConflicts_halfFree paths simple free D L deleted deletedSub (fun {_ _} => cover)
  have legal : HalfBridgeFree (Before kept) 5 := restrictListPaths_halfFree repairedSimple repairedFree A B
  have keptSimple (j : B) : (kept j).Nodup := restrictListPath_nodup (repairedSimple j.val) A
  have length (j : B) : (kept j).length ≤ L := by
    rw [show (kept j).length = (marks j.val ∩ A).card from restrictListPath_length (repairedSimple j.val) A]
    exact (card_le_card inter_subset_left).trans ((List.toFinset_card_le _).trans
      ((lengthMonotone j.val).trans (rawLength j.val)))
  have degree (v : A) : (occurrences (fun j => (kept j).toFinset) v).card ≤ D := by
    rw [show (fun j => (kept j).toFinset) = rectanglePaths marks A B from
      funext (restrictListPaths_toFinset repaired A B)]
    exact (rectanglePaths_degree_le marks A B v).trans ((degreeMonotone v.val).trans (rawDegree v.val))
  have upper : R ≤ M := calc
    _ = ∑ j : B, (rectanglePaths marks A B j).card :=
      sum_congr rfl (fun j _ => (List.toFinset_card_of_nodup (keptSimple j)).symm.trans
        (congrArg Finset.card (restrictListPaths_toFinset repaired A B j)))
    _ ≤ ∑ j : J, (marks j).card := rectanglePaths_mass_le marks A B
    _ ≤ ∑ j : J, (raw j).length := sum_le_sum fun j _ => (List.toFinset_card_le _).trans (lengthMonotone j)
    _ = _ := rawMass
  exact regularization_list_frozen_after_caps_with_ratios_of_mass (half := true) (k := 5)
    (retention := 5000) (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1)
    kept keptSimple legal hn hp dense long (by decide) (by decide) le_rfl le_rfl
    (by simpa only [one_mul,Fintype.card_coe] using vertexBudget)
    (by simpa only [one_mul,Fintype.card_coe] using pathBudget) length degree upper enough

end OnlineReachabilityPreservers
