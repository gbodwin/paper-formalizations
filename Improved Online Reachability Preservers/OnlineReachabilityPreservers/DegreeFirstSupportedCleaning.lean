import OnlineReachabilityPreservers.DegreeFirstRectangleCleaning

/-! A cut comparison requires its two shared witness incidences. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

variable {n p : ℕ}

/-- The endpoints and both occurrences of the reversing witness must
lie in the retained support. At a degree cut the witness is the same
degree copy in both rows. At a path cut it is in a different piece of
one parent and in the endpoint piece of the other parent. -/
def SupportedDegreeFirstConflict (paths : Fin p → List (Fin n)) (D L : ℕ)
    (support : Finset (ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D))
    (a b : ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D) : Prop :=
  let copies := splitListVertices paths D
  let raw := listRegularizedPaths paths D L
  a ∈ support ∧ b ∈ support ∧ a.1.fst < b.1.fst ∧
    ∃ x q r, q.fst = a.1.fst ∧ r.fst = b.1.fst ∧ (q,x) ∈ support ∧ (r,x) ∈ support ∧
      Before copies a.1.fst x a.2 ∧ Before copies b.1.fst b.2 x ∧
      ((a.2.fst = b.2.fst ∧ a.2.snd.val ≠ b.2.snd.val) ∨
        (a.2 = b.2 ∧ ((q ≠ a.1 ∧ Before raw b.1 b.2 x) ∨
          (r ≠ b.1 ∧ Before raw a.1 x a.2))))

theorem SupportedDegreeFirstConflict.toCutConflict {paths : Fin p → List (Fin n)} {D L : ℕ}
    (simple : ∀ i, (paths i).Nodup) {support}
    (valid : support ⊆ pieceIncidences (listRegularizedPaths paths D L) univ) {a b}
    (edge : SupportedDegreeFirstConflict paths D L support a b) :
    DegreeFirstCutConflict paths D L a b := by
  obtain ⟨aOn,bOn,arrives,x,q,r,qParent,rParent,qOn,rOn,forward,backward,kind⟩ := edge
  have left := (mem_pieceIncidences.mp (valid aOn)).2
  have right := (mem_pieceIncidences.mp (valid bOn)).2
  rcases kind with ⟨same,different⟩ | ⟨same,⟨qDiff,back⟩ | ⟨rDiff,ahead⟩⟩
  · refine Or.inr ⟨left,right,(mem_localPathBlock.mp left).1,(mem_localPathBlock.mp right).1,
      same,different,arrives,x.fst,splitListVertices_step (simple _) forward,?_⟩
    exact same.symm ▸ splitListVertices_step (simple _) backward
  · exact Or.inl ⟨same,arrives,x,Or.inl
      ⟨q,qDiff,qParent,(mem_pieceIncidences.mp (valid qOn)).2,left,forward,back⟩⟩
  · exact Or.inl ⟨same,arrives,x,Or.inr
      ⟨r,rDiff,rParent,(mem_pieceIncidences.mp (valid rOn)).2,right,ahead,backward⟩⟩

set_option maxHeartbeats 1200000 in
/-- After restricting to a support, it suffices to cover the comparisons
with both occurrences of the other corner still in that support. -/
theorem eraseDegreeFirstSupportedConflicts_halfFree (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5) (D L : ℕ)
    (support cover : Finset (ListBlockIndex (splitListVertices paths D) L × ListVertexBlockIndex paths D))
    (covers : ∀ {a b}, SupportedDegreeFirstConflict paths D L support a b → a ∈ cover ∨ b ∈ cover) :
    HalfBridgeFree (Before (erasePieceIncidences (listRegularizedPaths paths D L)
      (pieceIncidences (listRegularizedPaths paths D L) univ \ (support \ cover)))) 5 := by
  classical
  let copies := splitListVertices paths D
  let raw := listRegularizedPaths paths D L
  let J := ListBlockIndex copies L
  let V := ListVertexBlockIndex paths D
  let parent (j : J) := j.fst
  let project (a : J × V) := (parent a.1,a.2)
  let kept := support \ cover
  let deleted := pieceIncidences raw univ \ kept
  let parentDeleted := deleted.image project
  let degreeRows := erasePieceIncidences copies parentDeleted
  let clean := erasePieceIncidences raw deleted
  change HalfBridgeFree (Before clean) 5
  have copySimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have rawSimple (j : J) : (raw j).Nodup := listRegularizedPaths_simple paths simple D L j
  have cleanSimple (j : J) : (clean j).Nodup :=
    (erasePieceIncidences_sublist raw deleted j).nodup (rawSimple j)
  have rawStep {j x y} (step : Before raw j x y) : Before copies (parent j) x y :=
    listBefore_of_sublist (paths := fun j : J => copies (parent j)) (copySimple (parent j)) List.filter_sublist step
  have cleanStep {j x y} (step : Before clean j x y) : Before raw j x y :=
    listBefore_of_sublist (rawSimple j) (erasePieceIncidences_sublist raw deleted j) step
  have degreeStep {i x y} (step : Before degreeRows i x y) : Before copies i x y :=
    listBefore_of_sublist (copySimple i) (erasePieceIncidences_sublist copies parentDeleted i) step
  have rawKept {j : J} {x : V} (on : x ∈ clean j) : (j,x) ∈ kept := by
    obtain ⟨rawOn,notDeleted⟩ := mem_erasePieceIncidences.mp on
    by_contra! outside
    exact notDeleted (mem_sdiff.mpr ⟨mem_pieceIncidences.mpr ⟨mem_univ _,rawOn⟩,outside⟩)
  have notConflict {a b : J × V} (aOn : a ∈ kept) (bOn : b ∈ kept)
      (edge : SupportedDegreeFirstConflict paths D L support a b) : False :=
    (covers edge).elim (mem_sdiff.mp aOn).2 (mem_sdiff.mp bOn).2
  have supportOf {a : J × V} (on : a ∈ kept) : a ∈ support := (mem_sdiff.mp on).1
  have pieceOf {i : Fin p} {x : V} (on : x ∈ degreeRows i) :
      ∃ j : J, parent j = i ∧ (j,x) ∈ kept := by
    obtain ⟨old,notDeleted⟩ := mem_erasePieceIncidences.mp on
    obtain ⟨j,jParent,here⟩ := list_mem_has_path_block (copySimple i) old L
    refine ⟨j,jParent,?_⟩
    by_contra! outside
    have erased : (j,x) ∈ deleted := mem_sdiff.mpr ⟨mem_pieceIncidences.mpr ⟨mem_univ _,here⟩,outside⟩
    exact notDeleted (mem_image.mpr ⟨_,erased,Prod.ext jParent rfl⟩)
  have apartRaw {i j : J} {x : V} (diff : i ≠ j) (same : parent i = parent j)
      (one : x ∈ raw i) (two : x ∈ raw j) : False :=
    splitListPaths_disjoint diff same one two
  have keepsParent {j : J} {x : V} (on : x ∈ clean j) : x ∈ degreeRows (parent j) := by
    obtain ⟨onRaw,notDeleted⟩ := mem_erasePieceIncidences.mp on
    refine mem_erasePieceIncidences.mpr ⟨(mem_localPathBlock.mp onRaw).1,?_⟩
    intro erased
    obtain ⟨⟨i,y⟩,iDeleted,equal⟩ := mem_image.mp erased
    have same : parent i = parent j := congrArg Prod.fst equal
    have vertex : y = x := congrArg Prod.snd equal
    subst y
    have iRaw : x ∈ raw i := (mem_pieceIncidences.mp (mem_sdiff.mp iDeleted).1).2
    have piece : i = j := by_contra fun diff => apartRaw diff same iRaw onRaw
    exact notDeleted (piece ▸ iDeleted)
  have parentStep {j x y} (step : Before clean j x y) : Before degreeRows (parent j) x y :=
    (listBefore_sublist_iff (copySimple (parent j)) (erasePieceIncidences_sublist copies parentDeleted (parent j))
      (keepsParent step.1) (keepsParent step.2.1)).mpr (rawStep (cleanStep step))
  have safeDegree : ∀ {a b : Fin p} {v w x : ListVertexBlockIndex paths D}, a < b → v.fst = w.fst →
      Before degreeRows a x v → Before degreeRows b w x → v = w := by
    intro a b v w x arrives same forward backward
    by_contra! distinct
    have blocks : v.snd.val ≠ w.snd.val := fun h => distinct (vertexBlock_eq_of_same_label same h)
    obtain ⟨j,jParent,jOn⟩ := pieceOf forward.2.1
    obtain ⟨k,kParent,kOn⟩ := pieceOf backward.1
    obtain ⟨q,qParent,qOn⟩ := pieceOf forward.1
    obtain ⟨r,rParent,rOn⟩ := pieceOf backward.2.1
    have ordered : j.fst < k.fst := by
      change parent j < parent k
      rwa [jParent,kParent]
    have fwd : Before copies j.fst x v := by
      change Before copies (parent j) x v
      rw [jParent]
      exact degreeStep forward
    have bwd : Before copies k.fst w x := by
      change Before copies (parent k) w x
      rw [kParent]
      exact degreeStep backward
    apply notConflict jOn kOn
    exact ⟨supportOf jOn,supportOf kOn,ordered,
      x,q,r,qParent.trans jParent.symm,rParent.trans kParent.symm,supportOf qOn,supportOf rOn,
      fwd,bwd,Or.inl ⟨same,blocks⟩⟩
  have degreeFree : HalfBridgeFree (Before degreeRows) 5 :=
    eraseDegreeBlocks_halfFive_of_no_live_return simple free D parentDeleted (fun {_ _ _ _ _} => safeDegree)
  have noPathConflict {a b : J × V} (edge : OppositeWidthConflict degreeRows clean parent a b) : False := by
    have aOn := rawKept edge.left_mem
    have bOn := rawKept edge.right_mem
    apply notConflict aOn bOn
    obtain ⟨same,earlier,x,⟨q,qDiff,qParent,qOn,_,forward,back⟩ | ⟨r,rDiff,rParent,rOn,_,ahead,backward⟩⟩ := edge
    · exact ⟨supportOf aOn,supportOf bOn,earlier,x,q,b.1,qParent,rfl,
        supportOf (rawKept qOn),supportOf (rawKept back.2.1),
        degreeStep forward,rawStep (cleanStep back),Or.inr ⟨same,Or.inl ⟨qDiff,cleanStep back⟩⟩⟩
    · exact ⟨supportOf aOn,supportOf bOn,earlier,x,a.1,r,rfl,rParent,
        supportOf (rawKept ahead.1),supportOf (rawKept rOn),
        rawStep (cleanStep ahead),degreeStep backward,Or.inr ⟨same,Or.inr ⟨rDiff,cleanStep ahead⟩⟩⟩
  have monotone : Monotone parent := block_parent_mono (fun i => (copies i).toFinset) L
  have halfFree := eraseOppositeWidthConflicts_halfFree degreeFree cleanSimple monotone
    (fun {_ _ _} => parentStep)
    (fun {_ _ _} diff same one two => apartRaw diff same
      (mem_erasePieceIncidences.mp one).1 (mem_erasePieceIncidences.mp two).1)
    (∅ : Finset (J × V)) (fun {_ _} edge => (noPathConflict edge).elim)
  have identity : erasePieceIncidences clean (∅ : Finset (J × V)) = clean := by
    funext j
    simp [erasePieceIncidences]
  rwa [identity] at halfFree

/-- Only conflicts with both occurrences of their witness in the
chosen rectangle contribute to the matching bound. -/
theorem regularization_list_frozen_half_five_of_supported_degree_first_rectangle {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (bound : let M := ∑ i, (paths i).length
      let D := 4*M/n
      let L := 4*M/p
      ∃ A : Finset (ListVertexBlockIndex paths D), A.card ≤ n ∧
      ∃ B : Finset (ListBlockIndex (splitListVertices paths D) L), B.card ≤ p ∧
        let support := degreeFirstRectangleIncidences paths D L A B
        ∀ matching, CutMatching (SupportedDegreeFirstConflict paths D L support) support matching →
          (M:ℝ)/5000+(M:ℝ)/(4*(n:ℝ))*A.card+(M:ℝ)/(4*(p:ℝ))*B.card+matching.card ≤
            (degreeFirstRectangleIncidences paths D L A B).card) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let J := ListBlockIndex (splitListVertices paths D) L
  let V := ListVertexBlockIndex paths D
  obtain ⟨A,vertexBudget,B,pathBudget,matchingBound⟩ := bound
  let support := degreeFirstRectangleIncidences paths D L A B
  let edge := SupportedDegreeFirstConflict paths D L support
  let rank (a : J × V) : ℕ := a.1.fst.val
  have supportSub : support ⊆ pieceIncidences (listRegularizedPaths paths D L) univ := filter_subset _ _
  have ordered {a b} (ab : edge a b) : rank a < rank b := ab.2.2.1
  have outUnique {a b c} (ab : edge a b) (ac : edge a c) : b = c :=
    DegreeFirstCutConflict.out_unique simple free (ab.toCutConflict simple supportSub) (ac.toCutConflict simple supportSub)
  obtain ⟨cover,coverSub,matching,count,covers,matched⟩ :=
    exists_cut_cover_and_matching edge rank (fun {_ _} => ordered) (fun {_ _ _} => outUnique) support
  have valid {a b} (ab : edge a b) : a ∈ cover ∨ b ∈ cover := covers a ab.1 b ab.2.1 ab
  refine regularization_list_frozen_half_five_after_rectangle_cover paths simple hn hp dense long
    A vertexBudget B pathBudget cover coverSub
    (eraseDegreeFirstSupportedConflicts_halfFree paths simple free D L support cover (fun {_ _} => valid)) ?_
  rw [count]
  exact matchingBound matching matched

end OnlineReachabilityPreservers
