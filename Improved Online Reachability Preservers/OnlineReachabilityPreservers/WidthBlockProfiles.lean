import OnlineReachabilityPreservers.LocalBalancedRegularization

/-! The full blocks and remainders in the degree and path width splits. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

private def fullBlockPosition {total w j : ℕ} (positive : 0 < w) (full : j < total/w) (offset : Fin w) : Fin total :=
  ⟨j*w+offset.val,by
    have last := (Nat.le_div_iff_mul_le positive).mp (show j+1 ≤ total/w from full)
    rw [Nat.add_mul,Nat.one_mul] at last
    exact (Nat.add_lt_add_left offset.isLt _).trans_le last⟩

private theorem fullBlockPosition_quotient {total w j : ℕ} (positive : 0 < w) (full : j < total/w) (offset : Fin w) :
    (fullBlockPosition positive full offset).val/w = j := by
  change (j*w+offset.val)/w = j
  rw [Nat.add_comm (j*w),Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt offset.isLt,Nat.zero_add]

private theorem fullBlockPosition_injective {total w j : ℕ} (positive : 0 < w) (full : j < total/w) :
    Function.Injective (fullBlockPosition positive full) := by
  intro a b eq
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val eq)

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

private noncomputable def orderedSetPositions (S : Finset V) : S ≃ Fin S.card := by
  classical
  let f (x : S) : Fin S.card := ⟨(predecessors S x.val).card,by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,?_⟩
    intro equal
    have member : x.val ∈ predecessors S x.val := equal.symm ▸ x.property
    simp [predecessors] at member⟩
  have injective : Function.Injective f := fun x y equal =>
    Subtype.ext (predecessor_count_injective S x.property y.property (congrArg Fin.val equal))
  let labels : S ≃ Fin S.card := (Fintype.equivFin _).trans (finCongr (Fintype.card_coe S))
  have onto := Finite.surjective_of_injective (injective.comp labels.symm.injective)
  exact Equiv.ofBijective f ⟨injective,fun y => by obtain ⟨j,eq⟩ := onto y; exact ⟨labels.symm j,eq⟩⟩

private theorem orderedSetPositions_value (S : Finset V) (x : S) :
    (orderedSetPositions S x).val = (predecessors S x.val).card := rfl

/-- An ordered-set block before the remainder has exactly the fixed width. -/
theorem orderBlock_card_of_full (S : Finset V) {w j : ℕ} (positive : 0 < w) (full : j < S.card/w) :
    (orderBlock S w j).card = w := by
  classical
  let f (offset : Fin w) := (orderedSetPositions S).symm (fullBlockPosition positive full offset)
  have rank (offset : Fin w) : (predecessors S (f offset).val).card =
      (fullBlockPosition positive full offset).val := by
    rw [← orderedSetPositions_value S,show (orderedSetPositions S) (f offset) =
      fullBlockPosition positive full offset from Equiv.apply_symm_apply _ _]
  have filled : w ≤ (orderBlock S w j).card := by
    calc
      w = (univ : Finset (Fin w)).card := by simp
      _ ≤ (orderBlock S w j).card := by
        apply card_le_card_of_injOn (fun offset : Fin w => (f offset).val)
        · intro offset _
          refine mem_filter.mpr ⟨(f offset).property,?_⟩
          rw [rank]
          exact fullBlockPosition_quotient positive full offset
        · intro a _ b _ eq
          exact fullBlockPosition_injective positive full ((orderedSetPositions S).symm.injective (Subtype.ext eq))
  exact le_antisymm (orderBlock_card S positive j) filled

omit [LinearOrder I] in
private theorem localPathBlock_card_of_full (path : List V) (simple : path.Nodup) {w j : ℕ}
    (positive : 0 < w) (full : j < path.length/w) : w ≤ (localPathBlock path w j).length := by
  have nodup : (localPathBlock path w j).Nodup := List.filter_sublist.nodup simple
  rw [← List.toFinset_card_of_nodup nodup]
  let item (offset : Fin w) := path[(fullBlockPosition positive full offset).val]'(fullBlockPosition positive full offset).isLt
  have index (offset : Fin w) : path.idxOf (item offset) = (fullBlockPosition positive full offset).val :=
    simple.idxOf_getElem _ _
  calc
    w = (univ : Finset (Fin w)).card := by simp
    _ ≤ (localPathBlock path w j).toFinset.card := by
      apply card_le_card_of_injOn item
      · intro offset _
        apply List.mem_toFinset.mpr
        refine mem_localPathBlock.mpr ⟨List.getElem_mem _,?_⟩
        rw [index]
        exact fullBlockPosition_quotient positive full offset
      · intro a _ b _ eq
        have same := congrArg (List.idxOf · path) eq
        rw [index,index] at same
        exact fullBlockPosition_injective positive full (Fin.ext same)

/-- All but the last allocated slot for each parent are filled. -/
noncomputable def nonfinalWidthBlocks (sets : I → Finset V) (w : ℕ) : Finset (BlockIndex sets w) := by
  classical
  exact univ.filter fun block => block.snd.val < (sets block.fst).card/w

omit [LinearOrder V] in
/-- The one possible remainder slot per parent is the exact complement. -/
theorem nonfinalWidthBlocks_remainders (sets : I → Finset V) (w : ℕ) :
    (univ \ nonfinalWidthBlocks sets w).card = Fintype.card I := by
  classical
  let last : I ↪ BlockIndex sets w := ⟨fun i => ⟨i,Fin.last ((sets i).card/w)⟩,
    fun _ _ eq => congrArg Sigma.fst eq⟩
  have same : univ \ nonfinalWidthBlocks sets w = univ.map last := by
    apply Finset.ext
    intro block
    rw [mem_sdiff,mem_map]
    simp only [mem_univ,true_and,nonfinalWidthBlocks,mem_filter]
    constructor
    · intro notFull
      have divided : block.snd = Fin.last ((sets block.fst).card/w) := by
        apply Fin.ext
        change block.snd.val = (sets block.fst).card/w
        have within : block.snd.val < (sets block.fst).card/w+1 := block.snd.isLt
        omega
      have sameParent : last block.fst = (⟨block.fst,block.snd⟩ : BlockIndex sets w) :=
        congrArg (Sigma.mk block.fst) divided.symm
      exact ⟨block.fst,sameParent.trans (by cases block; rfl)⟩
    · rintro ⟨i,equal⟩
      rw [← equal]
      exact lt_irrefl ((sets i).card/w)
  rw [same,card_map,card_univ]

private theorem splitVertices_full_degree (paths : I → Finset V) {w : ℕ} (positive : 0 < w)
    (v : VertexBlockIndex paths w) (full : v.snd.val < (occurrences paths v.fst).card/w) :
    (occurrences (splitVertices paths w) v).card = w := by
  have lower : (orderBlock (occurrences paths v.fst) w v.snd.val).card ≤
      (occurrences (splitVertices paths w) v).card := by
    apply card_le_card
    intro i member
    obtain ⟨on,idx⟩ := mem_filter.mp member
    let original : paths i := ⟨v.fst,mem_occurrences.mp on⟩
    have copied : vertexCopy paths w i original = v := by
      rcases v with ⟨x,j⟩
      exact congrArg (Sigma.mk x) (Fin.ext idx)
    exact mem_occurrences.mpr (mem_map.mpr ⟨original,mem_attach _ _,copied⟩)
  rw [orderBlock_card_of_full _ positive full] at lower
  exact le_antisymm (splitVertices_degree paths positive v) lower

omit [LinearOrder I] in
private theorem splitListPaths_degree_lower (paths : I → List V) (simple : ∀ i, (paths i).Nodup) {w : ℕ} (v : V) :
    (occurrences (fun i => (paths i).toFinset) v).card ≤
      (occurrences (fun j => (splitListPaths paths w j).toFinset) v).card := by
  classical
  let original := occurrences (fun i => (paths i).toFinset) v
  let copied := occurrences (fun j => (splitListPaths paths w j).toFinset) v
  have onRow (i : original) : v ∈ paths i.val := List.mem_toFinset.mp
    ((mem_occurrences (marks := fun k => (paths k).toFinset)).mp i.property)
  let image (i : original) : ListBlockIndex paths w := ⟨i.val,⟨(paths i.val).idxOf v/w,by
    unfold blockCount
    rw [List.toFinset_card_of_nodup (simple i.val)]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (List.idxOf_lt_length_of_mem (onRow i)).le)⟩⟩
  let charge (i : original) : copied := ⟨image i,mem_occurrences.mpr
    (List.mem_toFinset.mpr (mem_localPathBlock.mpr ⟨onRow i,rfl⟩))⟩
  have injective : Function.Injective charge := fun _ _ eq =>
    Subtype.ext (congrArg (fun j : copied => j.val.fst) eq)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective charge injective

variable [Fintype V]

/-- Every nonfinal slot in the two width splits has full degree or full
length. Each original vertex and row contributes one possible remainder. -/
theorem listRegularizedPaths_full_block_profiles (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    {D L : ℕ} (Dpos : 0 < D) (Lpos : 0 < L) :
    let copies := splitListVertices paths D
    let pieces := listRegularizedPaths paths D L
    ∃ (filledV : Finset (ListVertexBlockIndex paths D)) (filledI : Finset (ListBlockIndex copies L)),
      (∀ v ∈ filledV, (occurrences (fun j => (pieces j).toFinset) v).card = D) ∧
      (univ \ filledV).card = Fintype.card V ∧
      (∀ i ∈ filledI, (pieces i).length = L) ∧ (univ \ filledI).card = Fintype.card I := by
  let original := fun i => (paths i).toFinset
  let copies := splitListVertices paths D
  let pieces := listRegularizedPaths paths D L
  let filledV := nonfinalWidthBlocks (occurrences original) D
  let filledI := nonfinalWidthBlocks (fun i => (copies i).toFinset) L
  obtain ⟨_,lengthCap,degreeCap⟩ := regularization_list_mass_caps paths simple D L Dpos Lpos
  have copySimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  refine ⟨filledV,filledI,?_,nonfinalWidthBlocks_remainders _ _,?_,nonfinalWidthBlocks_remainders _ _⟩
  · intro v full
    have here := (mem_filter.mp full).2
    have baseDegree := splitVertices_full_degree original Dpos v here
    have equal : (fun i => (copies i).toFinset) = splitVertices original D :=
      funext (splitListVertices_toFinset paths D)
    have lower := splitListPaths_degree_lower copies copySimple (w := L) v
    have copiedDegree : (occurrences (fun i => (copies i).toFinset) v).card = D :=
      (congrArg (fun rows : I → Finset (ListVertexBlockIndex paths D) => (occurrences rows v).card) equal).trans baseDegree
    exact le_antisymm (degreeCap v) (copiedDegree.ge.trans lower)
  · intro i full
    have here := (mem_filter.mp full).2
    rw [List.toFinset_card_of_nodup (copySimple i.fst)] at here
    exact le_antisymm (lengthCap i) (localPathBlock_card_of_full _ (copySimple i.fst) Lpos here)

/-- The degree split alone has one possible remainder for each original
vertex, and every earlier block has exactly the prescribed degree. -/
theorem splitListVertices_full_block_profile (paths : I → List V)
    {D : ℕ} (positive : 0 < D) :
    ∃ filled : Finset (ListVertexBlockIndex paths D),
      (∀ v ∈ filled, (occurrences (fun i => (splitListVertices paths D i).toFinset) v).card = D) ∧
      (univ \ filled).card = Fintype.card V := by
  let original := fun i => (paths i).toFinset
  let filled := nonfinalWidthBlocks (occurrences original) D
  have eq : (fun i => (splitListVertices paths D i).toFinset) = splitVertices original D :=
    funext (splitListVertices_toFinset paths D)
  refine ⟨filled,?_,nonfinalWidthBlocks_remainders _ _⟩
  intro v member
  rw [eq]
  exact splitVertices_full_degree original positive v (mem_filter.mp member).2

end OnlineReachabilityPreservers
