import OnlineReachabilityPreservers.OverlayLowerAudit
import OnlineReachabilityPreservers.UniqueSplitAudit
import OnlineReachabilityPreservers.LocalSourceCounting

/-! A dense cyclic example for the frozen regularization split widths. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset
open scoped BigOperators

private noncomputable def bridgeWithinRows {V W I J : Type*} [DecidableEq V] [DecidableEq W] [Nonempty V]
    (paths : I → List V) (rows : J → List W) (simple : ∀ i, (paths i).Nodup)
    (vertex : V → W) (vertexInj : Function.Injective vertex)
    (row : I → J)
    (rowsEq : ∀ i, rows (row i) = (paths i).map vertex)
    (closed : ∀ j x, vertex x ∈ rows j → ∃ i, j = row i)
    {k : ℕ} (b : Bridge (BeforeIn rows) k) (r : I) (river : b.river = row r) : Bridge (BeforeIn paths) k := by
  classical
  have corner (j : Fin (k+2)) : ∃ x, b.vertex j = vertex x := by
    induction j using Fin.induction with
    | zero =>
      have first := b.riverStep.1
      rw [river,rowsEq] at first
      obtain ⟨x,_,hx⟩ := List.mem_map.mp first
      exact ⟨x,hx.symm⟩
    | succ j ih =>
      obtain ⟨x,hx⟩ := ih
      have on := b.arcStep j
      obtain ⟨i,hi⟩ := closed (b.arc j) x (hx ▸ on.1)
      have next := on.2.1
      rw [hi,rowsEq] at next
      obtain ⟨y,_,hy⟩ := List.mem_map.mp next
      exact ⟨y,hy.symm⟩
  let u (j : Fin (k+2)) := Classical.choose (corner j)
  have hu (j : Fin (k+2)) : b.vertex j = vertex (u j) := Classical.choose_spec (corner j)
  have arcRow (j : Fin (k+1)) : ∃ i, b.arc j = row i :=
    closed _ _ (hu j.castSucc ▸ (b.arcStep j).1)
  let a (j : Fin (k+1)) := Classical.choose (arcRow j)
  have ha (j : Fin (k+1)) : b.arc j = row (a j) := Classical.choose_spec (arcRow j)
  let back := Function.invFun vertex
  have undo : Function.LeftInverse back vertex := Function.leftInverse_invFun vertexInj
  have project (i : I) {s t : V} (step : BeforeIn rows (row i) (vertex s) (vertex t)) : BeforeIn paths i s t := by
    let joined : I → List W := rows ∘ row
    have restored (l : I) : (joined l).map back = paths l := by
      change (rows (row l)).map back = _
      rw [rowsEq,List.map_map]
      have idEq : back ∘ vertex = id := funext undo
      rw [idEq,List.map_id]
    have move := listBefore_map (paths := joined) back ((restored i).symm ▸ simple i) step
    simpa only [restored,undo s,undo t] using move
  refine ⟨u,a,r,?_,?_,?_,?_,?_⟩
  · intro i j eq
    exact b.distinctVertices ((hu i).trans (eq ▸ (hu j).symm))
  · intro i j eq
    exact b.distinctArcs ((ha i).trans (eq ▸ (ha j).symm))
  · intro i eq
    exact b.river_ne_arc i (river.trans (eq ▸ (ha i).symm))
  · apply project
    rw [← hu,← hu,← river]
    exact b.riverStep
  · intro i
    apply project
    rw [← hu,← hu,← ha]
    exact b.arcStep i

private theorem bridgeCorner_twoPaths {V I : Type*} [DecidableEq V] {paths : I → List V} {k : ℕ}
    (b : Bridge (BeforeIn paths) k) (j : Fin (k+2)) :
    ∃ a c, a ≠ c ∧ b.vertex j ∈ paths a ∧ b.vertex j ∈ paths c := by
  refine Fin.cases ?_ ?_ j
  · exact ⟨b.river,b.arc 0,b.river_ne_arc 0,b.riverStep.1,(b.arcStep 0).1⟩
  · intro i
    refine Fin.lastCases (motive := fun i : Fin (k+1) =>
      ∃ a c, a ≠ c ∧ b.vertex i.succ ∈ paths a ∧ b.vertex i.succ ∈ paths c) ?_ ?_ i
    · rw [Fin.succ_last]
      exact ⟨b.river,b.arc (Fin.last k),b.river_ne_arc _,b.riverStep.2.1,(b.arcStep _).2.1⟩
    · intro h
      have apart : h.castSucc ≠ h.succ := by
        intro eq
        have value := congrArg Fin.val eq
        simp only [Fin.val_castSucc,Fin.val_succ] at value
        omega
      refine ⟨b.arc h.castSucc,b.arc h.succ,fun eq => apart (b.distinctArcs eq),
        (b.arcStep h.castSucc).2.1,?_⟩
      rw [Fin.succ_castSucc]
      exact (b.arcStep h.succ).1

private def gadgetPadding (extra : ℕ) (i : Fin 6) : List (Fin 7 ⊕ Fin extra) :=
  if i = 0 then (List.finRange extra).map Sum.inr else []

private def paddedSevenGadget (extra : ℕ) (i : Fin 6) : List (Fin 7 ⊕ Fin extra) :=
  gadgetPadding extra i ++ (uniqueSplitExample i).map Sum.inl

private theorem paddedSevenGadget_simple (extra : ℕ) (i : Fin 6) : (paddedSevenGadget extra i).Nodup := by
  have base := uniqueSplitExample_creates_half_seven.1 i
  unfold paddedSevenGadget gadgetPadding
  split
  · rw [List.nodup_append]
    exact ⟨(List.nodup_finRange _).map Sum.inr_injective,base.map Sum.inl_injective,by simp⟩
  · simpa only [List.nil_append] using base.map (Sum.inl_injective (β := Fin extra))

private theorem gadgetMem_inl {extra : ℕ} {i : Fin 6} {x : Fin 7} :
    Sum.inl x ∈ paddedSevenGadget extra i ↔ x ∈ uniqueSplitExample i := by
  unfold paddedSevenGadget gadgetPadding
  split <;> simp

private theorem gadgetMem_inr {extra : ℕ} {i : Fin 6} {x : Fin extra}
    (mem : Sum.inr x ∈ paddedSevenGadget extra i) : i = 0 := by
  by_contra h
  simp [paddedSevenGadget,gadgetPadding,h] at mem

private theorem gadgetBefore_inl {extra : ℕ} {i : Fin 6} {s t : Fin 7} :
    BeforeIn (paddedSevenGadget extra) i (.inl s) (.inl t) ↔ BeforeIn uniqueSplitExample i s t := by
  let _ : BEq (Fin 7 ⊕ Fin extra) := instBEqOfDecidableEq
  let main : Fin 6 → List (Fin 7 ⊕ Fin extra) := fun i => (uniqueSplitExample i).map Sum.inl
  have simple := uniqueSplitExample_creates_half_seven.1 i
  have absent (v : Fin 7) : Sum.inl v ∉ gadgetPadding extra i := by
    unfold gadgetPadding
    split <;> simp
  have rank {x y : Fin 7} : ((paddedSevenGadget extra i).idxOf (.inl x) <
      (paddedSevenGadget extra i).idxOf (.inl y)) ↔
      (main i).idxOf (.inl x) < (main i).idxOf (.inl y) := by
    unfold paddedSevenGadget
    rw [List.idxOf_append_of_notMem (absent x),List.idxOf_append_of_notMem (absent y)]
    exact Nat.add_lt_add_iff_left
  have forward (step : BeforeIn uniqueSplitExample i s t) : BeforeIn main i (.inl s) (.inl t) :=
    listBefore_map (paths := uniqueSplitExample) Sum.inl (simple.map Sum.inl_injective) step
  have back (step : BeforeIn main i (.inl s) (.inl t)) : BeforeIn uniqueSplitExample i s t := by
    let project : Fin 7 ⊕ Fin extra → Fin 7 := Sum.elim id (fun _ => 0)
    have undo (j : Fin 6) : (main j).map project = uniqueSplitExample j := by simp [main,project,List.map_map]
    simpa only [undo,project,Sum.elim_inl,id_eq] using
      listBefore_map (paths := main) project ((undo i).symm ▸ simple) step
  refine ⟨fun step => back ?_,fun step => ?_⟩
  · have left : Sum.inl s ∈ main i := List.mem_map_of_mem (gadgetMem_inl.mp step.1)
    have right : Sum.inl t ∈ main i := List.mem_map_of_mem (gadgetMem_inl.mp step.2.1)
    exact ⟨left,right,rank.mp step.2.2⟩
  · exact ⟨gadgetMem_inl.mpr step.1,gadgetMem_inl.mpr step.2.1,rank.mpr (forward step).2.2⟩

private theorem paddedSevenGadget_fullFree (extra k : ℕ) : IsEmpty (Bridge (BeforeIn (paddedSevenGadget extra)) k) := by
  refine ⟨fun b => ?_⟩
  have corner (j : Fin (k+2)) : ∃ v, b.vertex j = Sum.inl v := by
    generalize eq : b.vertex j = x
    cases x with
    | inl v => exact ⟨v,rfl⟩
    | inr fresh =>
      obtain ⟨a,c,apart,ma,mc⟩ := bridgeCorner_twoPaths b j
      exact (apart ((gadgetMem_inr (eq ▸ ma)).trans (gadgetMem_inr (eq ▸ mc)).symm)).elim
  let v (j : Fin (k+2)) := Classical.choose (corner j)
  have hv (j : Fin (k+2)) : b.vertex j = Sum.inl (v j) := Classical.choose_spec (corner j)
  apply (uniqueSplitExample_bridge_free k).false
  refine ⟨v,b.arc,b.river,?_,b.distinctArcs,b.river_ne_arc,?_,?_⟩
  · intro i j eq
    exact b.distinctVertices ((hv i).trans (eq ▸ (hv j).symm))
  · apply gadgetBefore_inl.mp
    rw [← hv,← hv]
    exact b.riverStep
  · intro i
    apply gadgetBefore_inl.mp
    rw [← hv,← hv]
    exact b.arcStep i

private theorem paddedSevenGadget_unique {extra : ℕ} {a c : Fin 6} {x y : Fin 7 ⊕ Fin extra}
    (apart : a ≠ c) (xa : x ∈ paddedSevenGadget extra a) (xc : x ∈ paddedSevenGadget extra c)
    (ya : y ∈ paddedSevenGadget extra a) (yc : y ∈ paddedSevenGadget extra c) : x = y := by
  cases x with
  | inr privateX => exact (apart ((gadgetMem_inr xa).trans (gadgetMem_inr xc).symm)).elim
  | inl u =>
    cases y with
    | inr privateY => exact (apart ((gadgetMem_inr ya).trans (gadgetMem_inr yc).symm)).elim
    | inl v =>
      exact congrArg Sum.inl (uniqueSplitExample_creates_half_seven.2.1 a c apart u v
        (gadgetMem_inl.mp xa) (gadgetMem_inl.mp xc) (gadgetMem_inl.mp ya) (gadgetMem_inl.mp yc))

private def disjointRows {V W I J : Type*} (left : I → List V) (right : J → List W) : I ⊕ J → List (V ⊕ W)
  | .inl i => (left i).map Sum.inl
  | .inr j => (right j).map Sum.inr

private theorem disjointRows_fullFree {V W I J : Type*} [DecidableEq V] [DecidableEq W] [Nonempty V] [Nonempty W]
    (left : I → List V) (right : J → List W) (leftSimple : ∀ i, (left i).Nodup)
    (rightSimple : ∀ i, (right i).Nodup) {k : ℕ}
    (leftFree : IsEmpty (Bridge (BeforeIn left) k)) (rightFree : IsEmpty (Bridge (BeforeIn right) k)) :
    IsEmpty (Bridge (BeforeIn (disjointRows left right)) k) := by
  refine ⟨fun b => ?_⟩
  cases river : b.river with
  | inl i =>
    apply leftFree.false (bridgeWithinRows left (disjointRows left right) leftSimple Sum.inl Sum.inl_injective
      Sum.inl (fun _ => rfl) ?_ b i river)
    intro r v on
    cases r with
    | inl r => exact ⟨r,rfl⟩
    | inr r => simp [disjointRows] at on
  | inr i =>
    apply rightFree.false (bridgeWithinRows right (disjointRows left right) rightSimple Sum.inr Sum.inr_injective
      Sum.inr (fun _ => rfl) ?_ b i river)
    intro r v on
    cases r with
    | inl r => simp [disjointRows] at on
    | inr r => exact ⟨r,rfl⟩

private theorem disjointRows_unique {V W I J : Type*} (left : I → List V) (right : J → List W)
    (leftUnique : ∀ {i j x y}, i ≠ j → x ∈ left i → x ∈ left j → y ∈ left i → y ∈ left j → x = y)
    (rightUnique : ∀ {i j x y}, i ≠ j → x ∈ right i → x ∈ right j → y ∈ right i → y ∈ right j → x = y)
    {i j : I ⊕ J} {x y : V ⊕ W} (apart : i ≠ j) (xi : x ∈ disjointRows left right i)
    (xj : x ∈ disjointRows left right j) (yi : y ∈ disjointRows left right i)
    (yj : y ∈ disjointRows left right j) : x = y := by
  cases i with
  | inl a =>
    simp only [disjointRows,List.mem_map] at xi yi
    obtain ⟨u,ua,rfl⟩ := xi
    obtain ⟨v,va,rfl⟩ := yi
    cases j with
    | inl c =>
      simp only [disjointRows,List.mem_map,Sum.inl.injEq,exists_eq_right] at xj yj
      exact congrArg Sum.inl (leftUnique (fun e => apart (congrArg Sum.inl e)) ua xj va yj)
    | inr c => simp [disjointRows] at xj
  | inr a =>
    simp only [disjointRows,List.mem_map] at xi yi
    obtain ⟨u,ua,rfl⟩ := xi
    obtain ⟨v,va,rfl⟩ := yi
    cases j with
    | inl c => simp [disjointRows] at xj
    | inr c =>
      simp only [disjointRows,List.mem_map,Sum.inr.injEq,exists_eq_right] at xj yj
      exact congrArg Sum.inr (rightUnique (fun e => apart (congrArg Sum.inr e)) ua xj va yj)

private abbrev DenseWidthV := LatticeVertex 40 40 ⊕ (Fin 7 ⊕ Fin 161)
private abbrev DenseWidthI := LatticeLine 40 40 ⊕ Fin 6

private theorem denseWidthV_card : Fintype.card DenseWidthV = 16793600168 := by
  simp only [DenseWidthV, LatticeVertex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  norm_num

private theorem denseWidthI_card : Fintype.card DenseWidthI = 4096000006 := by
  simp only [DenseWidthI, LatticeLine, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  norm_num

private noncomputable def denseWidthVertexIndex : DenseWidthV ≃ Fin 16793600168 :=
  Fintype.equivFinOfCardEq denseWidthV_card

private noncomputable def denseWidthPathIndex : DenseWidthI ≃ Fin 4096000006 :=
  Fintype.equivFinOfCardEq denseWidthI_card

private def denseWidthUnranked : DenseWidthI → List DenseWidthV :=
  disjointRows (@latticePaths 40 40) (paddedSevenGadget 161)

private noncomputable def denseWidthPaths (i : Fin 4096000006) : List (Fin 16793600168) :=
  (denseWidthUnranked (denseWidthPathIndex.symm i)).map denseWidthVertexIndex

private theorem sum_lengths_after_ranking {A B I J : Type*} [Fintype I] [Fintype J]
    (paths : I → List A) (iv : A → B) (rank : I ≃ J) :
    (∑ j : J, ((paths (rank.symm j)).map iv).length) = ∑ i : I, (paths i).length := by
  simp only [List.length_map]
  rw [← Equiv.sum_comp rank]
  simp only [Equiv.symm_apply_apply]

private theorem disjointRows_mass {A B I J : Type*} [Fintype I] [Fintype J]
    (left : I → List A) (right : J → List B) :
    (∑ i : I ⊕ J, (disjointRows left right i).length) = (∑ i : I, (left i).length)+(∑ j : J, (right j).length) := by
  rw [Fintype.sum_sum_type]
  simp only [disjointRows,List.length_map]

private theorem latticePaths_mass_exact (steps slopes : ℕ) :
    (∑ i : LatticeLine steps slopes, (latticePaths i).length) = (steps+1)*steps^2*slopes^4 := by
  simp only [latticePaths,List.length_ofFn,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,LatticeLine,
    Fintype.card_prod,Fintype.card_fin,Nat.cast_id]
  ring

private theorem paddedSevenGadget_mass (extra : ℕ) : (∑ i : Fin 6, (paddedSevenGadget extra i).length) = extra+14 := by
  simp only [paddedSevenGadget,List.length_append,List.length_map,Finset.sum_add_distrib]
  rw [uniqueSplitExample_original_sizes.1]
  have exactPad : (∑ i : Fin 6, (gadgetPadding extra i).length) = extra := by
    simp [gadgetPadding,apply_ite]
  rw [exactPad]

private theorem denseWidthPaths_mass : (∑ i, (denseWidthPaths i).length) = 167936000175 := by
  unfold denseWidthPaths
  rw [sum_lengths_after_ranking]
  unfold denseWidthUnranked
  rw [disjointRows_mass,latticePaths_mass_exact,paddedSevenGadget_mass]
  norm_num

private noncomputable def widthCounterGadgetVertex (x : Fin 7 ⊕ Fin 161) : Fin 16793600168 :=
  denseWidthVertexIndex (.inr x)

private noncomputable def widthCounterGadgetPath (i : Fin 6) : Fin 4096000006 :=
  denseWidthPathIndex (.inr i)

private theorem widthCounterGadgetVertex_inj : Function.Injective widthCounterGadgetVertex :=
  denseWidthVertexIndex.injective.comp Sum.inr_injective

private theorem denseWidthPaths_gadget (i : Fin 6) :
    denseWidthPaths (widthCounterGadgetPath i) = (paddedSevenGadget 161 i).map widthCounterGadgetVertex := by
  simp only [denseWidthPaths,widthCounterGadgetPath,Equiv.symm_apply_apply,denseWidthUnranked,disjointRows,List.map_map]
  rfl

private theorem denseWidthUnranked_simple
    (base : ∀ i : LatticeLine 40 40, (latticePaths i).Nodup) (i : DenseWidthI) :
    (denseWidthUnranked i).Nodup := by
  unfold denseWidthUnranked
  cases i with
  | inl r => exact (base r).map Sum.inl_injective
  | inr r => exact (paddedSevenGadget_simple _ r).map Sum.inr_injective

private theorem denseWidthPaths_simple
    (base : ∀ i : LatticeLine 40 40, (latticePaths i).Nodup) (i : Fin 4096000006) :
    (denseWidthPaths i).Nodup :=
  (denseWidthUnranked_simple base _).map denseWidthVertexIndex.injective

private theorem denseWidthPaths_fullFree (base : ∀ i : LatticeLine 40 40, (latticePaths i).Nodup)
    (free : ∀ k, IsEmpty (Bridge (BeforeIn (@latticePaths 40 40)) k)) (k : ℕ) :
    IsEmpty (Bridge (BeforeIn denseWidthPaths) k) := by
  refine ⟨fun b => ?_⟩
  have empty : IsEmpty (Bridge (BeforeIn denseWidthUnranked) k) :=
    disjointRows_fullFree _ _ base (paddedSevenGadget_simple _) (free k) (paddedSevenGadget_fullFree _ k)
  have restore (i : Fin 4096000006) :
      (denseWidthPaths i).map denseWidthVertexIndex.symm = denseWidthUnranked (denseWidthPathIndex.symm i) := by
    simp [denseWidthPaths,List.map_map]
  let moved := b.mapVertices denseWidthVertexIndex.symm denseWidthVertexIndex.symm.injective
    (after := BeforeIn (fun i => denseWidthUnranked (denseWidthPathIndex.symm i))) (fun i _ _ before => by
      have back := listBefore_map denseWidthVertexIndex.symm ((restore i).symm ▸
        denseWidthUnranked_simple base _) before
      simpa only [restore] using back)
  exact empty.false (moved.mapPaths denseWidthPathIndex.symm denseWidthPathIndex.symm.injective (fun _ _ _ h => h))

private theorem denseWidthPaths_gadgetDegree (x : Fin 7 ⊕ Fin 161) :
    (occurrences (fun i => (denseWidthPaths i).toFinset) (widthCounterGadgetVertex x)).card ≤ 6 := by
  classical
  let ids := (univ : Finset (Fin 6)).image widthCounterGadgetPath
  have sub : occurrences (fun i => (denseWidthPaths i).toFinset) (widthCounterGadgetVertex x) ⊆ ids := by
    intro i inside
    have contains : widthCounterGadgetVertex x ∈ (denseWidthPaths i).toFinset :=
      (mem_occurrences (marks := fun j => (denseWidthPaths j).toFinset)).mp inside
    have on : widthCounterGadgetVertex x ∈ denseWidthPaths i := List.mem_toFinset.mp contains
    unfold denseWidthPaths at on
    obtain ⟨v, mem, equal⟩ := List.mem_map.mp on
    have eq : v = Sum.inr x := denseWidthVertexIndex.injective equal
    subst v
    cases id : denseWidthPathIndex.symm i with
    | inl left => simp [denseWidthUnranked,disjointRows,id] at mem
    | inr j =>
      apply mem_image.mpr
      refine ⟨j,mem_univ _,?_⟩
      change denseWidthPathIndex (.inr j) = i
      rw [← id,Equiv.apply_symm_apply]
  exact (card_le_card sub).trans (card_image_le.trans_eq (by simp))

private theorem denseWidthPaths_unique
    (base : ∀ {a c : LatticeLine 40 40} {x y}, a ≠ c → x ∈ latticePaths a → x ∈ latticePaths c →
      y ∈ latticePaths a → y ∈ latticePaths c → x = y)
    {i j : Fin 4096000006} {x y : Fin 16793600168} (apart : i ≠ j)
    (xi : x ∈ denseWidthPaths i) (xj : x ∈ denseWidthPaths j)
    (yi : y ∈ denseWidthPaths i) (yj : y ∈ denseWidthPaths j) : x = y := by
  have old (i : Fin 4096000006) (x : Fin 16793600168) (h : x ∈ denseWidthPaths i) :
      denseWidthVertexIndex.symm x ∈ denseWidthUnranked (denseWidthPathIndex.symm i) := by
    unfold denseWidthPaths at h
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
    simpa only [Equiv.symm_apply_apply] using hv
  apply denseWidthVertexIndex.symm.injective
  exact disjointRows_unique _ _ (fun {_ _ _ _} => base) (fun {_ _ _ _} => paddedSevenGadget_unique)
    (fun eq => apart (denseWidthPathIndex.symm.injective eq)) (old i x xi) (old j x xj) (old i y yi) (old j y yj)

private theorem idxOf_map_on_path {A B : Type*} [DecidableEq A] [DecidableEq B] (f : A → B)
    {row : List A} {x : A} (simple : (row.map f).Nodup) (on : x ∈ row) :
    (row.map f).idxOf (f x) = row.idxOf x := by
  have inside := List.idxOf_lt_length_of_mem on
  have imageInside : row.idxOf x < (row.map f).length := by simpa only [List.length_map] using inside
  have rank := simple.idxOf_getElem (i := row.idxOf x) imageInside
  rw [List.getElem_map,List.getElem_idxOf inside] at rank
  exact rank

private theorem paddedGadget_index {extra : ℕ} {i : Fin 6} {v : Fin 7} (on : v ∈ uniqueSplitExample i) :
    @List.idxOf (Fin 7 ⊕ Fin extra) instBEqOfDecidableEq (.inl v) (paddedSevenGadget extra i) =
      (if i = 0 then extra else 0)+(uniqueSplitExample i).idxOf v := by
  let _ : BEq (Fin 7 ⊕ Fin extra) := instBEqOfDecidableEq
  have absent : Sum.inl v ∉ gadgetPadding extra i := by
    unfold gadgetPadding
    split <;> simp
  have before := idxOf_map_on_path (Sum.inl : Fin 7 → Fin 7 ⊕ Fin extra)
    ((uniqueSplitExample_creates_half_seven.1 i).map Sum.inl_injective) on
  unfold paddedSevenGadget
  rw [List.idxOf_append_of_notMem absent,before]
  by_cases first : i = 0 <;> simp [gadgetPadding,first]

private def chartParent : Fin 7 → Fin 6 := ![0,0,1,2,3,4,5]
private def chartBlock : Fin 7 → ℕ := ![0,1,0,0,0,0,0]

private theorem chart_injective : Function.Injective (fun i => (chartParent i,chartBlock i)) := by decide

local instance decidableListBefore {V I : Type*} [DecidableEq V]
    (paths : I → List V) (i : I) (u v : V) : Decidable (BeforeIn paths i u v) := by
  unfold BeforeIn
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem splitWidthCertificate :
    ∀ i x y, BeforeIn uniqueSplitExampleAfter i x y →
      BeforeIn uniqueSplitExample (chartParent i) x y ∧
      ((if chartParent i = 0 then 161 else 0)+(uniqueSplitExample (chartParent i)).idxOf x)/163 = chartBlock i ∧
      ((if chartParent i = 0 then 161 else 0)+(uniqueSplitExample (chartParent i)).idxOf y)/163 = chartBlock i := by
  decide

private def firstVertexCopy {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]
    (paths : I → List V) (w : ℕ) (x : V) : ListVertexBlockIndex paths w :=
  ⟨x,⟨0,Nat.succ_pos _⟩⟩

private theorem firstVertexCopy_injective {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]
    (paths : I → List V) (w : ℕ) : Function.Injective (firstVertexCopy paths w) :=
  fun _ _ h => congrArg Sigma.fst h

private theorem splitListVertices_eq_firstCopy {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]
    (paths : I → List V) (w : ℕ) (i : I)
    (small : ∀ x ∈ paths i, (occurrences (fun j => (paths j).toFinset) x).card < w) :
    splitListVertices paths w i = (paths i).map (firstVertexCopy paths w) := by
  unfold splitListVertices
  trans (paths i).attach.map (fun x => firstVertexCopy paths w x.val)
  · congr 1
    funext x
    have limited : (predecessors (occurrences (fun j => (paths j).toFinset) x.val) i).card < w :=
      (card_filter_le _ _).trans_lt (small x.val x.property)
    simp only [vertexCopy,firstVertexCopy,Nat.div_eq_of_lt limited]
    rfl
  · calc
      _ = ((paths i).attach.map Subtype.val).map (firstVertexCopy paths w) := by
        simp only [List.map_map,Function.comp_def]
      _ = _ := by rw [List.attach_map_subtype_val]

private abbrev denseWidthCopies := ListVertexBlockIndex denseWidthPaths 39
private noncomputable def denseCopiedPaths := splitListVertices denseWidthPaths 39

private theorem denseGadgetCopies (i : Fin 6) :
    denseCopiedPaths (widthCounterGadgetPath i) =
      (denseWidthPaths (widthCounterGadgetPath i)).map (firstVertexCopy denseWidthPaths 39) := by
  apply splitListVertices_eq_firstCopy
  intro x on
  rw [denseWidthPaths_gadget] at on
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp on
  exact (denseWidthPaths_gadgetDegree v).trans_lt (by decide)

private noncomputable def denseGadgetCorner (x : Fin 7) : denseWidthCopies :=
  firstVertexCopy denseWidthPaths 39 (widthCounterGadgetVertex (.inl x))

private theorem denseGadgetCorner_inj : Function.Injective denseGadgetCorner :=
  (firstVertexCopy_injective denseWidthPaths 39).comp (widthCounterGadgetVertex_inj.comp Sum.inl_injective)

private theorem denseGadgetCopyPositions {i : Fin 6} {v : Fin 7} (on : v ∈ uniqueSplitExample i) :
    @List.idxOf denseWidthCopies instBEqOfDecidableEq (denseGadgetCorner v) (denseCopiedPaths (widthCounterGadgetPath i)) =
      (if i = 0 then 161 else 0)+(uniqueSplitExample i).idxOf v := by
  let raw := denseWidthPaths (widthCounterGadgetPath i)
  let padded := paddedSevenGadget 161 i
  have start : Sum.inl v ∈ padded := gadgetMem_inl.mpr on
  have member : widthCounterGadgetVertex (Sum.inl v) ∈ raw := by
    rw [show raw = _ from denseWidthPaths_gadget i]
    exact List.mem_map_of_mem start
  have simple : raw.Nodup := by
    rw [show raw = _ from denseWidthPaths_gadget i]
    exact (paddedSevenGadget_simple 161 i).map widthCounterGadgetVertex_inj
  rw [denseGadgetCopies]
  change @List.idxOf denseWidthCopies instBEqOfDecidableEq
    (firstVertexCopy denseWidthPaths 39 (widthCounterGadgetVertex (.inl v))) (raw.map (firstVertexCopy denseWidthPaths 39)) = _
  calc
    _ = @List.idxOf (Fin 16793600168) instBEqOfDecidableEq (widthCounterGadgetVertex (.inl v)) raw :=
      idxOf_map_on_path (firstVertexCopy denseWidthPaths 39)
        (simple.map (firstVertexCopy_injective denseWidthPaths 39)) member
    _ = @List.idxOf (Fin 7 ⊕ Fin 161) instBEqOfDecidableEq (.inl v) padded := by
      rw [show raw = _ from denseWidthPaths_gadget i]
      exact idxOf_map_on_path widthCounterGadgetVertex ((paddedSevenGadget_simple 161 i).map widthCounterGadgetVertex_inj) start
    _ = _ := paddedGadget_index on

private theorem denseGadgetCopiedSimple (i : Fin 6) : (denseCopiedPaths (widthCounterGadgetPath i)).Nodup := by
  rw [denseGadgetCopies,denseWidthPaths_gadget]
  exact ((paddedSevenGadget_simple 161 i).map widthCounterGadgetVertex_inj).map
    (firstVertexCopy_injective denseWidthPaths 39)

private theorem chartBlockExists (i : Fin 7) :
    chartBlock i < blockCount (denseCopiedPaths (widthCounterGadgetPath (chartParent i))).toFinset 163 := by
  by_cases splits : i = 1
  · subst i
    have parent : chartParent (1 : Fin 7) = 0 := by decide
    have piece : chartBlock (1 : Fin 7) = 1 := by decide
    rw [parent,piece,blockCount,List.toFinset_card_of_nodup (denseGadgetCopiedSimple 0),denseCopiedPaths,
      splitListVertices_length,denseWidthPaths_gadget,List.length_map]
    have length : (paddedSevenGadget 161 0).length = 165 := by
      simp [paddedSevenGadget,gadgetPadding,uniqueSplitExample]
    rw [length]
    decide
  · have first : ∀ j : Fin 7, j ≠ 1 → chartBlock j = 0 := by decide
    rw [first i splits,blockCount]
    exact Nat.succ_pos _

private noncomputable def denseWidthPiece (i : Fin 7) : ListBlockIndex denseCopiedPaths 163 :=
  ⟨widthCounterGadgetPath (chartParent i),⟨chartBlock i,chartBlockExists i⟩⟩

private theorem denseWidthPiece_injective : Function.Injective denseWidthPiece := by
  intro i j same
  have projected := congrArg Sigma.fst same
  change widthCounterGadgetPath (chartParent i) = widthCounterGadgetPath (chartParent j) at projected
  have parent : chartParent i = chartParent j := Sum.inr_injective (denseWidthPathIndex.injective projected)
  have block : chartBlock i = chartBlock j := congrArg (fun z : ListBlockIndex denseCopiedPaths 163 => z.snd.val) same
  exact chart_injective (Prod.ext parent block)

private theorem denseWidthPiece_step (i x y : Fin 7) (after : BeforeIn uniqueSplitExampleAfter i x y) :
    BeforeIn (fun j => listRegularizedPaths denseWidthPaths 39 163 (denseWidthPiece j)) i
      (denseGadgetCorner x) (denseGadgetCorner y) := by
  obtain ⟨old,slotX,slotY⟩ := splitWidthCertificate i x y after
  let j := chartParent i
  have padded : BeforeIn (paddedSevenGadget 161) j (.inl x) (.inl y) := gadgetBefore_inl.mpr old
  let u := widthCounterGadgetVertex (.inl x)
  let v := widthCounterGadgetVertex (.inl y)
  have before : BeforeIn denseWidthPaths (widthCounterGadgetPath j) u v := by
    have shifted := listBefore_map widthCounterGadgetVertex
      ((paddedSevenGadget_simple 161 j).map widthCounterGadgetVertex_inj) padded
    simpa only [BeforeIn,denseWidthPaths_gadget,u,v] using shifted
  have order : BeforeIn denseCopiedPaths (widthCounterGadgetPath j) (denseGadgetCorner x) (denseGadgetCorner y) := by
    have shifted := listBefore_map (firstVertexCopy denseWidthPaths 39)
      ((denseGadgetCopies j) ▸ denseGadgetCopiedSimple j) before
    simpa only [BeforeIn,denseGadgetCopies,denseGadgetCorner,u,v] using shifted
  let parents (q : Fin 7) := denseCopiedPaths (widthCounterGadgetPath (chartParent q))
  let pieces (q : Fin 7) := listRegularizedPaths denseWidthPaths 39 163 (denseWidthPiece q)
  have sub : (pieces i).Sublist (parents i) := List.filter_sublist
  have member {z : Fin 7} (on : z ∈ uniqueSplitExample j)
      (block : ((if chartParent i = 0 then 161 else 0)+(uniqueSplitExample (chartParent i)).idxOf z)/163 = chartBlock i)
      (onCopy : denseGadgetCorner z ∈ parents i) : denseGadgetCorner z ∈ pieces i := by
    change denseGadgetCorner z ∈ localPathBlock (denseCopiedPaths (widthCounterGadgetPath (chartParent i))) 163 (chartBlock i)
    refine mem_localPathBlock.mpr ⟨onCopy,?_⟩
    change (@List.idxOf denseWidthCopies instBEqOfDecidableEq (denseGadgetCorner z)
      (denseCopiedPaths (widthCounterGadgetPath j)))/163 = _
    rw [denseGadgetCopyPositions on]
    exact block
  exact (listBefore_sublist_iff (paths := parents) (cut := pieces) (denseGadgetCopiedSimple j) sub
    (member old.1 slotX order.1) (member old.2.1 slotY order.2.1)).mpr order

private theorem denseWidthPaths_split_bridge :
    Nonempty (Bridge (BeforeIn (listRegularizedPaths denseWidthPaths 39 163)) 5) := by
  obtain ⟨b,_⟩ := uniqueSplitExample_creates_half_seven.2.2
  let moved := b.mapVertices denseGadgetCorner denseGadgetCorner_inj denseWidthPiece_step
  exact ⟨moved.mapPaths denseWidthPiece denseWidthPiece_injective (fun _ _ _ h => h)⟩

/-- The dense example survives opposite-intersection pruning unchanged. -/
private theorem denseWidthPaths_prune (simple : ∀ i, (denseWidthPaths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ denseWidthPaths a → x ∈ denseWidthPaths b →
      y ∈ denseWidthPaths a → y ∈ denseWidthPaths b → x = y) :
    removeOppositeIntersections denseWidthPaths = denseWidthPaths := by
  funext i
  have sub := removeOppositeIntersections_sublist denseWidthPaths i
  apply sub.eq_of_length_le
  rw [← List.toFinset_card_of_nodup (simple i),← List.toFinset_card_of_nodup (sub.nodup (simple i))]
  apply card_le_card
  intro x on
  apply List.mem_toFinset.mpr
  refine (removeOppositeIntersections_mem denseWidthPaths i x).mpr ⟨List.mem_toFinset.mp on,?_⟩
  rintro ⟨j,earlier,y,xy,yx⟩
  have reversed := removeOppositeIntersections_before simple yx
  exact listBefore_ne xy (unique earlier.ne.symm xy.1 reversed.2.1 xy.2.1 reversed.1)

/-- The frozen factor-four widths can create a seven-bridge even above the
dense-branch mass floor, with unique intersections and full exclusion at every size. -/
theorem denseFrozenWidthSplit_creates_full_seven :
    ∃ paths : Fin 4096000006 → List (Fin 16793600168),
      (∀ i, (paths i).Nodup) ∧ (∀ k, IsEmpty (Bridge (BeforeIn paths) k)) ∧
      (∀ a b x y, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y) ∧
      removeOppositeIntersections paths = paths ∧
      let M := ∑ i, (paths i).length
      8*max 16793600168 4096000006 < M ∧
        Nonempty (Bridge (BeforeIn (listRegularizedPaths (removeOppositeIntersections paths)
          (4*M/16793600168) (4*M/4096000006))) 5) := by
  obtain ⟨simpleLattice,fullLattice,uniqueLattice⟩ := layerPaths_simple_full_and_unique 40
  have simple := denseWidthPaths_simple simpleLattice
  have full := denseWidthPaths_fullFree simpleLattice fullLattice
  have unique := @denseWidthPaths_unique (fun {_ _ _ _} => uniqueLattice)
  have prunes := denseWidthPaths_prune simple (fun {_ _ _ _} => unique)
  refine ⟨denseWidthPaths,simple,full,(fun _ _ _ _ => unique),prunes,?_⟩
  dsimp only
  rw [denseWidthPaths_mass,prunes]
  refine ⟨by norm_num,denseWidthPaths_split_bridge⟩

end OnlineReachabilityPreservers.SourceAudit
