import OnlineReachabilityPreservers.LocalRegularization

/-! Disjoint unions of full-bridge-free families with separate budgets. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private def sumListRows {I J V W : Type*} (left : I → List V) (right : J → List W) :
    I ⊕ J → List (V ⊕ W)
  | .inl i => (left i).map Sum.inl
  | .inr j => (right j).map Sum.inr

private theorem sumListRows_valid {I J V W : Type*} {left : I → List V} {right : J → List W}
    (wellL : ∀ i, left i ≠ [] ∧ (left i).Nodup) (wellR : ∀ i, right i ≠ [] ∧ (right i).Nodup) :
    ∀ i, sumListRows left right i ≠ [] ∧ (sumListRows left right i).Nodup := by
  rintro (i | i)
  · exact ⟨by simpa [sumListRows] using (wellL i).1, (wellL i).2.map Sum.inl_injective⟩
  · exact ⟨by simpa [sumListRows] using (wellR i).1, (wellR i).2.map Sum.inr_injective⟩

private theorem sumListRows_distinct {I J V W : Type*} {left : I → List V} {right : J → List W}
    (distinctL : Function.Injective left) (distinctR : Function.Injective right)
    (wellL : ∀ i, left i ≠ []) : Function.Injective (sumListRows left right) := by
  have across (i : I) (j : J) : sumListRows left right (.inl i) ≠ sumListRows left right (.inr j) := by
    intro equal
    obtain ⟨x,on⟩ := List.exists_mem_of_ne_nil _ (wellL i)
    have member : Sum.inl x ∈ sumListRows left right (.inr j) := equal ▸ List.mem_map_of_mem on
    obtain ⟨y,_,impossible⟩ := List.mem_map.mp (show Sum.inl x ∈ (right j).map Sum.inr from member)
    exact Sum.inr_ne_inl impossible
  rintro (i | i) (j | j) same
  · exact congrArg Sum.inl (distinctL ((List.map_injective_iff.mpr Sum.inl_injective)
      (show (left i).map Sum.inl = (left j).map Sum.inl from same)))
  · exact (across i j same).elim
  · exact (across j i same.symm).elim
  · exact congrArg Sum.inr (distinctR ((List.map_injective_iff.mpr Sum.inr_injective)
      (show (right i).map Sum.inr = (right j).map Sum.inr from same)))

private theorem noSumBridgeWithLeftRiver {I J V W : Type*} [DecidableEq V] [DecidableEq W]
    {left : I → List V} {right : J → List W} (simpleL : ∀ i, (left i).Nodup)
    {d : ℕ} (freeL : IsEmpty (Bridge (Before left) d))
    (bridge : Bridge (Before (sumListRows left right)) d) {r : I} (river : bridge.river = .inl r) : False := by
  have memberSide {i v} (on : v ∈ sumListRows left right i) :
      (∃ a : V, v = .inl a) ↔ (∃ j : I, i = .inl j) := by
    cases i with
    | inl j =>
      obtain ⟨a,_,equal⟩ := List.mem_map.mp (show v ∈ (left j).map Sum.inl from on)
      exact ⟨fun _ => ⟨j,rfl⟩,fun _ => ⟨a,equal.symm⟩⟩
    | inr j =>
      obtain ⟨w,_,equal⟩ := List.mem_map.mp (show v ∈ (right j).map Sum.inr from on)
      exact ⟨fun ⟨a,h⟩ => (Sum.inr_ne_inl (equal.trans h)).elim,
        fun ⟨i,h⟩ => (Sum.inr_ne_inl h).elim⟩
  have vertexSide (j : Fin (d+2)) : ∃ a : V, bridge.vertex j = .inl a := by
    induction j using Fin.induction with
    | zero => exact (memberSide bridge.riverStep.1).mpr ⟨r,river⟩
    | succ i ih =>
      exact (memberSide (bridge.arcStep i).2.1).mpr ((memberSide (bridge.arcStep i).1).mp ih)
  have rowSide (i : Fin (d+1)) : ∃ j : I, bridge.arc i = .inl j :=
    (memberSide (bridge.arcStep i).1).mp (vertexSide i.castSucc)
  let projectV : V ⊕ W → V := Sum.elim id (fun _ => (vertexSide 0).choose)
  let projectI : I ⊕ J → I := Sum.elim id (fun _ => r)
  have restoresV (j) : Sum.inl (projectV (bridge.vertex j)) = bridge.vertex j := by
    obtain ⟨a,on⟩ := vertexSide j
    rw [on]
    rfl
  have restoresI (i) : Sum.inl (projectI (bridge.arc i)) = bridge.arc i := by
    obtain ⟨j,on⟩ := rowSide i
    rw [on]
    rfl
  have restoresR : Sum.inl (projectI bridge.river) = bridge.river := by rw [river]; rfl
  have steps {i x y} (leftSide : ∃ j : I, i = .inl j) (step : Before (sumListRows left right) i x y) :
      Before left (projectI i) (projectV x) (projectV y) := by
    obtain ⟨j,rfl⟩ := leftSide
    have undo : (sumListRows left right (.inl j)).map projectV = left j := by
      simp [sumListRows,projectV,List.map_map,Function.comp_def]
    simpa only [SourceAudit.BeforeIn,undo,projectI,Sum.elim_inl,id_eq] using
      listBefore_map projectV (undo.symm ▸ simpleL j) step
  exact freeL.false
    { vertex := projectV ∘ bridge.vertex
      arc := projectI ∘ bridge.arc
      river := projectI bridge.river
      distinctVertices := fun i j same => bridge.distinctVertices
        ((restoresV i).symm.trans ((congrArg Sum.inl same).trans (restoresV j)))
      distinctArcs := fun i j same => bridge.distinctArcs
        ((restoresI i).symm.trans ((congrArg Sum.inl same).trans (restoresI j)))
      river_ne_arc := fun i same => bridge.river_ne_arc i
        (restoresR.symm.trans ((congrArg Sum.inl same).trans (restoresI i)))
      riverStep := steps ⟨r,river⟩ bridge.riverStep
      arcStep := fun i => steps (rowSide i) (bridge.arcStep i) }

private theorem sumListRows_full {I J V W : Type*} [DecidableEq V] [DecidableEq W]
    {left : I → List V} {right : J → List W} (simpleL : ∀ i, (left i).Nodup)
    (simpleR : ∀ i, (right i).Nodup) {cutoff : ℕ} (freeL : BridgeFree (Before left) cutoff)
    (freeR : BridgeFree (Before right) cutoff) : BridgeFree (Before (sumListRows left right)) cutoff := by
  intro d size
  refine ⟨fun bridge => ?_⟩
  cases river : bridge.river with
  | inl i => exact noSumBridgeWithLeftRiver simpleL (freeL size) bridge river
  | inr i =>
    let vSwap : V ⊕ W ≃ W ⊕ V := Equiv.sumComm _ _
    let iSwap : I ⊕ J ≃ J ⊕ I := Equiv.sumComm _ _
    have decoded (j : I ⊕ J) : (sumListRows left right j).map vSwap = sumListRows right left (iSwap j) := by
      cases j <;> simp [sumListRows,vSwap,iSwap,List.map_map,Function.comp_def]
    have simple (j : J ⊕ I) : (sumListRows right left j).Nodup := by
      cases j with
      | inl j => exact (simpleR j).map Sum.inl_injective
      | inr j => exact (simpleL j).map Sum.inr_injective
    have steps {j x y} (step : Before (sumListRows left right) j x y) :
        Before (sumListRows right left) (iSwap j) (vSwap x) (vSwap y) := by
      simpa only [SourceAudit.BeforeIn,decoded] using listBefore_map vSwap
        ((decoded j).symm ▸ simple (iSwap j)) step
    let moved : Bridge (Before (fun j => sumListRows right left (iSwap j))) d :=
      bridge.mapVertices vSwap vSwap.injective (fun _ _ _ step => steps step)
    let swapped : Bridge (Before (sumListRows right left)) d :=
      moved.mapPaths iSwap iSwap.injective (fun _ _ _ step => step)
    exact noSumBridgeWithLeftRiver simpleR (freeR size) swapped (r := i)
      (by simp [swapped,moved,iSwap,Bridge.mapPaths,Bridge.mapVertices,river])

/-- A disjoint union of two literal full-bridge-free families keeps both
component budgets, adds their masses, and preserves the cutoff. -/
theorem exists_literal_full_disjoint_union {n₁ n₂ p₁ p₂ cutoff : ℕ}
    (left : Fin p₁ → List (Fin n₁)) (right : Fin p₂ → List (Fin n₂))
    (distinctL : Function.Injective left) (distinctR : Function.Injective right)
    (wellL : ∀ i, left i ≠ [] ∧ (left i).Nodup) (wellR : ∀ i, right i ≠ [] ∧ (right i).Nodup)
    (freeL : BridgeFree (Before left) cutoff) (freeR : BridgeFree (Before right) cutoff) :
    ∃ rows : Fin (p₁+p₂) → List (Fin (n₁+n₂)), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) cutoff ∧
      (∑ i, (rows i).length) = (∑ i, (left i).length)+(∑ j, (right j).length) := by
  let label := finSumFinEquiv (m := p₁) (n := p₂)
  let vertex := finSumFinEquiv (m := n₁) (n := n₂)
  let rows (i : Fin (p₁+p₂)) := (sumListRows left right (label.symm i)).map vertex
  have undo (i : Fin (p₁+p₂)) : (rows i).map vertex.symm = sumListRows left right (label.symm i) := by
    simp [rows,List.map_map]
  have well := sumListRows_valid wellL wellR
  have distinct : Function.Injective rows :=
    (List.map_injective_iff.mpr vertex.injective).comp
      ((sumListRows_distinct distinctL distinctR (fun i => (wellL i).1)).comp label.symm.injective)
  have free : BridgeFree (Before rows) cutoff := by
    intro d size
    refine ⟨fun bridge => ?_⟩
    let moved : Bridge (Before (fun i => sumListRows left right (label.symm i))) d :=
      bridge.mapVertices vertex.symm vertex.symm.injective (fun i _ _ step => by
        simpa only [SourceAudit.BeforeIn,undo] using listBefore_map vertex.symm
          ((undo i).symm ▸ (well (label.symm i)).2) step)
    exact (sumListRows_full (fun i => (wellL i).2) (fun i => (wellR i).2) freeL freeR size).false
      (moved.mapPaths label.symm label.symm.injective (fun _ _ _ step => step))
  have mass : (∑ i, (rows i).length) = (∑ i, (left i).length)+(∑ j, (right j).length) := by
    simp only [rows,List.length_map]
    rw [Equiv.sum_comp label.symm (fun i => (sumListRows left right i).length),Fintype.sum_sum_type]
    simp [sumListRows]
  exact ⟨rows,distinct,fun i => ⟨by simpa [rows] using (well (label.symm i)).1,
    (well (label.symm i)).2.map vertex.injective⟩,free,mass⟩

end OnlineReachabilityPreservers
