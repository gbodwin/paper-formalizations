import OnlineReachabilityPreservers.LocalRegularization

/-! Splitting a vertex alone can create a half-bridge, even with unique intersections. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

private local instance {V I : Type*} [DecidableEq V] (paths : I → List V) (i : I) (s t : V) :
    Decidable (BeforeIn paths i s t) := by
  unfold BeforeIn
  infer_instance

/-- The incoming edge from 4 and the river are the first two paths at vertex 2. -/
def vertexSplitExample : Fin 6 → List (Fin 5) :=
  ![[4,2], [0,2], [0,1], [1,2], [2,3], [3,4]]

/-- The first pair at vertex 2 is assigned to copy 5 and the later pair to copy 2. -/
def vertexSplitExampleAfter : Fin 6 → List (Fin 6) :=
  ![[4,5], [0,5], [0,1], [1,2], [2,3], [3,4]]

private def prefixArcs {V I : Type*} [DecidableEq V] [DecidableEq I] [Fintype V] [Fintype I]
    (paths : I → List V) (r : I) (t : V) : Arcs V :=
  univ.filter fun e => e.1 ≠ t ∧ ∃ i : I, i ≠ r ∧ BeforeIn paths i e.1 e.2

private theorem reach_indexed {V : Type*} {G : Arcs V} : ∀ {n : ℕ} (v : Fin (n+1) → V),
    (∀ i : Fin n, Edge G (v i.castSucc) (v i.succ)) → Reach G (v 0) (v (Fin.last n)) := by
  intro n
  induction n with
  | zero =>
    intro v _
    have eq : Fin.last 0 = (0 : Fin 1) := rfl
    rw [eq]
  | succ n ih =>
    intro v h
    exact (ih (v ∘ Fin.succ) (fun i => h i.succ)).head (h 0)

private theorem halfBridge_prefix_membership {V I : Type*}
    [DecidableEq V] [DecidableEq I] [Fintype V] [Fintype I]
    (paths : I → List V) {k : ℕ} (b : Bridge (BeforeIn paths) k) :
    b.vertex 0 ∈ reaches (prefixArcs paths b.river (b.vertex (Fin.last (k+1))))
      (b.vertex (Fin.last k).castSucc) := by
  let t := b.vertex (Fin.last (k+1))
  let v : Fin (k+1) → V := b.vertex ∘ Fin.castSucc
  have edge (i : Fin k) : Edge (prefixArcs paths b.river t) (v i.castSucc) (v i.succ) := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, fun same => ?_, b.arc i.castSucc, (b.river_ne_arc _).symm, ?_⟩
    · have eq := b.distinctVertices same
      have vals := congrArg Fin.val eq
      simp only [Fin.val_castSucc, Fin.val_last] at vals
      omega
    · simpa only [v, Function.comp_apply, Fin.succ_castSucc] using b.arcStep i.castSucc
  exact mem_reaches.mpr (reach_indexed v edge)

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 1024 in
set_option maxHeartbeats 1600000 in
private theorem no_prefix_to_earlier_last :
    ∀ (a r : Fin 6) (s u t : Fin 5), a < r → BeforeIn vertexSplitExample r s t →
      BeforeIn vertexSplitExample a u t → s ∉ reaches (prefixArcs vertexSplitExample r t) u := by
  decide

/-- Every original half-bridge would need to hit an earlier final arc before
visiting the river's endpoint. The finite prefix tests exclude all such walks. -/
theorem vertexSplitExample_half_free (k : ℕ) (b : Bridge (BeforeIn vertexSplitExample) k) :
    ¬ b.arc (Fin.last k) < b.river := by
  intro earlier
  exact no_prefix_to_earlier_last (b.arc (Fin.last k)) b.river _ _ _ earlier b.riverStep
    (b.arcStep (Fin.last k)) (halfBridge_prefix_membership vertexSplitExample b)

set_option synthInstance.maxSize 1024 in
/-- All original paths have length two. The only vertex above the average
degree of 12/5 is vertex 2, where the original incidence count is four. -/
theorem vertexSplitExample_original_sizes :
    (∀ i, (vertexSplitExample i).length = 2) ∧
    (∀ v : Fin 5, (occurrences (fun i => (vertexSplitExample i).toFinset) v).card =
      if v = 2 then 4 else 2) := by decide

private def vertexSplitCopyLabel (v : ListVertexBlockIndex vertexSplitExample 2) : Fin 6 :=
  if v.fst = 2 ∧ v.snd.val = 0 then 5 else v.fst.castSucc

set_option synthInstance.maxSize 1024 in
/-- The example's new lists are exactly the consecutive incidence blocks. -/
theorem vertexSplitExample_matches_split :
    ∀ i, (splitListVertices vertexSplitExample 2 i).map vertexSplitCopyLabel = vertexSplitExampleAfter i := by
  decide

set_option synthInstance.maxSize 1024 in
/-- The split creates the chain 0→1→2→3→4→5 and the river 0→5.
The last arc belongs to the first path and the river to the second. -/
theorem vertexSplitExample_creates_half_six :
    (∀ i, (vertexSplitExample i).Nodup) ∧
    (∀ (i j : Fin 6), i ≠ j → ∀ x y : Fin 5,
      x ∈ vertexSplitExample i → x ∈ vertexSplitExample j →
      y ∈ vertexSplitExample i → y ∈ vertexSplitExample j → x = y) ∧
    ∃ b : Bridge (BeforeIn vertexSplitExampleAfter) 4, b.arc (Fin.last 4) < b.river := by
  refine ⟨by decide, by decide, ?_⟩
  let v : Fin 6 → Fin 6 := id
  let a : Fin 5 → Fin 6 := ![2,3,4,5,0]
  have ha : ∀ i j, a i = a j → i = j := by decide
  have hr : ∀ i, (1 : Fin 6) ≠ a i := by decide
  have hs : BeforeIn vertexSplitExampleAfter 1 (v 0) (v (Fin.last 5)) := by unfold BeforeIn; decide
  have ht : ∀ i, BeforeIn vertexSplitExampleAfter (a i) (v i.castSucc) (v i.succ) := by unfold BeforeIn; decide
  exact ⟨⟨v, a, 1, Function.injective_id, fun {_ _} => ha _ _, hr, hs, ht⟩, by change (0 : Fin 6) < 1; decide⟩

set_option synthInstance.maxSize 1024 in
/-- The half-6-bridge exists in the actual incidence blocks. -/
theorem vertexSplitExample_blocks_create_half_six :
    ∃ b : Bridge (BeforeIn (splitListVertices vertexSplitExample 2)) 4, b.arc (Fin.last 4) < b.river := by
  let v : Fin 6 → ListVertexBlockIndex vertexSplitExample 2 :=
    ![⟨0,⟨0,by decide⟩⟩, ⟨1,⟨0,by decide⟩⟩, ⟨2,⟨1,by decide⟩⟩,
      ⟨3,⟨0,by decide⟩⟩, ⟨4,⟨0,by decide⟩⟩, ⟨2,⟨0,by decide⟩⟩]
  let a : Fin 5 → Fin 6 := ![2,3,4,5,0]
  have hv : ∀ i j, v i = v j → i = j := by decide
  have ha : ∀ i j, a i = a j → i = j := by decide
  have hr : ∀ i, (1 : Fin 6) ≠ a i := by decide
  have river : BeforeIn (splitListVertices vertexSplitExample 2) 1 (v 0) (v (Fin.last 5)) := by
    unfold BeforeIn
    decide
  have chain : ∀ i, BeforeIn (splitListVertices vertexSplitExample 2) (a i) (v i.castSucc) (v i.succ) := by
    unfold BeforeIn
    decide
  exact ⟨⟨v,a,1,fun {_ _} => hv _ _,fun {_ _} => ha _ _,hr,river,chain⟩,by change (0 : Fin 6) < 1; decide⟩

/-- After the first two incidences of vertex 2 are split off, the
two opposite edges between 2 and 3 link different copies. -/
def vertexSplitFiveExample : Fin 5 → List (Fin 4) :=
  ![[3,2], [0,2], [1,2], [2,3], [0,1]]

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 1024 in
set_option maxHeartbeats 1600000 in
private theorem no_five_prefix_to_earlier_last :
    ∀ (a r : Fin 5) (s u t : Fin 4), a < r → BeforeIn vertexSplitFiveExample r s t →
      BeforeIn vertexSplitFiveExample a u t → s ∉ reaches (prefixArcs vertexSplitFiveExample r t) u := by
  decide

/-- The original five paths exclude half-bridges of every size. -/
theorem vertexSplitFiveExample_half_free (k : ℕ) : HalfBridgeFree (BeforeIn vertexSplitFiveExample) k := by
  intro j _ b earlier
  exact no_five_prefix_to_earlier_last (b.arc (Fin.last j)) b.river _ _ _ earlier b.riverStep
    (b.arcStep (Fin.last j)) (halfBridge_prefix_membership vertexSplitFiveExample b)

set_option synthInstance.maxSize 1024 in
/-- Degree four at vertex 2 is the only degree above the average of 10/4. -/
theorem vertexSplitFiveExample_original_sizes :
    (∀ i, (vertexSplitFiveExample i).Nodup ∧ (vertexSplitFiveExample i).length = 2) ∧
    (∀ v : Fin 4, (occurrences (fun i => (vertexSplitFiveExample i).toFinset) v).card =
      if v = 2 then 4 else 2) := by decide

set_option synthInstance.maxSize 1024 in
/-- The actual consecutive incidence blocks create a half-5-bridge. -/
theorem vertexSplitFiveExample_blocks_create_half_five :
    ∃ b : Bridge (BeforeIn (splitListVertices vertexSplitFiveExample 2)) 3, b.arc (Fin.last 3) < b.river := by
  let v : Fin 5 → ListVertexBlockIndex vertexSplitFiveExample 2 :=
    ![⟨0,⟨0,by decide⟩⟩, ⟨1,⟨0,by decide⟩⟩, ⟨2,⟨1,by decide⟩⟩,
      ⟨3,⟨0,by decide⟩⟩, ⟨2,⟨0,by decide⟩⟩]
  let a : Fin 4 → Fin 5 := ![4,2,3,0]
  have hv : ∀ i j, v i = v j → i = j := by decide
  have ha : ∀ i j, a i = a j → i = j := by decide
  have hr : ∀ i, (1 : Fin 5) ≠ a i := by decide
  have river : BeforeIn (splitListVertices vertexSplitFiveExample 2) 1 (v 0) (v (Fin.last 4)) := by
    unfold BeforeIn
    decide
  have chain : ∀ i, BeforeIn (splitListVertices vertexSplitFiveExample 2) (a i) (v i.castSucc) (v i.succ) := by
    unfold BeforeIn
    decide
  exact ⟨⟨v,a,1,fun {_ _} => hv _ _,fun {_ _} => ha _ _,hr,river,chain⟩,by change (0 : Fin 5) < 1; decide⟩

end OnlineReachabilityPreservers.SourceAudit
