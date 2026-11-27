import OnlineReachabilityPreservers.BackwardCopyReturns
import OnlineReachabilityPreservers.DegreeFirstSupportedCleaning
import OnlineReachabilityPreservers.LocalRegularization
import OnlineReachabilityPreservers.HalfFivePathRepair

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

/-- Two early rows end at vertex 1 under the long fourth row. -/
def incomingCutPaths : Fin 5 → List (Fin 7) :=
  ![[4,1],[5,1],[0,3],[0,6,1,2,4,5],[3,2]]

/-- Each path in the incoming-conflict example is simple. -/
theorem incomingCutPaths_simple : ∀ i, (incomingCutPaths i).Nodup := by decide

set_option maxRecDepth 8192 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 2600000 in
private theorem incomingCut_no_early_prefix :
    ∀ (a r : Fin 5) (s u t : Fin 7), a < r → BeforeIn incomingCutPaths r s t →
      BeforeIn incomingCutPaths a u t → s ∉ reaches (prefixArcs incomingCutPaths r t) u := by
  decide

/-- The unsplit input excludes half-bridges at every cutoff. -/
theorem incomingCutPaths_halfFree (k : ℕ) : HalfBridgeFree (BeforeIn incomingCutPaths) k := by
  intro s small bridge earlier
  exact incomingCut_no_early_prefix (bridge.arc (Fin.last s)) bridge.river _ _ _ earlier
    bridge.riverStep (bridge.arcStep (Fin.last s)) (halfBridge_prefix_membership incomingCutPaths bridge)

abbrev IncomingCutPiece := ListBlockIndex incomingCutPaths 3

def incomingCutEarly : IncomingCutPiece := ⟨3,⟨0,by decide⟩⟩
def incomingCutLate : IncomingCutPiece := ⟨3,⟨1,by decide⟩⟩
def incomingCutSource0 : IncomingCutPiece := ⟨0,⟨0,by decide⟩⟩
def incomingCutSource1 : IncomingCutPiece := ⟨1,⟨0,by decide⟩⟩

/-- A single incidence on the overlong parent is the target of two
different incoming conflicts after the width-three split. -/
theorem incomingCutPaths_two_conflicts :
    incomingCutSource0 ≠ incomingCutSource1 ∧
      OppositeWidthConflict incomingCutPaths (splitListPaths incomingCutPaths 3) Sigma.fst
        (incomingCutSource0,1) (incomingCutEarly,1) ∧
      OppositeWidthConflict incomingCutPaths (splitListPaths incomingCutPaths 3) Sigma.fst
        (incomingCutSource1,1) (incomingCutEarly,1) := by
  refine ⟨by decide,?_,?_⟩
  · refine ⟨rfl,by decide,4,Or.inr ⟨incomingCutLate,by decide,rfl,by decide,by decide,?_,?_⟩⟩
    · unfold BeforeIn
      decide
    · unfold BeforeIn
      decide
  · refine ⟨rfl,by decide,5,Or.inr ⟨incomingCutLate,by decide,rfl,by decide,by decide,?_,?_⟩⟩
    · unfold BeforeIn
      decide
    · unfold BeforeIn
      decide

set_option synthInstance.maxSize 2048 in
private def incomingCut_bridge (i : Fin 2) : Bridge (BeforeIn (splitListPaths incomingCutPaths 3)) 3 := by
  let vertex : Fin 5 → Fin 7 := ![0,3,2,⟨i.val+4,by omega⟩,1]
  let first : IncomingCutPiece := ⟨2,⟨0,by decide⟩⟩
  let second : IncomingCutPiece := ⟨4,⟨0,by decide⟩⟩
  let last : IncomingCutPiece := if i = 0 then incomingCutSource0 else incomingCutSource1
  let arc : Fin 4 → IncomingCutPiece := ![first,second,incomingCutLate,last]
  have distinctV : ∀ a b, vertex a = vertex b → a = b := by
    dsimp only [vertex]
    revert i
    decide
  have distinctA : ∀ a b, arc a = arc b → a = b := by
    dsimp only [arc,last,first,second]
    revert i
    decide
  have distinctR : ∀ j, incomingCutEarly ≠ arc j := by
    dsimp only [arc,last,first,second]
    revert i
    decide
  have river : BeforeIn (splitListPaths incomingCutPaths 3) incomingCutEarly (vertex 0) (vertex (Fin.last 4)) := by
    unfold BeforeIn
    dsimp only [vertex]
    revert i
    decide
  have steps : ∀ j, BeforeIn (splitListPaths incomingCutPaths 3) (arc j) (vertex j.castSucc) (vertex j.succ) := by
    unfold BeforeIn
    dsimp only [arc,last,first,second,vertex]
    revert i
    decide
  exact ⟨vertex,arc,incomingCutEarly,fun {_ _} => distinctV _ _,fun {_ _} => distinctA _ _,distinctR,river,steps⟩

/-- Each of the two early sources produces a forbidden bridge with the
same river piece. -/
theorem incomingCutPaths_creates_two_half_bridges :
    ∃ first second : Bridge (BeforeIn (splitListPaths incomingCutPaths 3)) 3,
      first.river = second.river ∧ first.arc (Fin.last 3) ≠ second.arc (Fin.last 3) ∧
        first.arc (Fin.last 3) < first.river ∧ second.arc (Fin.last 3) < second.river :=
  ⟨incomingCut_bridge 0,incomingCut_bridge 1,by decide⟩

/-- Insert singleton incidences so the original factor-four degree
width realizes the consecutive degree cut. -/
def frozenDegreeReturnPaths (i : Fin 35) : List (Fin 5) :=
  if i = 0 then [3,2] else if i = 1 then [0,2] else if i = 32 then [1,2]
  else if i = 33 then [2,3] else if i = 34 then [0,1] else [2]

private def frozenDegreeReturnCore : Fin 5 → Fin 35 := ![0,1,32,33,34]

/-- All strict comparisons belong to these five rows. -/
private theorem frozenDegreeReturn_active :
    ∀ (i : Fin 35) (x y : Fin 5), BeforeIn frozenDegreeReturnPaths i x y →
      ∃ j, frozenDegreeReturnCore j = i := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3500000 in
private theorem frozenDegreeReturn_no_earlier_prefix :
    ∀ (a r : Fin 5) (s u t : Fin 5), frozenDegreeReturnCore a < frozenDegreeReturnCore r →
      BeforeIn frozenDegreeReturnPaths (frozenDegreeReturnCore r) s t →
      BeforeIn frozenDegreeReturnPaths (frozenDegreeReturnCore a) u t →
      s ∉ reaches (prefixArcs frozenDegreeReturnPaths (frozenDegreeReturnCore r) t) u := by
  decide

set_option maxHeartbeats 2000000 in
/-- The unmodified original paths satisfy the half exclusion at all sizes. -/
theorem frozenDegreeReturnPaths_halfFree (k : ℕ) : HalfBridgeFree (BeforeIn frozenDegreeReturnPaths) k := by
  intro d _ b earlier
  obtain ⟨a,arc⟩ := frozenDegreeReturn_active _ _ _ (b.arcStep (Fin.last d))
  obtain ⟨r,river⟩ := frozenDegreeReturn_active _ _ _ b.riverStep
  exact frozenDegreeReturn_no_earlier_prefix a r (b.vertex 0) (b.vertex (Fin.last d).castSucc)
    (b.vertex (Fin.last (d+1))) (by simpa only [arc,river] using earlier)
    (by simpa only [river] using b.riverStep) (by simpa only [arc,Fin.succ_last] using b.arcStep (Fin.last d))
    (by simpa only [river] using halfBridge_prefix_membership frozenDegreeReturnPaths b)

private abbrev FrozenDegreeReturnCopy := ListVertexBlockIndex frozenDegreeReturnPaths 32

/-- Keep the fixed degree labels and remove the last incidence of the
row that supplies the earlier-block return. -/
def frozenDegreeReturnKept (i : Fin 35) : List FrozenDegreeReturnCopy :=
  let row := splitListVertices frozenDegreeReturnPaths 32 i
  if i = 0 then row.take 1 else row

theorem frozenDegreeReturn_widths :
    let M := ∑ i, (frozenDegreeReturnPaths i).length
    M = 40 ∧ 4*M/5 = 32 ∧ 4*M/35 = 4 ∧ (∑ i, (frozenDegreeReturnKept i).length) = 39 := by
  decide

set_option synthInstance.maxSize 1024 in
/-- The actual original-average degree split creates a half-5-bridge. -/
theorem frozenDegreeReturn_copy_creates_halfFive :
    ¬ HalfBridgeFree (BeforeIn (splitListVertices frozenDegreeReturnPaths 32)) 5 := by
  let vertex : Fin 5 → FrozenDegreeReturnCopy :=
    ![⟨0,⟨0,by decide⟩⟩,⟨1,⟨0,by decide⟩⟩,⟨2,⟨1,by decide⟩⟩,
      ⟨3,⟨0,by decide⟩⟩,⟨2,⟨0,by decide⟩⟩]
  let arc : Fin 4 → Fin 35 := ![34,32,33,0]
  have distinctVertices : ∀ i j, vertex i = vertex j → i = j := by decide
  have distinctRows : ∀ i j, arc i = arc j → i = j := by decide
  have riverApart : ∀ i, (1 : Fin 35) ≠ arc i := by decide
  have river : BeforeIn (splitListVertices frozenDegreeReturnPaths 32) 1 (vertex 0) (vertex (Fin.last 4)) := by
    unfold BeforeIn
    decide
  have steps : ∀ i, BeforeIn (splitListVertices frozenDegreeReturnPaths 32) (arc i) (vertex i.castSucc) (vertex i.succ) := by
    unfold BeforeIn
    decide
  intro free
  exact free (k := 3) (by decide)
    ⟨vertex,arc,1,fun {_ _} => distinctVertices _ _,fun {_ _} => distinctRows _ _,riverApart,river,steps⟩ (by
      change (0 : Fin 35) < 1
      decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Deleting the one copied incidence removes all earlier-block returns
needed at cutoff five. The retained rows fit the original path width. -/
theorem frozenDegreeReturn_after_deletion :
    NoShortBackwardCopyReturnIn frozenDegreeReturnKept 2 ∧
      NoShortReturnAcrossWidthCutsInPieces frozenDegreeReturnKept 4 5 := by
  constructor
  · apply NoShortBackwardCopyReturnIn.of_reachIn
    change ∀ (x y : FrozenDegreeReturnCopy), x.fst = y.fst → y.snd.val < x.snd.val →
      x ∉ reachIn (listPiecePrecedenceGraph frozenDegreeReturnKept) y 2
    decide
  · intro i x y step different
    have short : ∀ i, (frozenDegreeReturnKept i).length ≤ 4 := by decide
    have left := (List.idxOf_lt_length_of_mem step.1).trans_le (short i)
    have right := (List.idxOf_lt_length_of_mem step.2.1).trans_le (short i)
    exact (different ((Nat.div_eq_of_lt left).trans (Nat.div_eq_of_lt right).symm)).elim

/-- Two crossed comparisons share the first incidence of the long row. -/
def sharedCutWitnessPaths (i : Fin 18) : List (Fin 6) :=
  if i = 0 then [0,1,2,3,4,5] else if i = 1 then [4,0] else if i = 2 then [5,0]
  else if i.val < 11 then [1] else []

private def sharedCutActiveRows (i : Fin 3) : Fin 18 := Fin.castLE (by decide) i

private theorem sharedCutWitness_active :
    ∀ (i : Fin 18) (x y : Fin 6), BeforeIn sharedCutWitnessPaths i x y →
      ∃ r, sharedCutActiveRows r = i := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
private theorem sharedCutWitness_no_earlier_prefix :
    ∀ (a r : Fin 3) (s u t : Fin 6), sharedCutActiveRows a < sharedCutActiveRows r →
      BeforeIn sharedCutWitnessPaths (sharedCutActiveRows r) s t →
      BeforeIn sharedCutWitnessPaths (sharedCutActiveRows a) u t →
      s ∉ reaches (prefixArcs sharedCutWitnessPaths (sharedCutActiveRows r) t) u := by decide

theorem sharedCutWitnessPaths_halfFree (k : ℕ) : HalfBridgeFree (BeforeIn sharedCutWitnessPaths) k := by
  intro d _ b earlier
  obtain ⟨a,arc⟩ := sharedCutWitness_active _ _ _ (b.arcStep (Fin.last d))
  obtain ⟨r,river⟩ := sharedCutWitness_active _ _ _ b.riverStep
  exact sharedCutWitness_no_earlier_prefix a r (b.vertex 0) (b.vertex (Fin.last d).castSucc)
    (b.vertex (Fin.last (d+1))) (by simpa only [arc,river] using earlier)
    (by simpa only [river] using b.riverStep) (by simpa only [arc,Fin.succ_last] using b.arcStep (Fin.last d))
    (by simpa only [river] using halfBridge_prefix_membership sharedCutWitnessPaths b)

private abbrev SharedCutCopies := ListVertexBlockIndex sharedCutWitnessPaths 12
private abbrev SharedCutPieces := ListBlockIndex (splitListVertices sharedCutWitnessPaths 12) 4
private abbrev SharedCutIncidence := SharedCutPieces × SharedCutCopies

private def sharedCutVertex0 : SharedCutCopies := ⟨0,⟨0,by decide⟩⟩
private def sharedCutVertex4 : SharedCutCopies := ⟨4,⟨0,by decide⟩⟩
private def sharedCutVertex5 : SharedCutCopies := ⟨5,⟨0,by decide⟩⟩
private def sharedCutPiece0 : SharedCutPieces := ⟨0,⟨0,by decide⟩⟩
private def sharedCutPieceLast : SharedCutPieces := ⟨0,⟨1,by decide⟩⟩
private def sharedCutPiece1 : SharedCutPieces := ⟨1,⟨0,by decide⟩⟩
private def sharedCutPiece2 : SharedCutPieces := ⟨2,⟨0,by decide⟩⟩

private def sharedCutVertices : Finset SharedCutCopies := {sharedCutVertex0,sharedCutVertex4,sharedCutVertex5}
private def sharedCutPieces : Finset SharedCutPieces :=
  univ.filter fun j => listRegularizedPaths sharedCutWitnessPaths 12 4 j ≠ []

private def sharedCutWitness : SharedCutIncidence := (sharedCutPiece0,sharedCutVertex0)
private def sharedCutA4 : SharedCutIncidence := (sharedCutPieceLast,sharedCutVertex4)
private def sharedCutA5 : SharedCutIncidence := (sharedCutPieceLast,sharedCutVertex5)
private def sharedCutB4 : SharedCutIncidence := (sharedCutPiece1,sharedCutVertex4)
private def sharedCutB5 : SharedCutIncidence := (sharedCutPiece2,sharedCutVertex5)

private def sharedCutSupport : Finset SharedCutIncidence :=
  {sharedCutWitness,sharedCutA4,sharedCutA5,sharedCutB4,sharedCutB5,
    (sharedCutPiece1,sharedCutVertex0),(sharedCutPiece2,sharedCutVertex0)}

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem sharedCutSupport_eq :
    degreeFirstRectangleIncidences sharedCutWitnessPaths 12 4 sharedCutVertices sharedCutPieces = sharedCutSupport := by
  ext ⟨j,v⟩
  simp only [degreeFirstRectangleIncidences,mem_filter,mem_pieceIncidences,mem_univ,true_and]
  have test : ∀ (j : SharedCutPieces) (v : SharedCutCopies),
      ((v ∈ listRegularizedPaths sharedCutWitnessPaths 12 4 j) ∧ j ∈ sharedCutPieces ∧ v ∈ sharedCutVertices) ↔
        (j,v) ∈ sharedCutSupport := by decide
  exact test j v

set_option synthInstance.maxSize 4096 in
private local instance (s : Finset SharedCutIncidence) (a b : SharedCutIncidence) :
    Decidable (SupportedDegreeFirstConflict sharedCutWitnessPaths 12 4 s a b) := by
  unfold SupportedDegreeFirstConflict
  dsimp only
  infer_instance

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem sharedCutSupportedEdges :
    SupportedDegreeFirstConflict sharedCutWitnessPaths 12 4 sharedCutSupport sharedCutA4 sharedCutB4 ∧
      SupportedDegreeFirstConflict sharedCutWitnessPaths 12 4 sharedCutSupport sharedCutA5 sharedCutB5 := by
  constructor
  · exact ⟨by decide,by decide,by decide,sharedCutVertex0,sharedCutPiece0,sharedCutPiece1,
      rfl,rfl,by decide,by decide,by decide,by decide,Or.inr ⟨rfl,Or.inl ⟨by decide,by decide⟩⟩⟩
  · exact ⟨by decide,by decide,by decide,sharedCutVertex0,sharedCutPiece0,sharedCutPiece2,
      rfl,rfl,by decide,by decide,by decide,by decide,Or.inr ⟨rfl,Or.inl ⟨by decide,by decide⟩⟩⟩

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
private theorem sharedCutWitness_clear :
    ∀ ⦃a b⦄, ¬ SupportedDegreeFirstConflict sharedCutWitnessPaths 12 4 (sharedCutSupport \ {sharedCutWitness}) a b := by
  let kept := sharedCutSupport \ {sharedCutWitness}
  change ∀ ⦃a b⦄, ¬ SupportedDegreeFirstConflict sharedCutWitnessPaths 12 4 kept a b
  have finite : ∀ (a b : (sharedCutSupport \ {sharedCutWitness} : Finset SharedCutIncidence)),
      ¬ SupportedDegreeFirstConflict sharedCutWitnessPaths 12 4 (sharedCutSupport \ {sharedCutWitness}) a.val b.val := by
    decide
  intro a b conflict
  exact finite ⟨a,conflict.1⟩ ⟨b,conflict.2.1⟩ conflict

set_option synthInstance.maxSize 4096 in
private def sharedCutMatching : Finset (SharedCutIncidence × SharedCutIncidence) :=
  {(sharedCutA4,sharedCutB4),(sharedCutA5,sharedCutB5)}

set_option synthInstance.maxSize 4096 in
private theorem sharedCutMatching_valid :
    CutMatching (SupportedDegreeFirstConflict sharedCutWitnessPaths 12 4 sharedCutSupport)
      sharedCutSupport sharedCutMatching := by
  constructor
  · intro e member
    rcases mem_insert.mp member with rfl | second
    · exact ⟨sharedCutSupportedEdges.1.1,sharedCutSupportedEdges.1.2.1,sharedCutSupportedEdges.1⟩
    · rw [mem_singleton] at second
      subst e
      exact ⟨sharedCutSupportedEdges.2.1,sharedCutSupportedEdges.2.2.1,sharedCutSupportedEdges.2⟩
  · intro e he f hf different
    have apart : Disjoint (cutEdgeEndpoints (sharedCutA4,sharedCutB4)) (cutEdgeEndpoints (sharedCutA5,sharedCutB5)) := by
      decide
    rcases mem_insert.mp he with rfl | second
    · rcases mem_insert.mp hf with rfl | second
      · exact (different rfl).elim
      · rwa [mem_singleton.mp second]
    · rw [mem_singleton] at second
      subst e
      rcases mem_insert.mp hf with rfl | second
      · exact apart.symm
      · exact (different (mem_singleton.mp second).symm).elim

/-- One witness deletion fits the peeling budget for this rectangle.
A matching of its two supported conflicts exceeds the same budget. -/
theorem sharedCutWitness_deletion_beats_endpoint_matching :
    let R := degreeFirstRectangleIncidences sharedCutWitnessPaths 12 4 sharedCutVertices sharedCutPieces
    let fee := (18:ℝ)/5000+(18:ℝ)/(4*6)*sharedCutVertices.card+(18:ℝ)/(4*18)*sharedCutPieces.card
    (∑ i, (sharedCutWitnessPaths i).length) = 18 ∧
    (∀ ⦃a b⦄, ¬ SupportedDegreeFirstConflict sharedCutWitnessPaths 12 4 (R \ {sharedCutWitness}) a b) ∧
    fee+1 ≤ R.card ∧
    ∃ matching, CutMatching (SupportedDegreeFirstConflict sharedCutWitnessPaths 12 4 R) R matching ∧
      (R.card:ℝ) < fee+matching.card := by
  have vertices : sharedCutVertices.card = 3 := by decide
  have pieces : sharedCutPieces.card = 12 := by decide
  have size : sharedCutSupport.card = 7 := by decide
  have matching : sharedCutMatching.card = 2 := by decide
  dsimp only
  rw [sharedCutSupport_eq]
  refine ⟨by decide,fun {a b} => sharedCutWitness_clear (a := a) (b := b),?_,
    sharedCutMatching,sharedCutMatching_valid,?_⟩
  · rw [vertices,pieces,size]
    norm_num
  · rw [vertices,pieces,size,matching]
    norm_num

end OnlineReachabilityPreservers.SourceAudit
