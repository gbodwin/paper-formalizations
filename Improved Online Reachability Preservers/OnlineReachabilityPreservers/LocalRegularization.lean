import OnlineReachabilityPreservers.BridgeVertexProjection
import OnlineReachabilityPreservers.CyclicSplits
import OnlineReachabilityPreservers.OppositeIntersectionPruning
import OnlineReachabilityPreservers.Regularization

/-! Keep the order of each list through vertex and path regularization. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "ListBefore" => SourceAudit.BeforeIn

section Projection

variable {V W I : Type*} [DecidableEq V] [DecidableEq W]

/-- Projecting the vertices of a simple path to another simple path retains the local order. -/
theorem listBefore_map {paths : I → List W} {i : I} (project : W → V)
    (simple : ((paths i).map project).Nodup) {x y : W} (step : ListBefore paths i x y) :
    ListBefore (fun j => (paths j).map project) i (project x) (project y) := by
  let path := paths i
  have position {v : W} (on : v ∈ path) : ((path.map project).idxOf (project v)) = path.idxOf v := by
    have bound := List.idxOf_lt_length_of_mem on
    have mapped : path.idxOf v < (path.map project).length := by simpa only [List.length_map] using bound
    have atPosition := simple.idxOf_getElem (i := path.idxOf v) mapped
    rw [List.getElem_map, List.getElem_idxOf bound] at atPosition
    exact atPosition
  have xp := position step.1
  have yp := position step.2.1
  exact ⟨List.mem_map_of_mem step.1, List.mem_map_of_mem step.2.1, xp.symm ▸ yp.symm ▸ step.2.2⟩

private def projectShortListBridge {paths : I → List V} {copies : I → List W} (project : W → V)
    (steps : ∀ {i x y}, ListBefore copies i x y → ListBefore paths i (project x) (project y))
    {k : ℕ} (short : k ≤ 2)
    (noParallel : k = 2 → ∀ {a b x y}, a ≠ b → ListBefore paths a x y → ListBefore paths b x y → False)
    (b : Bridge (ListBefore copies) k) : Bridge (ListBefore paths) k := by
  let vertices := project ∘ b.vertex
  refine ⟨vertices, b.arc, b.river, ?_, b.distinctArcs, b.river_ne_arc, steps b.riverStep,
    fun i => steps (b.arcStep i)⟩
  intro i j equal
  interval_cases k
  · have edge : ListBefore paths (b.arc 0) (vertices 0) (vertices 1) := steps (b.arcStep 0)
    have apart : vertices 0 ≠ vertices 1 := listBefore_ne edge
    fin_cases i <;> fin_cases j <;> simp_all
  · have one : ListBefore paths (b.arc 0) (vertices 0) (vertices 1) := steps (b.arcStep 0)
    have two : ListBefore paths (b.arc 1) (vertices 1) (vertices 2) := steps (b.arcStep 1)
    have river : ListBefore paths b.river (vertices 0) (vertices 2) := steps b.riverStep
    have apart01 := listBefore_ne one
    have apart12 := listBefore_ne two
    have apart02 := listBefore_ne river
    fin_cases i <;> fin_cases j <;> simp_all
  · have one : ListBefore paths (b.arc 0) (vertices 0) (vertices 1) := steps (b.arcStep 0)
    have two : ListBefore paths (b.arc 1) (vertices 1) (vertices 2) := steps (b.arcStep 1)
    have three : ListBefore paths (b.arc 2) (vertices 2) (vertices 3) := steps (b.arcStep 2)
    have river : ListBefore paths b.river (vertices 0) (vertices 3) := steps b.riverStep
    have apart01 := listBefore_ne one
    have apart12 := listBefore_ne two
    have apart23 := listBefore_ne three
    have apart03 := listBefore_ne river
    have apart02 : vertices 0 ≠ vertices 2 := by
      intro same
      exact noParallel rfl (b.river_ne_arc 2) river (same.symm ▸ three)
    have apart13 : vertices 1 ≠ vertices 3 := by
      intro same
      exact noParallel rfl (b.river_ne_arc 0) river (same ▸ one)
    fin_cases i <;> fin_cases j <;> simp_all

/-- A projected bridge through size four still has distinct corners when
its original paths have at most one meeting vertex per pair. -/
def listBridge_after_vertex_split {paths : I → List V} {copies : I → List W} (project : W → V)
    (steps : ∀ {i x y}, ListBefore copies i x y → ListBefore paths i (project x) (project y))
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    {k : ℕ} (short : k ≤ 2) (b : Bridge (ListBefore copies) k) : Bridge (ListBefore paths) k :=
  projectShortListBridge project steps short
    (fun _ {_ _ _ _} diff left right => listBefore_ne left (unique diff left.1 right.1 left.2.1 right.2.1)) b

/-- Vertex splitting preserves full bridge exclusion at every size. -/
theorem BridgeFree.split_list_vertices_any {paths : I → List V} {copies : I → List W} {size : ℕ}
    (free : BridgeFree (ListBefore paths) size) (project : W → V)
    (steps : ∀ {i x y}, ListBefore copies i x y → ListBefore paths i (project x) (project y)) :
    BridgeFree (ListBefore copies) size := by
  intro k hk
  refine ⟨fun b => ?_⟩
  obtain ⟨j,small,old,_⟩ := b.project_vertices project steps (fun h => listBefore_ne h)
  exact (free (k := j) (by omega)).false old

/-- In a projected bridge of size four, identifying opposite corners
would give a 2-bridge. Through four, projection can keep the last arc. -/
theorem HalfBridgeFree.split_list_vertices_short [LinearOrder I]
    {paths : I → List V} {copies : I → List W} {size : ℕ}
    (free : HalfBridgeFree (ListBefore paths) size) (short : size ≤ 4) (project : W → V)
    (steps : ∀ {i x y}, ListBefore copies i x y → ListBefore paths i (project x) (project y)) :
    HalfBridgeFree (ListBefore copies) size := by
  intro k hk b earlier
  let old := projectShortListBridge project steps (by omega)
    (fun same {_ _ _ _} diff left right => no_parallel_list_steps free (by omega) diff left right) b
  exact free hk old earlier

/-- Full exclusion through `fullSize` prevents collisions in the projection
of a half-bridge with at most `fullSize + 2` corners. Thus the last arc is
kept, along with its strict arrival relation to the river. -/
theorem HalfBridgeFree.split_list_vertices_of_full [LinearOrder I]
    {paths : I → List V} {copies : I → List W} {size fullSize : ℕ}
    (free : HalfBridgeFree (ListBefore paths) size) (fullFree : BridgeFree (ListBefore paths) fullSize)
    (short : size ≤ fullSize + 2) (project : W → V)
    (steps : ∀ {i x y}, ListBefore copies i x y → ListBefore paths i (project x) (project y)) :
    HalfBridgeFree (ListBefore copies) size := by
  intro k hk b earlier
  have different : Function.Injective (project ∘ b.vertex) := by
    by_contra collision
    obtain ⟨j,smaller,old,_⟩ := b.project_vertices_with_collision project steps listBefore_ne collision
    exact (fullFree (k := j) (by omega)).false old
  let old : Bridge (ListBefore paths) k :=
    ⟨project ∘ b.vertex, b.arc, b.river, different, b.distinctArcs, b.river_ne_arc,
      steps b.riverStep, fun j => steps (b.arcStep j)⟩
  exact free hk old earlier

theorem BridgeFree.split_list_vertices {paths : I → List V} {copies : I → List W}
    (free : BridgeFree (ListBefore paths) 4) (project : W → V)
    (steps : ∀ {i x y}, ListBefore copies i x y → ListBefore paths i (project x) (project y))
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y) :
    BridgeFree (ListBefore copies) 4 := by
  intro k hk
  exact ⟨fun b => (free hk).false (listBridge_after_vertex_split project steps unique (by omega) b)⟩

theorem HalfBridgeFree.split_list_vertices [LinearOrder I] {paths : I → List V} {copies : I → List W}
    (free : HalfBridgeFree (ListBefore paths) 4) (project : W → V)
    (steps : ∀ {i x y}, ListBefore copies i x y → ListBefore paths i (project x) (project y))
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y) :
    HalfBridgeFree (ListBefore copies) 4 := by
  intro k hk b earlier
  exact free hk (listBridge_after_vertex_split project steps unique (by omega) b) earlier

end Projection

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

abbrev ListVertexBlockIndex (paths : I → List V) (width : ℕ) :=
  VertexBlockIndex (fun i => (paths i).toFinset) width

/-- Use the same degree blocks as the common-order construction and keep
the input list order along each path. -/
def splitListVertices (paths : I → List V) (width : ℕ) (i : I) : List (ListVertexBlockIndex paths width) :=
  (paths i).attach.map fun v => vertexCopy (fun j => (paths j).toFinset) width i ⟨v.val, List.mem_toFinset.mpr v.property⟩

@[simp]
theorem splitListVertices_project (paths : I → List V) (width : ℕ) (i : I) :
    (splitListVertices paths width i).map (fun v => v.fst) = paths i := by
  unfold splitListVertices
  rw [List.map_map]
  exact List.attach_map_subtype_val _

@[simp]
theorem splitListVertices_length (paths : I → List V) (width : ℕ) (i : I) :
    (splitListVertices paths width i).length = (paths i).length := by
  simp [splitListVertices]

theorem splitListVertices_toFinset (paths : I → List V) (width : ℕ) (i : I) :
    (splitListVertices paths width i).toFinset = splitVertices (fun j => (paths j).toFinset) width i := by
  ext v
  rw [List.mem_toFinset]
  simp only [splitListVertices, splitVertices, List.mem_map, Finset.mem_map]
  constructor
  · rintro ⟨x, _, rfl⟩
    exact ⟨⟨x.val, List.mem_toFinset.mpr x.property⟩, mem_attach _ _, rfl⟩
  · rintro ⟨x, _, rfl⟩
    exact ⟨⟨x.val, List.mem_toFinset.mp x.property⟩, List.mem_attach _ _, rfl⟩

/-- Vertex copies preserve simplicity within a row. -/
theorem splitListVertices_simple (paths : I → List V) (width : ℕ) (i : I) (simple : (paths i).Nodup) :
    (splitListVertices paths width i).Nodup :=
  List.Nodup.of_map (fun v => v.fst) ((splitListVertices_project paths width i).symm ▸ simple)

/-- An ordered step on vertex copies projects to the original row. -/
theorem splitListVertices_step {paths : I → List V} {width : ℕ} {i : I} {x y : ListVertexBlockIndex paths width}
    (simple : (paths i).Nodup) (step : ListBefore (splitListVertices paths width) i x y) :
    ListBefore paths i x.fst y.fst := by
  have keeps := listBefore_map (fun v : ListVertexBlockIndex paths width => v.fst) ((splitListVertices_project paths width i).symm ▸ simple) step
  simpa only [splitListVertices_project] using keeps

/-- Vertex copies preserve the unique-intersection property. -/
theorem splitListVertices_unique {paths : I → List V} {width : ℕ}
    (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    {a b : I} {x y : ListVertexBlockIndex paths width} (different : a ≠ b)
    (xa : x ∈ splitListVertices paths width a) (xb : x ∈ splitListVertices paths width b)
    (ya : y ∈ splitListVertices paths width a) (yb : y ∈ splitListVertices paths width b) : x = y := by
  have project {i : I} {x : ListVertexBlockIndex paths width} (on : x ∈ splitListVertices paths width i) :
      x.fst ∈ paths i := by
    rw [← splitListVertices_project paths width i]
    exact List.mem_map_of_mem on
  have mapSimple : ((splitListVertices paths width a).map (fun v => v.fst)).Nodup := by
    rw [splitListVertices_project]
    exact simple a
  exact List.inj_on_of_nodup_map mapSimple xa ya
    (unique different (project xa) (project xb) (project ya) (project yb))

/-- One block of consecutive positions in a list path, with no reordering. -/
def localPathBlock (path : List V) (width block : ℕ) : List V :=
  path.filter fun v => decide (path.idxOf v / width = block)

@[simp]
theorem mem_localPathBlock {path : List V} {width block : ℕ} {v : V} :
    v ∈ localPathBlock path width block ↔ v ∈ path ∧ path.idxOf v / width = block := by
  simp [localPathBlock]

private theorem localPathBlock_length (path : List V) (simple : path.Nodup) {width : ℕ} (widthPos : 0 < width) (block : ℕ) :
    (localPathBlock path width block).length ≤ width := by
  have simpleBlock : (localPathBlock path width block).Nodup := List.filter_sublist.nodup simple
  rw [← List.toFinset_card_of_nodup simpleBlock]
  calc
    _ ≤ (range width).card := by
      apply card_le_card_of_injOn (fun v => path.idxOf v % width)
      · intro _ _
        exact mem_range.mpr (Nat.mod_lt _ widthPos)
      · intro x hx y hy equal
        obtain ⟨oldX, blockX⟩ := mem_localPathBlock.mp (List.mem_toFinset.mp hx)
        obtain ⟨_, blockY⟩ := mem_localPathBlock.mp (List.mem_toFinset.mp hy)
        change path.idxOf x % width = path.idxOf y % width at equal
        have idxX := Nat.mod_add_div (path.idxOf x) width
        have idxY := Nat.mod_add_div (path.idxOf y) width
        rw [blockX] at idxX
        rw [blockY] at idxY
        exact (List.idxOf_inj oldX).mp (by omega)
    _ = _ := card_range _

abbrev ListBlockIndex (paths : I → List V) (width : ℕ) := BlockIndex (fun i => (paths i).toFinset) width

def splitListPaths (paths : I → List V) (width : ℕ) (i : ListBlockIndex paths width) : List V :=
  localPathBlock (paths i.fst) width i.snd.val

omit [LinearOrder I] [Fintype I] in
private theorem splitListPaths_sublist (paths : I → List V) (width : ℕ) (i : ListBlockIndex paths width) :
    List.Sublist (splitListPaths paths width i) (paths i.fst) := List.filter_sublist

omit [LinearOrder I] [Fintype I] in
/-- Different consecutive blocks of one row have disjoint vertex sets. -/
theorem splitListPaths_disjoint {paths : I → List V} {width : ℕ} {i j : ListBlockIndex paths width}
    {x : V} (different : i ≠ j) (parent : i.fst = j.fst)
    (first : x ∈ splitListPaths paths width i) (second : x ∈ splitListPaths paths width j) : False := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  change i = j at parent
  subst j
  have qa : (paths i).idxOf x / width = a.val := (mem_localPathBlock.mp first).2
  have qb : (paths i).idxOf x / width = b.val := (mem_localPathBlock.mp second).2
  obtain rfl := Fin.ext (qa.symm.trans qb)
  exact different rfl

omit [LinearOrder I] [Fintype I] in
private theorem splitListPaths_unique {paths : I → List V} {width : ℕ}
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    {a b : ListBlockIndex paths width} {x y : V} (different : a ≠ b)
    (xa : x ∈ splitListPaths paths width a) (xb : x ∈ splitListPaths paths width b)
    (ya : y ∈ splitListPaths paths width a) (yb : y ∈ splitListPaths paths width b) : x = y := by
  have parent : a.fst ≠ b.fst := fun equal => splitListPaths_disjoint different equal xa xb
  exact unique parent ((mem_localPathBlock.mp xa).1) ((mem_localPathBlock.mp xb).1)
    ((mem_localPathBlock.mp ya).1) ((mem_localPathBlock.mp yb).1)

private theorem localPathBlock_sum (path : List V) (simple : path.Nodup) (width : ℕ) :
    (∑ q : Fin (blockCount path.toFinset width), (localPathBlock path width q.val).length) = path.length := by
  have count := card_eq_sum_card_fiberwise (s := path.toFinset) (t := range (blockCount path.toFinset width))
    (f := fun v => path.idxOf v / width) (by
      intro x hx
      change path.idxOf x / width ∈ range (blockCount path.toFinset width)
      rw [mem_range, blockCount, List.toFinset_card_of_nodup simple]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (List.idxOf_lt_length_of_mem (List.mem_toFinset.mp hx)).le))
  have same (q : ℕ) : (path.toFinset.filter (fun v => path.idxOf v / width = q)).card =
      (localPathBlock path width q).length := by
    have simpleBlock : (localPathBlock path width q).Nodup := List.filter_sublist.nodup simple
    rw [← List.toFinset_card_of_nodup simpleBlock]
    congr 1
    ext x
    simp [mem_filter]
  calc
    _ = ∑ q ∈ range (blockCount path.toFinset width), (localPathBlock path width q).length :=
      Fin.sum_univ_eq_sum_range _ _
    _ = path.toFinset.card := by
      rw [count]
      exact sum_congr rfl fun q _ => (same q).symm
    _ = _ := List.toFinset_card_of_nodup simple

omit [LinearOrder I] in
private theorem splitListPaths_size (paths : I → List V) (simple : ∀ i, (paths i).Nodup) (width : ℕ) :
    (∑ j : ListBlockIndex paths width, (splitListPaths paths width j).length) = ∑ i, (paths i).length := by
  change (∑ j : (Σ i : I, Fin (blockCount (paths i).toFinset width)), (localPathBlock (paths j.1) width j.2.val).length) = _
  rw [Fintype.sum_sigma]
  exact sum_congr rfl fun i _ => localPathBlock_sum (paths i) (simple i) width

private theorem splitListPaths_degree (paths : I → List V) (width : ℕ) (v : V) :
    (occurrences (fun i => (splitListPaths paths width i).toFinset) v).card ≤
      (occurrences (fun i => (paths i).toFinset) v).card := by
  let marks (i : ListBlockIndex paths width) := (splitListPaths paths width i).toFinset
  have listMem {i : ListBlockIndex paths width} (present : i ∈ occurrences marks v) :
      v ∈ splitListPaths paths width i := List.mem_toFinset.mp ((mem_occurrences (marks := marks)).mp present)
  apply card_le_card_of_injOn (fun i : ListBlockIndex paths width => i.fst)
  · intro i hi
    exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_localPathBlock.mp (listMem hi)).1)
  · intro a ha b hb equal
    by_contra different
    exact splitListPaths_disjoint different equal (listMem ha) (listMem hb)

/-- Apply the degree split and then divide each path into blocks of its own order. -/
def listRegularizedPaths (paths : I → List V) (D L : ℕ) :=
  splitListPaths (splitListVertices paths D) L

theorem listRegularizedPaths_simple (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (D L : ℕ) (i : ListBlockIndex (splitListVertices paths D) L) :
    (listRegularizedPaths paths D L i).Nodup :=
  (splitListPaths_sublist (splitListVertices paths D) L i).nodup
    (splitListVertices_simple paths D i.fst (simple i.fst))

theorem listRegularizedPaths_unique {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (D L : ℕ) {a b : ListBlockIndex (splitListVertices paths D) L} {x y : ListVertexBlockIndex paths D}
    (different : a ≠ b) (xa : x ∈ listRegularizedPaths paths D L a) (xb : x ∈ listRegularizedPaths paths D L b)
    (ya : y ∈ listRegularizedPaths paths D L a) (yb : y ∈ listRegularizedPaths paths D L b) : x = y :=
  splitListPaths_unique (fun ne hx hy hx' hy' => splitListVertices_unique simple unique ne hx hy hx' hy')
    different xa xb ya yb

theorem listRegularizedPaths_halfFree {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (free : HalfBridgeFree (ListBefore paths) 4) (D L : ℕ) :
    HalfBridgeFree (ListBefore (listRegularizedPaths paths D L)) 4 := by
  let copies := splitListVertices paths D
  have copyFree : HalfBridgeFree (ListBefore copies) 4 :=
    free.split_list_vertices_short le_rfl (fun v => v.fst)
      (fun {i x y} step => splitListVertices_step (width := D) (simple i) step)
  change HalfBridgeFree (ListBefore (splitListPaths copies L)) 4
  apply copyFree.split_list_paths (fun j : ListBlockIndex copies L => j.fst)
    (block_parent_mono (fun i => (copies i).toFinset) L)
  · intro i x y h
    exact listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
      (cut := splitListPaths copies L) (splitListVertices_simple paths D i.fst (simple i.fst))
      (splitListPaths_sublist copies L i) h
  · exact fun different equal first second => splitListPaths_disjoint different equal first second
  · exact fun different first second third fourth => splitListVertices_unique simple unique different first second third fourth

theorem listRegularizedPaths_fullFree {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (free : BridgeFree (ListBefore paths) 4) (D L : ℕ) :
    BridgeFree (ListBefore (listRegularizedPaths paths D L)) 4 := by
  let copies := splitListVertices paths D
  have copyFree : BridgeFree (ListBefore copies) 4 :=
    free.split_list_vertices_any (fun v => v.fst)
      (fun {i x y} step => splitListVertices_step (width := D) (simple i) step)
  change BridgeFree (ListBefore (splitListPaths copies L)) 4
  apply copyFree.split_list_paths (fun j : ListBlockIndex copies L => j.fst)
  · intro i x y h
    exact listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
      (cut := splitListPaths copies L) (splitListVertices_simple paths D i.fst (simple i.fst))
      (splitListPaths_sublist copies L i) h
  · exact fun different equal first second => splitListPaths_disjoint different equal first second
  · exact fun different first second third fourth => splitListVertices_unique simple unique different first second third fourth

/-- Both splitting steps preserve the half-bridge condition through three
on arbitrary simple paths. The parent order is unchanged. -/
theorem listRegularizedPaths_halfFree_short {paths : I → List V} {size : ℕ} (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) size) (short : size ≤ 3) (D L : ℕ) :
    HalfBridgeFree (ListBefore (listRegularizedPaths paths D L)) size := by
  let copies := splitListVertices paths D
  have copyFree : HalfBridgeFree (ListBefore copies) size :=
    free.split_list_vertices_short (short.trans (by decide)) (fun v => v.fst)
      (fun {i x y} step => splitListVertices_step (width := D) (simple i) step)
  change HalfBridgeFree (ListBefore (splitListPaths copies L)) size
  apply copyFree.split_list_paths_short short (fun j : ListBlockIndex copies L => j.fst)
    (block_parent_mono (fun i => (copies i).toFinset) L)
  · intro i x y h
    exact listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
      (cut := splitListPaths copies L) (splitListVertices_simple paths D i.fst (simple i.fst))
      (splitListPaths_sublist copies L i) h
  · exact fun different equal first second => splitListPaths_disjoint different equal first second

/-- Full bridge exclusion through three survives both splitting steps
on arbitrary simple paths. -/
theorem listRegularizedPaths_fullFree_short {paths : I → List V} {size : ℕ} (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (ListBefore paths) size) (short : size ≤ 3) (D L : ℕ) :
    BridgeFree (ListBefore (listRegularizedPaths paths D L)) size := by
  let copies := splitListVertices paths D
  have copyFree : BridgeFree (ListBefore copies) size :=
    free.split_list_vertices_any (fun v => v.fst)
      (fun {i x y} step => splitListVertices_step (width := D) (simple i) step)
  change BridgeFree (ListBefore (splitListPaths copies L)) size
  apply copyFree.split_list_paths_short short (fun j : ListBlockIndex copies L => j.fst)
  · intro i x y h
    exact listBefore_of_sublist (paths := fun j : ListBlockIndex copies L => copies j.fst)
      (cut := splitListPaths copies L) (splitListVertices_simple paths D i.fst (simple i.fst))
      (splitListPaths_sublist copies L i) h
  · exact fun different equal first second => splitListPaths_disjoint different equal first second

theorem listRegularizedPaths_halfFree_three {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) 3) (D L : ℕ) :
    HalfBridgeFree (ListBefore (listRegularizedPaths paths D L)) 3 :=
  listRegularizedPaths_halfFree_short simple free le_rfl D L

theorem listRegularizedPaths_fullFree_three {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (ListBefore paths) 3) (D L : ℕ) :
    BridgeFree (ListBefore (listRegularizedPaths paths D L)) 3 :=
  listRegularizedPaths_fullFree_short simple free le_rfl D L

/-- With positive widths, the two list splits preserve the incidence mass
and bound every degree and length by the respective width. -/
theorem regularization_list_mass_caps (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (D L : ℕ) (hD : 0 < D) (hL : 0 < L) :
    let after := listRegularizedPaths paths D L
    (∑ i, (after i).length) = ∑ i, (paths i).length ∧
      (∀ i, (after i).length ≤ L) ∧
      ∀ v, (occurrences (fun i => (after i).toFinset) v).card ≤ D := by
  let copies := splitListVertices paths D
  have copiesSimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  refine ⟨?_, ?_, ?_⟩
  · change (∑ i, (splitListPaths copies L i).length) = _
    exact (splitListPaths_size copies copiesSimple L).trans (sum_congr rfl (fun i _ => splitListVertices_length paths D i))
  · intro i
    exact localPathBlock_length (copies i.fst) (copiesSimple i.fst) hL i.snd.val
  · intro v
    apply (splitListPaths_degree copies L v).trans
    have inclusion : (occurrences (fun i => (copies i).toFinset) v) ⊆
        occurrences (splitVertices (fun i => (paths i).toFinset) D) v := by
      intro i hi
      apply mem_occurrences.mpr
      rw [← splitListVertices_toFinset paths D i]
      exact (mem_occurrences (marks := fun j => (copies j).toFinset)).mp hi
    exact (card_le_card inclusion).trans (splitVertices_degree (fun i => (paths i).toFinset) hD v)

variable [Fintype V]

/-- Splitting locally ordered simple paths preserves the mass and achieves
the two upper caps with at most twice each original ambient budget. -/
theorem regularization_list_size (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (D L : ℕ) (hD : 0 < D) (hL : 0 < L)
    (degree_mass : (∑ i, (paths i).length) ≤ Fintype.card V * D)
    (length_mass : (∑ i, (paths i).length) ≤ Fintype.card I * L) :
    let copies := splitListVertices paths D
    let after := listRegularizedPaths paths D L
    Fintype.card (ListVertexBlockIndex paths D) ≤ 2 * Fintype.card V ∧
      Fintype.card (ListBlockIndex copies L) ≤ 2 * Fintype.card I ∧
      (∑ i, (after i).length) = ∑ i, (paths i).length ∧
      (∀ i, (after i).length ≤ L) ∧
      ∀ v, (occurrences (fun i => (after i).toFinset) v).card ≤ D := by
  let copies := splitListVertices paths D
  have copiesSimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have lengths (i : I) : (paths i).toFinset.card = (paths i).length := List.toFinset_card_of_nodup (simple i)
  have copiedLengths (i : I) : (copies i).toFinset.card = (paths i).length :=
    (List.toFinset_card_of_nodup (copiesSimple i)).trans (splitListVertices_length paths D i)
  have lengthBound : (∑ i, (copies i).toFinset.card) ≤ Fintype.card I * L :=
    (sum_congr rfl (fun i _ => copiedLengths i)).trans_le length_mass
  exact ⟨splitVertices_card _ hD (by simpa only [lengths] using degree_mass),
    blockIndex_card_bound (fun i => (copies i).toFinset) hL lengthBound,
    regularization_list_mass_caps paths simple D L hD hL⟩

/-- The caps obtained from one plus the integer parts of the two averages
are at most four times the averages in the split family. -/
theorem regularization_list_average_caps (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : Fintype.card V ≤ ∑ i, (paths i).length) (long : Fintype.card I ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    let D := M / Fintype.card V + 1
    let L := M / Fintype.card I + 1
    let copies := splitListVertices paths D
    let after := listRegularizedPaths paths D L
    Fintype.card (ListVertexBlockIndex paths D) ≤ 2 * Fintype.card V ∧
      Fintype.card (ListBlockIndex copies L) ≤ 2 * Fintype.card I ∧
      (∑ i, (after i).length) = M ∧ (∀ i, (after i).length ≤ L) ∧
      (∀ v, (occurrences (fun i => (after i).toFinset) v).card ≤ D) ∧
      D * Fintype.card (ListVertexBlockIndex paths D) ≤ 4 * M ∧
      L * Fintype.card (ListBlockIndex copies L) ≤ 4 * M := by
  let M := ∑ i, (paths i).length
  let n := Fintype.card V
  let p := Fintype.card I
  let D := M/n + 1
  let L := M/p + 1
  have mD : M ≤ n * D := (Nat.lt_mul_div_succ M hn).le
  have mL : M ≤ p * L := (Nat.lt_mul_div_succ M hp).le
  obtain ⟨nCap, pCap, mass, length, degree⟩ := regularization_list_size paths simple D L
    (Nat.succ_pos (M/n)) (Nat.succ_pos (M/p)) mD mL
  exact ⟨nCap, pCap, mass, length, degree, averageWidth_times_card_le dense nCap,
    averageWidth_times_card_le long pCap⟩

section UniqueIntersectionsThroughSix

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

omit [LinearOrder I] [Fintype I] in
theorem contiguousBlocks_separated {paths : I → List V} {width : ℕ}
    {i j : ListBlockIndex paths width} (different : i ≠ j) (same : i.fst = j.fst) :
    (∀ {x y}, x ∈ splitListPaths paths width i → y ∈ splitListPaths paths width j → ListBefore paths i.fst x y) ∨
    (∀ {x y}, x ∈ splitListPaths paths width i → y ∈ splitListPaths paths width j → ListBefore paths i.fst y x) := by
  obtain ⟨i,a⟩ := i
  obtain ⟨j,b⟩ := j
  change i = j at same
  subst j
  have distinct : a.val ≠ b.val := fun eq => different (congrArg (Sigma.mk i) (Fin.ext eq))
  have order {u v : V} {r t : ℕ} (uMem : u ∈ localPathBlock (paths i) width r)
      (vMem : v ∈ localPathBlock (paths i) width t) (lt : r < t) : ListBefore paths i u v := by
    obtain ⟨uOn,rankU⟩ := mem_localPathBlock.mp uMem
    obtain ⟨vOn,rankV⟩ := mem_localPathBlock.mp vMem
    refine ⟨uOn,vOn,?_⟩
    by_contra! reverse
    have divided : (paths i).idxOf v / width ≤ (paths i).idxOf u / width := Nat.div_le_div_right reverse
    rw [rankU,rankV] at divided
    omega
  rcases lt_or_gt_of_ne distinct with ab | ba
  · exact Or.inl (fun h h' => order h h' ab)
  · exact Or.inr (fun h h' => order h' h ba)

omit [Fintype I] in
private theorem sixBlocks_project {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (three : BridgeFree (ListBefore paths) 3) (width : ℕ) {k : ℕ} (short : k ≤ 4)
    (b : Bridge (ListBefore (splitListPaths paths width)) k) :
    ∃ old : Bridge (ListBefore paths) k, old.river = b.river.fst ∧ old.arc = fun i => (b.arc i).fst := by
  let W := ListBlockIndex paths width
  let parent (j : W) := j.fst
  let pieces := splitListPaths paths width
  have steps {i : W} {x y : V} (bc : ListBefore pieces i x y) : ListBefore paths (parent i) x y :=
    listBefore_of_sublist (paths := fun j => paths (parent j)) (simple (parent i)) List.filter_sublist bc
  have together {i j q : W} {x y : V} (_same : parent i = parent j) (diff : parent i ≠ parent q)
      (xy : ListBefore paths (parent i) x y) (yx : ListBefore pieces q y x)
      (_left : x ∈ pieces i) (_right : y ∈ pieces j) : i = j := by
    have step := steps yx
    exact (listBefore_ne xy (unique diff xy.1 step.2.1 xy.2.1 step.1)).elim
  by_cases small : k ≤ 3
  · let old := listBridge_after_opposite_safe_split_through_five parent
      (fun {i _ _} h => steps (i := i) h) (fun {_ _ _} => splitListPaths_disjoint)
      (fun _ {_ _ _ _} diff one two => no_parallel_list_steps three.halfFree (by decide) diff one two)
      (fun _ {_ _ _ _ _} => together) small b
    exact ⟨old,rfl,rfl⟩
  · have kSix : k = 4 := by omega
    subst k
    let old := listBridge_after_contiguous_opposite_safe_split_six parent
      (fun {i _ _} h => steps (i := i) h) (fun {_ _ _} => splitListPaths_disjoint)
      (fun {_ _ _ _ _} => together) (fun {_ _} => contiguousBlocks_separated) three b
    exact ⟨old,rfl,rfl⟩

/-- Contiguous path pieces preserve full six-bridge exclusion with unique
intersections. For half exclusion the vertex projection also needs full
exclusion through size four. -/
theorem regularizedSix_bridge_free {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    {half : Bool} (four : BridgeFree (ListBefore paths) 4)
    (free : if half then HalfBridgeFree (ListBefore paths) 6 else BridgeFree (ListBefore paths) 6)
    (D L : ℕ) :
    if half then HalfBridgeFree (ListBefore (listRegularizedPaths paths D L)) 6
      else BridgeFree (ListBefore (listRegularizedPaths paths D L)) 6 := by
  let copies := splitListVertices paths D
  have copyStep {i : I} {x y : ListVertexBlockIndex paths D} (step : ListBefore copies i x y) :
      ListBefore paths i x.fst y.fst := splitListVertices_step (simple i) step
  have copiedSimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have copyUnique {a b x y} (ne : a ≠ b) (ax : x ∈ copies a) (bx : x ∈ copies b)
      (ay : y ∈ copies a) (by' : y ∈ copies b) : x = y :=
    splitListVertices_unique simple (fun {_ _ _ _} => unique) ne ax bx ay by'
  have oldThree : BridgeFree (ListBefore paths) 3 := fun _ hb => four (hb.trans (by decide))
  have three : BridgeFree (ListBefore copies) 3 :=
    BridgeFree.split_list_vertices_any oldThree (·.fst) (fun {_ _ _} => copyStep)
  cases half
  · have copyFree : BridgeFree (ListBefore copies) 6 :=
      (show BridgeFree (ListBefore paths) 6 from free).split_list_vertices_any (·.fst) (fun {_ _ _} => copyStep)
    intro k hk
    exact ⟨fun b => by
      obtain ⟨old,_,_⟩ := sixBlocks_project copiedSimple (fun {_ _ _ _} => copyUnique) three L (by omega) b
      exact (copyFree hk).false old⟩
  · have copyHalf : HalfBridgeFree (ListBefore copies) 6 :=
      (show HalfBridgeFree (ListBefore paths) 6 from free).split_list_vertices_of_full four (by decide)
        (·.fst) (fun {_ _ _} => copyStep)
    intro k hk b earlier
    obtain ⟨old,river,arcs⟩ := sixBlocks_project copiedSimple (fun {_ _ _ _} => copyUnique) three L (by omega) b
    apply copyHalf hk old
    have sameLast : old.arc (Fin.last k) = (b.arc (Fin.last k)).fst := congrFun arcs _
    have diff : (b.arc (Fin.last k)).fst ≠ b.river.fst := by
      rw [← sameLast,← river]
      exact (old.river_ne_arc _).symm
    rw [sameLast,river]
    have parentLe : (b.arc (Fin.last k)).fst ≤ b.river.fst :=
      (block_parent_mono (fun i => (copies i).toFinset) L) (le_of_lt earlier)
    exact parentLe.lt_of_ne diff

end UniqueIntersectionsThroughSix

end OnlineReachabilityPreservers
