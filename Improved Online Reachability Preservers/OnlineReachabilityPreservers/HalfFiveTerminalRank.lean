import OnlineReachabilityPreservers.HalfFiveProjection
import OnlineReachabilityPreservers.Components

/-! Rank copied vertices using only the two terminal comparisons relevant at half cutoff five. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- At a vertex, compare the river and final arc of each full three-bridge
ending there, and compare the start and end rows of each two-step return. -/
noncomputable def halfFiveTerminalRankGraph {I V : Type*} [DecidableEq I] [Fintype I] [DecidableEq V]
    (paths : I → List V) (v : V) : Arcs I := by
  classical
  exact univ.filter fun e =>
    (∃ b : Bridge (Before paths) 1, b.river = e.1 ∧ b.arc 1 = e.2 ∧ b.vertex 2 = v) ∨
    ∃ u, Before paths e.1 v u ∧ Before paths e.2 u v

theorem halfFiveTerminalRankGraph_edge {I V : Type*} [DecidableEq I] [Fintype I] [DecidableEq V]
    {paths : I → List V} {v : V} {a b : I} :
    Edge (halfFiveTerminalRankGraph paths v) a b ↔
      (∃ t : Bridge (Before paths) 1, t.river = a ∧ t.arc 1 = b ∧ t.vertex 2 = v) ∨
      ∃ u, Before paths a v u ∧ Before paths b u v := by
  classical
  simp only [Edge,halfFiveTerminalRankGraph,mem_filter,mem_univ,true_and]

/-- A three-bridge ending at `v`, followed by a two-step return to `v`.
The projected half-five witness uses five distinct rows and its last
row arrives before the river. -/
structure HalfFiveTerminalPattern {I V : Type*} [LinearOrder I] [DecidableEq V]
    (paths : I → List V) (v : V) where
  triangle : Bridge (Before paths) 1
  terminal : triangle.vertex 2 = v
  outRow : I
  inRow : I
  middle : V
  river_ne_out : triangle.river ≠ outRow
  river_ne_in : triangle.river ≠ inRow
  out_ne_arc : ∀ i, outRow ≠ triangle.arc i
  in_ne_arc : ∀ i, inRow ≠ triangle.arc i
  out_ne_in : outRow ≠ inRow
  outStep : Before paths outRow v middle
  inStep : Before paths inRow middle v
  earlier : inRow < triangle.river

/-- Keep only terminal comparisons used together in a projected
half-five pattern. -/
noncomputable def halfFiveCollisionRankGraph {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    (paths : I → List V) (v : V) : Arcs I := by
  classical
  exact univ.filter fun e => ∃ h : HalfFiveTerminalPattern paths v,
    (h.triangle.river = e.1 ∧ h.triangle.arc 1 = e.2) ∨ (h.outRow = e.1 ∧ h.inRow = e.2)

theorem halfFiveCollisionRankGraph_edge {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    {paths : I → List V} {v : V} {r a : I} :
    Edge (halfFiveCollisionRankGraph paths v) r a ↔ ∃ h : HalfFiveTerminalPattern paths v,
      (h.triangle.river = r ∧ h.triangle.arc 1 = a) ∨ (h.outRow = r ∧ h.inRow = a) := by
  classical
  simp only [Edge,halfFiveCollisionRankGraph,mem_filter,mem_univ,true_and]

/-- Each constraint is one of the broad terminal rank comparisons. -/
theorem halfFiveCollisionRankGraph_subset {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    (paths : I → List V) (v : V) : halfFiveCollisionRankGraph paths v ⊆ halfFiveTerminalRankGraph paths v := by
  rintro ⟨r,a⟩ on
  obtain ⟨h,⟨river,last⟩ | ⟨outRow,inRow⟩⟩ :=
    halfFiveCollisionRankGraph_edge.mp (show Edge (halfFiveCollisionRankGraph paths v) r a from on)
  · exact halfFiveTerminalRankGraph_edge.mpr (Or.inl ⟨h.triangle,river,last,h.terminal⟩)
  · subst r
    subst a
    exact halfFiveTerminalRankGraph_edge.mpr (Or.inr ⟨h.middle,h.outStep,h.inStep⟩)

/-- If no three-bridge ends at a vertex, the collision graph there is empty. -/
theorem halfFiveCollisionRankGraph_empty_of_no_terminal_three {I V : Type*}
    [LinearOrder I] [Fintype I] [DecidableEq V] {paths : I → List V} {v : V}
    (none : ∀ b : Bridge (Before paths) 1, b.vertex 2 ≠ v) :
    halfFiveCollisionRankGraph paths v = ∅ := by
  ext edge
  obtain ⟨r,a⟩ := edge
  constructor
  · intro on
    obtain ⟨h,_⟩ := halfFiveCollisionRankGraph_edge.mp
      (show Edge (halfFiveCollisionRankGraph paths v) r a from on)
    exact (none h.triangle h.terminal).elim
  · simp

private def HalfFiveTerminalPattern.ofBridge {I V W : Type*} [LinearOrder I] [DecidableEq V] [DecidableEq W]
    {paths : I → List V} {copies : I → List W} (b : Bridge (Before copies) 3) (project : W → V)
    (steps : ∀ {i x y}, Before copies i x y → Before paths i (project x) (project y))
    (same : project (b.vertex 2) = project (b.vertex 4)) (earlier : b.arc (Fin.last 3) < b.river) :
    HalfFiveTerminalPattern paths (project (b.vertex 4)) := by
  let v := project (b.vertex 4)
  have second : Before paths (b.arc 1) (project (b.vertex 1)) v := by
    change Before paths (b.arc 1) (project (b.vertex 1)) (project (b.vertex 4))
    rw [← same]
    exact steps (b.arcStep 1)
  let prefixBridge := threeListBridge
    (fun eq => (by decide : (0 : Fin 4) ≠ 1) (b.distinctArcs eq))
    (b.river_ne_arc 0) (b.river_ne_arc 1) (steps (b.arcStep 0)) second (steps b.riverStep)
  have third : Before paths (b.arc 2) v (project (b.vertex 3)) := by
    change Before paths (b.arc 2) (project (b.vertex 4)) (project (b.vertex 3))
    rw [← same]
    exact steps (b.arcStep 2)
  have outApart (i : Fin 2) : b.arc 2 ≠ prefixBridge.arc i := by
    fin_cases i
    · exact fun equal => (by decide : (2 : Fin 4) ≠ 0) (b.distinctArcs equal)
    · exact fun equal => (by decide : (2 : Fin 4) ≠ 1) (b.distinctArcs equal)
  have inApart (i : Fin 2) : b.arc 3 ≠ prefixBridge.arc i := by
    fin_cases i
    · exact fun equal => (by decide : (3 : Fin 4) ≠ 0) (b.distinctArcs equal)
    · exact fun equal => (by decide : (3 : Fin 4) ≠ 1) (b.distinctArcs equal)
  exact ⟨prefixBridge,rfl,b.arc 2,b.arc 3,project (b.vertex 3),
    b.river_ne_arc 2,b.river_ne_arc 3,outApart,inApart,
    fun equal => (by decide : (2 : Fin 4) ≠ 3) (b.distinctArcs equal),third,steps (b.arcStep 3),earlier⟩

/-- The collision graph supplies both rank inequalities at a repeated
projected terminal of a size-five half-bridge. -/
theorem HalfBridgeFree.split_list_vertices_five_of_collision_rank_graph {I V W : Type*}
    [LinearOrder I] [Fintype I] [DecidableEq V] [DecidableEq W]
    {paths : I → List V} {copies : I → List W} (free : HalfBridgeFree (Before paths) 5)
    (project : W → V) (rank : W → ℕ) (assigned : I → V → ℕ)
    (identify : ∀ {x y}, project x = project y → rank x = rank y → x = y)
    (localRank : ∀ {i x}, x ∈ copies i → rank x = assigned i (project x))
    (increases : ∀ v ⦃r a⦄, Edge (halfFiveCollisionRankGraph paths v) r a → assigned r v ≤ assigned a v)
    (steps : ∀ {i x y}, Before copies i x y → Before paths i (project x) (project y)) :
    HalfBridgeFree (Before copies) 5 := by
  intro d small b earlier
  by_cases short : d ≤ 2
  · have input : HalfBridgeFree (Before paths) 4 := fun _ bound => free (bound.trans (by decide))
    have safe := input.split_list_vertices_short le_rfl project (fun {_ _ _} => steps)
    exact safe (by omega) b earlier
  have size : d = 3 := by omega
  subst d
  have same := (free.project_half_five_terminal_collision project (fun {_ _ _} => steps) b earlier).1
  let v := project (b.vertex 4)
  let pattern := HalfFiveTerminalPattern.ofBridge b project (fun {_ _ _} => steps) same earlier
  have prefixEdge : Edge (halfFiveCollisionRankGraph paths v) b.river (b.arc 1) :=
    halfFiveCollisionRankGraph_edge.mpr ⟨pattern,Or.inl ⟨rfl,rfl⟩⟩
  have returnEdge : Edge (halfFiveCollisionRankGraph paths v) (b.arc 2) (b.arc 3) :=
    halfFiveCollisionRankGraph_edge.mpr ⟨pattern,Or.inr ⟨rfl,rfl⟩⟩
  have riverRank : rank (b.vertex 4) = assigned b.river v := localRank b.riverStep.2.1
  have prefixRank : rank (b.vertex 2) = assigned (b.arc 1) v :=
    (localRank (b.arcStep 1).2.1).trans (congrArg (assigned (b.arc 1)) same)
  have startRank : rank (b.vertex 2) = assigned (b.arc 2) v :=
    (localRank (b.arcStep 2).1).trans (congrArg (assigned (b.arc 2)) same)
  have finishRank : rank (b.vertex 4) = assigned (b.arc 3) v := localRank (b.arcStep 3).2.1
  have firstOrder : rank (b.vertex 4) ≤ rank (b.vertex 2) := by
    rw [riverRank,prefixRank]
    exact increases v prefixEdge
  have secondOrder : rank (b.vertex 2) ≤ rank (b.vertex 4) := by
    rw [startRank,finishRank]
    exact increases v returnEdge
  exact (by decide : (2 : Fin 5) ≠ 4) (b.distinctVertices (identify same (le_antisymm secondOrder firstOrder)))

/-- The half-five copy test only needs weak rank inequalities along the
terminal graph at each original vertex. It can allow other incidences
to change their rank order relative to arrival. -/
theorem HalfBridgeFree.split_list_vertices_five_of_terminal_rank_graph {I V W : Type*}
    [LinearOrder I] [Fintype I] [DecidableEq V] [DecidableEq W]
    {paths : I → List V} {copies : I → List W} (free : HalfBridgeFree (Before paths) 5)
    (project : W → V) (rank : W → ℕ) (assigned : I → V → ℕ)
    (identify : ∀ {x y}, project x = project y → rank x = rank y → x = y)
    (localRank : ∀ {i x}, x ∈ copies i → rank x = assigned i (project x))
    (increases : ∀ v ⦃r a⦄, Edge (halfFiveTerminalRankGraph paths v) r a → assigned r v ≤ assigned a v)
    (steps : ∀ {i x y}, Before copies i x y → Before paths i (project x) (project y)) :
    HalfBridgeFree (Before copies) 5 := by
  exact free.split_list_vertices_five_of_collision_rank_graph project rank assigned
    (fun {_ _} => identify) (fun {_ _} => localRank)
    (fun v {_ _} on => increases v (halfFiveCollisionRankGraph_subset paths v on))
    (fun {_ _ _} => steps)

/-- Every assignment increasing weakly on a terminal graph is constant
on its strongly connected components. -/
theorem halfFiveTerminalRank_eq_of_sameComponent {I V : Type*} [DecidableEq I] [Fintype I] [DecidableEq V]
    {paths : I → List V} {v : V} {rank : I → ℕ}
    (increases : ∀ ⦃r a⦄, Edge (halfFiveTerminalRankGraph paths v) r a → rank r ≤ rank a)
    {r a : I} (same : SameComponent (halfFiveTerminalRankGraph paths v) r a) : rank r = rank a := by
  have along {i j} (route : Reach (halfFiveTerminalRankGraph paths v) i j) : rank i ≤ rank j := by
    induction route with
    | refl => exact le_rfl
    | tail _ edge previous => exact previous.trans (increases edge)
  exact le_antisymm (along same.1) (along same.2)

/-- Give each component a distinct rank using its predecessor count and
its representative row as a tie-break. -/
noncomputable def halfFiveTerminalComponentRank {p : ℕ} {V : Type*} [DecidableEq V]
    (paths : Fin p → List V) (v : V) (i : Fin p) : ℕ :=
  let G := halfFiveTerminalRankGraph paths v
  let label := componentLabel G i
  (reaches (condensation G) label).card*p + label.val

private theorem terminalRank_lt_of_count_lt {p : ℕ} {a b : Fin p} {s t : ℕ} (less : s < t) :
    s*p+a.val < t*p+b.val := calc
  _ < s*p+p := Nat.add_lt_add_left a.isLt _
  _ = (s+1)*p := by ring
  _ ≤ t*p := Nat.mul_le_mul_right _ less
  _ ≤ _ := Nat.le_add_right _ _

/-- The component ranks increase weakly along all terminal constraints. -/
theorem halfFiveTerminalComponentRank_increases {p : ℕ} {V : Type*} [DecidableEq V]
    {paths : Fin p → List V} {v : V} {r a : Fin p}
    (edge : Edge (halfFiveTerminalRankGraph paths v) r a) :
    halfFiveTerminalComponentRank paths v r ≤ halfFiveTerminalComponentRank paths v a := by
  let G := halfFiveTerminalRankGraph paths v
  let u := componentLabel G r
  let w := componentLabel G a
  change (reaches (condensation G) u).card*p+u.val ≤ (reaches (condensation G) w).card*p+w.val
  by_cases equal : u = w
  · rw [equal]
  · have condensed : Edge (condensation G) u w := edge_condensation.mpr ⟨equal,r,a,edge,rfl,rfl⟩
    exact (terminalRank_lt_of_count_lt (reaches_card_lt (condensation_dag G) condensed)).le

/-- The distinct ranks identify exactly the pairs forced equal by mutual
reachability in the terminal constraint graph. -/
theorem halfFiveTerminalComponentRank_eq_iff {p : ℕ} {V : Type*} [DecidableEq V]
    {paths : Fin p → List V} {v : V} {r a : Fin p} :
    halfFiveTerminalComponentRank paths v r = halfFiveTerminalComponentRank paths v a ↔
      SameComponent (halfFiveTerminalRankGraph paths v) r a := by
  let G := halfFiveTerminalRankGraph paths v
  let u := componentLabel G r
  let w := componentLabel G a
  let s := (reaches (condensation G) u).card
  let t := (reaches (condensation G) w).card
  rw [← componentLabel_eq]
  change s*p+u.val = t*p+w.val ↔ u = w
  refine ⟨?_,fun equal => by dsimp only [s,t]; rw [equal]⟩
  intro equal
  rcases lt_trichotomy s t with less | same | more
  · exact (terminalRank_lt_of_count_lt (a := u) (b := w) less).ne equal |>.elim
  · apply Fin.ext
    rw [same] at equal
    exact Nat.add_left_cancel equal
  · exact (terminalRank_lt_of_count_lt (a := w) (b := u) more).ne equal.symm |>.elim

open scoped Prod.Lex

/-- A copy is identified by its original vertex and its assigned rank. -/
def halfFiveRankedVertexCopies {I V : Type*} (paths : I → List V)
    (assigned : I → V → ℕ) (i : I) : List (V ×ₗ ℕ) :=
  (paths i).map fun v => toLex (v,assigned i v)

theorem halfFiveRankedVertexCopies_project {I V : Type*} (paths : I → List V)
    (assigned : I → V → ℕ) (i : I) :
    (halfFiveRankedVertexCopies paths assigned i).map (fun x => (ofLex x).1) = paths i := by
  simp [halfFiveRankedVertexCopies,List.map_map,Function.comp_def]

theorem halfFiveRankedVertexCopies_simple {I V : Type*} {paths : I → List V}
    (simple : ∀ i, (paths i).Nodup) (assigned : I → V → ℕ) (i : I) :
    (halfFiveRankedVertexCopies paths assigned i).Nodup :=
  (simple i).map (fun _ _ equal => congrArg (fun x => (ofLex x).1) equal)

/-- Ranks satisfying the collision graph give explicit half-five-free copied rows. -/
theorem halfFiveRankedVertexCopies_halfFree_of_collision_graph {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    {paths : I → List V} (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (assigned : I → V → ℕ)
    (increases : ∀ v ⦃r a⦄, Edge (halfFiveCollisionRankGraph paths v) r a → assigned r v ≤ assigned a v) :
    HalfBridgeFree (Before (halfFiveRankedVertexCopies paths assigned)) 5 := by
  let project (x : V ×ₗ ℕ) := (ofLex x).1
  let rank (x : V ×ₗ ℕ) := (ofLex x).2
  have identify {x y : V ×ₗ ℕ} (same : project x = project y) (equal : rank x = rank y) : x = y :=
    ofLex.injective (Prod.ext same equal)
  have assignedHere {i x} (member : x ∈ halfFiveRankedVertexCopies paths assigned i) :
      rank x = assigned i (project x) := by
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp member
    rfl
  have step {i x y} (comparison : Before (halfFiveRankedVertexCopies paths assigned) i x y) :
      Before paths i (project x) (project y) := by
    have projected (i : I) : ((halfFiveRankedVertexCopies paths assigned i).map project) = paths i :=
      halfFiveRankedVertexCopies_project paths assigned i
    have found := listBefore_map project ((projected i).symm ▸ simple i) comparison
    simpa only [SourceAudit.BeforeIn,projected] using found
  exact free.split_list_vertices_five_of_collision_rank_graph project rank assigned
    (fun {_ _} => identify) (fun {_ _} => assignedHere) (fun v {_ _} edge => increases v edge) (fun {_ _ _} => step)

/-- Weakly increasing local ranks give explicit half-five-free copied rows. -/
theorem halfFiveRankedVertexCopies_halfFree {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    {paths : I → List V} (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (assigned : I → V → ℕ)
    (increases : ∀ v ⦃r a⦄, Edge (halfFiveTerminalRankGraph paths v) r a → assigned r v ≤ assigned a v) :
    HalfBridgeFree (Before (halfFiveRankedVertexCopies paths assigned)) 5 := by
  exact halfFiveRankedVertexCopies_halfFree_of_collision_graph simple free assigned
    (fun v {_ _} on => increases v (halfFiveCollisionRankGraph_subset paths v on))

local instance prefixComparisonDecidable {I V : Type*} [DecidableEq V] (rows : I → List V) (i : I) (x y : V) :
    Decidable (Before rows i x y) := by
  unfold SourceAudit.BeforeIn
  infer_instance

/-- Consider all strict path comparisons outside the two specified rows.
A bridge detour can use this graph until it takes its final arc. -/
def bridgePrefixGraph {I V : Type*} [DecidableEq I] [Fintype I] [DecidableEq V] [Fintype V]
    (rows : I → List V) (river final : I) : Arcs V :=
  univ.filter fun e => ∃ i, i ≠ river ∧ i ≠ final ∧ Before rows i e.1 e.2

/-- The prefix of a bridge detour avoids both its river and final arc. -/
theorem Bridge.reaches_prefix_excluding_river_and_final {I V : Type*}
    [DecidableEq I] [Fintype I] [DecidableEq V] [Fintype V]
    {rows : I → List V} {d : ℕ} (b : Bridge (Before rows) d) :
    Reach (bridgePrefixGraph rows b.river (b.arc (Fin.last d)))
      (b.vertex 0) (b.vertex (Fin.last d).castSucc) := by
  let a := b.arc (Fin.last d)
  let G := bridgePrefixGraph rows b.river a
  have reachesPrefix : ∀ (m : ℕ) (room : m < d+1),
      Reach G (b.vertex 0) (b.vertex (⟨m,room⟩ : Fin (d+1)).castSucc) := by
    intro m
    induction m with
    | zero => intro room; exact .refl
    | succ m previous =>
      intro room
      let i : Fin (d+1) := ⟨m,by omega⟩
      have notFinal : i ≠ Fin.last d := by
        intro equal
        have index := congrArg Fin.val equal
        change m = d at index
        omega
      have edge : Edge G (b.vertex i.castSucc) (b.vertex i.succ) :=
        mem_filter.mpr ⟨mem_univ _,b.arc i,(b.river_ne_arc i).symm,
          fun eq => notFinal (b.distinctArcs eq),b.arcStep i⟩
      exact (previous i.isLt).tail edge
  exact reachesPrefix d (Nat.lt_succ_self _)

/-- The copied endpoints of consecutive comparisons agree, including
those shared with the river. The two copies of the projected terminal
stay distinct. -/
structure HalfFiveTerminalPattern.Realized {I V : Type*} [LinearOrder I] [DecidableEq V]
    {paths : I → List V} {v : V} (h : HalfFiveTerminalPattern paths v) (assigned : I → V → ℕ) : Prop where
  source : assigned h.triangle.river (h.triangle.vertex 0) = assigned (h.triangle.arc 0) (h.triangle.vertex 0)
  firstJoin : assigned (h.triangle.arc 0) (h.triangle.vertex 1) = assigned (h.triangle.arc 1) (h.triangle.vertex 1)
  terminalJoin : assigned (h.triangle.arc 1) v = assigned h.outRow v
  returnJoin : assigned h.outRow h.middle = assigned h.inRow h.middle
  riverEnd : assigned h.inRow v = assigned h.triangle.river v
  copiesApart : assigned (h.triangle.arc 1) v ≠ assigned h.triangle.river v

private theorem halfFiveRankedVertexCopies_rank_of_mem {I V : Type*} {paths : I → List V}
    {assigned : I → V → ℕ} {i : I} {w : V ×ₗ ℕ}
    (member : w ∈ halfFiveRankedVertexCopies paths assigned i) :
    (ofLex w).2 = assigned i (ofLex w).1 := by
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp member
  rfl

private theorem halfFiveRankedVertexCopies_lift_step {I V : Type*} [DecidableEq V]
    {paths : I → List V} {assigned : I → V → ℕ}
    (simple : ∀ i, (paths i).Nodup) {i : I} {x y : V} (step : Before paths i x y) :
    Before (halfFiveRankedVertexCopies paths assigned) i
      (toLex (x,assigned i x)) (toLex (y,assigned i y)) := by
  let _ : BEq (V ×ₗ ℕ) := instBEqOfDecidableEq
  let f (v : V) : V ×ₗ ℕ := toLex (v,assigned i v)
  have index (v : V) (member : v ∈ paths i) :
      (halfFiveRankedVertexCopies paths assigned i).idxOf (f v) = (paths i).idxOf v := by
    let pos := (paths i).idxOf v
    have bounded : pos < (paths i).length := List.idxOf_lt_length_of_mem member
    have room : pos < (halfFiveRankedVertexCopies paths assigned i).length := by
      simpa only [halfFiveRankedVertexCopies,List.length_map] using bounded
    have roomMap : pos < ((paths i).map f).length := by
      simpa only [List.length_map] using bounded
    have mappedItem : ((paths i).map f)[pos]'roomMap = f v := by
      rw [List.getElem_map,List.getElem_idxOf bounded]
    have item : (halfFiveRankedVertexCopies paths assigned i)[pos]'room = f v := mappedItem
    rw [← item]
    exact (halfFiveRankedVertexCopies_simple simple assigned i).idxOf_getElem pos room
  refine ⟨List.mem_map_of_mem step.1,List.mem_map_of_mem step.2.1,?_⟩
  change (halfFiveRankedVertexCopies paths assigned i).idxOf (f x) <
    (halfFiveRankedVertexCopies paths assigned i).idxOf (f y)
  rw [index x step.1,index y step.2.1]
  exact step.2.2

/-- Any projected pattern with matching joins and distinct copies of its
terminal gives a forbidden copied half-five, under half-five exclusion
in the original rows. -/
theorem HalfFiveTerminalPattern.realized_forbids_halfFive {I V : Type*} [LinearOrder I] [DecidableEq V]
    {paths : I → List V} {v : V} (h : HalfFiveTerminalPattern paths v) (assigned : I → V → ℕ)
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (realized : h.Realized assigned) : ¬ HalfBridgeFree (Before (halfFiveRankedVertexCopies paths assigned)) 5 := by
  let r := h.triangle.river
  let a := h.triangle.arc 0
  let b := h.triangle.arc 1
  let c := h.outRow
  let e := h.inRow
  let s := h.triangle.vertex 0
  let t := h.triangle.vertex 1
  let w := h.middle
  let copy (i : I) (x : V) : V ×ₗ ℕ := toLex (x,assigned i x)
  have riverStep : Before paths r s v := by
    rw [← h.terminal]
    exact h.triangle.riverStep
  have firstStep : Before paths a s t := h.triangle.arcStep 0
  have secondStep : Before paths b t v := by
    rw [← h.terminal]
    exact h.triangle.arcStep 1
  have st : s ≠ t := listBefore_ne firstStep
  have sv : s ≠ v := listBefore_ne riverStep
  have tv : t ≠ v := listBefore_ne secondStep
  have vw : v ≠ w := listBefore_ne h.outStep
  have sw : s ≠ w := by
    intro same
    have parallel : Before paths e s v := same.symm ▸ h.inStep
    exact no_parallel_list_steps free (by decide) h.river_ne_in riverStep parallel
  have tw : t ≠ w := by
    intro same
    have returnStep : Before paths e t v := same.symm ▸ h.inStep
    let alternate := threeListBridge (h.in_ne_arc 0).symm (h.triangle.river_ne_arc 0) h.river_ne_in
      firstStep returnStep riverStep
    exact free (by decide : 1+2 ≤ 5) alternate h.earlier
  let vtx : Fin 5 → V ×ₗ ℕ := ![copy r s,copy a t,copy b v,copy c w,copy r v]
  have different : Function.Injective vtx := by
    intro i j same
    have projected := congrArg (fun x => (ofLex x).1) same
    have ranked := congrArg (fun x => (ofLex x).2) same
    have ranksApart : assigned b v ≠ assigned r v := realized.copiesApart
    fin_cases i <;> fin_cases j <;> simp_all [vtx,copy]
  let arc : Fin 4 → I := ![a,b,c,e]
  have arcApart : Function.Injective arc := by
    intro i j equal
    have ab : a ≠ b := fun eq => (by decide : (0 : Fin 2) ≠ 1) (h.triangle.distinctArcs eq)
    have ca : c ≠ a := h.out_ne_arc 0
    have cb : c ≠ b := h.out_ne_arc 1
    have ea : e ≠ a := h.in_ne_arc 0
    have eb : e ≠ b := h.in_ne_arc 1
    have ce : c ≠ e := h.out_ne_in
    fin_cases i <;> fin_cases j <;> simp_all [arc]
  have riverApart (i : Fin 4) : r ≠ arc i := by
    fin_cases i
    · exact h.triangle.river_ne_arc 0
    · exact h.triangle.river_ne_arc 1
    · exact h.river_ne_out
    · exact h.river_ne_in
  have liftedArcs (i : Fin 4) :
      Before (halfFiveRankedVertexCopies paths assigned) (arc i) (vtx i.castSucc) (vtx i.succ) := by
    fin_cases i
    · change Before (halfFiveRankedVertexCopies paths assigned) a (copy r s) (copy a t)
      rw [show copy r s = copy a s from congrArg (fun q => toLex (s,q)) realized.source]
      exact halfFiveRankedVertexCopies_lift_step simple firstStep
    · change Before (halfFiveRankedVertexCopies paths assigned) b (copy a t) (copy b v)
      rw [show copy a t = copy b t from congrArg (fun q => toLex (t,q)) realized.firstJoin]
      exact halfFiveRankedVertexCopies_lift_step simple secondStep
    · change Before (halfFiveRankedVertexCopies paths assigned) c (copy b v) (copy c w)
      rw [show copy b v = copy c v from congrArg (fun q => toLex (v,q)) realized.terminalJoin]
      exact halfFiveRankedVertexCopies_lift_step simple h.outStep
    · change Before (halfFiveRankedVertexCopies paths assigned) e (copy c w) (copy r v)
      rw [show copy c w = copy e w from congrArg (fun q => toLex (w,q)) realized.returnJoin,
        show copy r v = copy e v from congrArg (fun q => toLex (v,q)) realized.riverEnd.symm]
      exact halfFiveRankedVertexCopies_lift_step simple h.inStep
  let lifted : Bridge (Before (halfFiveRankedVertexCopies paths assigned)) 3 :=
    ⟨vtx,arc,r,different,arcApart,riverApart,halfFiveRankedVertexCopies_lift_step simple riverStep,liftedArcs⟩
  exact fun legal => legal (by decide : 3+2 ≤ 5) lifted h.earlier

/-- Half-five exclusion of an explicit rank assignment is equivalent to
absence of a projected terminal pattern with every join realized. -/
theorem halfFiveRankedVertexCopies_halfFree_iff_no_realized_terminal_pattern {I V : Type*}
    [LinearOrder I] [DecidableEq V] {paths : I → List V}
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5) (assigned : I → V → ℕ) :
    HalfBridgeFree (Before (halfFiveRankedVertexCopies paths assigned)) 5 ↔
      ∀ v (h : HalfFiveTerminalPattern paths v), ¬ h.Realized assigned := by
  constructor
  · exact fun legal _ h realized => h.realized_forbids_halfFive assigned simple free realized legal
  · intro none d small copied earlier
    let project (x : V ×ₗ ℕ) := (ofLex x).1
    let rank (x : V ×ₗ ℕ) := (ofLex x).2
    have step {i x y} (found : Before (halfFiveRankedVertexCopies paths assigned) i x y) :
        Before paths i (project x) (project y) := by
      have shape (i : I) : ((halfFiveRankedVertexCopies paths assigned i).map project) = paths i :=
        halfFiveRankedVertexCopies_project paths assigned i
      have old := listBefore_map project ((shape i).symm ▸ simple i) found
      simpa only [SourceAudit.BeforeIn,shape] using old
    by_cases short : d ≤ 2
    · have input : HalfBridgeFree (Before paths) 4 := fun _ bound => free (bound.trans (by decide))
      have safe := input.split_list_vertices_short le_rfl project (fun {_ _ _} => step)
      exact safe (by omega) copied earlier
    have size : d = 3 := by omega
    subst d
    have same := (free.project_half_five_terminal_collision project (fun {_ _ _} => step) copied earlier).1
    let v := project (copied.vertex 4)
    let pattern := HalfFiveTerminalPattern.ofBridge copied project (fun {_ _ _} => step) same earlier
    apply none v pattern
    have seen {i x} (member : x ∈ halfFiveRankedVertexCopies paths assigned i) :
        rank x = assigned i (project x) := halfFiveRankedVertexCopies_rank_of_mem member
    have atRiver : rank (copied.vertex 4) = assigned copied.river v := seen copied.riverStep.2.1
    have atPrefix : rank (copied.vertex 2) = assigned (copied.arc 1) v :=
      (seen (copied.arcStep 1).2.1).trans (congrArg (assigned (copied.arc 1)) same)
    have atOut : rank (copied.vertex 2) = assigned (copied.arc 2) v :=
      (seen (copied.arcStep 2).1).trans (congrArg (assigned (copied.arc 2)) same)
    refine ⟨(seen copied.riverStep.1).symm.trans (seen (copied.arcStep 0).1),
      (seen (copied.arcStep 0).2.1).symm.trans (seen (copied.arcStep 1).1),atPrefix.symm.trans atOut,
      (seen (copied.arcStep 2).2.1).symm.trans (seen (copied.arcStep 3).1),
      (seen (copied.arcStep 3).2.1).symm.trans atRiver,?_⟩
    intro equal
    have sameRank := atPrefix.trans (equal.trans atRiver.symm)
    have eqCopies : copied.vertex 2 = copied.vertex 4 := ofLex.injective (Prod.ext same sameRank)
    exact (by decide : (2 : Fin 5) ≠ 4) (copied.distinctVertices eqCopies)

end OnlineReachabilityPreservers
