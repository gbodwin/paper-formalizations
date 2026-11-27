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
  intro d small b earlier
  by_cases short : d ≤ 2
  · have input : HalfBridgeFree (Before paths) 4 := fun _ bound => free (bound.trans (by decide))
    have safe := input.split_list_vertices_short le_rfl project (fun {_ _ _} => steps)
    exact safe (by omega) b earlier
  have size : d = 3 := by omega
  subst d
  have same := (free.project_half_five_terminal_collision project (fun {_ _ _} => steps) b earlier).1
  let v := project (b.vertex 4)
  have second : Before paths (b.arc 1) (project (b.vertex 1)) v := by
    change Before paths (b.arc 1) (project (b.vertex 1)) (project (b.vertex 4))
    rw [← same]
    exact steps (b.arcStep 1)
  let prefixBridge := threeListBridge
    (fun eq => (by decide : (0 : Fin 4) ≠ 1) (b.distinctArcs eq))
    (b.river_ne_arc 0) (b.river_ne_arc 1) (steps (b.arcStep 0)) second (steps b.riverStep)
  have prefixEdge : Edge (halfFiveTerminalRankGraph paths v) b.river (b.arc 1) :=
    halfFiveTerminalRankGraph_edge.mpr (Or.inl ⟨prefixBridge,rfl,rfl,rfl⟩)
  have third : Before paths (b.arc 2) v (project (b.vertex 3)) := by
    change Before paths (b.arc 2) (project (b.vertex 4)) (project (b.vertex 3))
    rw [← same]
    exact steps (b.arcStep 2)
  have returnEdge : Edge (halfFiveTerminalRankGraph paths v) (b.arc 2) (b.arc 3) :=
    halfFiveTerminalRankGraph_edge.mpr (Or.inr ⟨_,third,steps (b.arcStep 3)⟩)
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

end OnlineReachabilityPreservers
