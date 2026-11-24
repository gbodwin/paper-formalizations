import DirectedFlowCutGap.RationalSparsestEdgeDistances

/-! Express average-distance normalization by per-demand vertex potentials.
Each potential has one inequality per actual arc. Truncating distances at
the requested sum gives feasible potentials even for unrelated vertices. -/
namespace DirectedFlowCutGap.SparsestNormalizedPotentials

open scoped BigOperators NNReal NNRat ENNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalSparsestEdgeDistances (distance observe distance_exact)

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

structure Feasible (G : Digraph V) (w : V × V → ℝ≥0) (P : Fin m → V × V)
    (target : ℝ≥0) (potential : Fin m → V → ℝ≥0) : Prop where
  start : ∀ i, potential i (P i).1=0
  arc : ∀ i u v, G.Adj u v → potential i v≤potential i u+w (u,v)
  total : target≤∑ i, potential i (P i).2

omit [Fintype V] [DecidableEq V] in
private theorem walk_bound {G : Digraph V} (w : V × V → ℝ≥0) (p : V → ℝ≥0)
    (edges : ∀ u v, G.Adj u v → p v≤p u+w (u,v)) {s t : V} (walk : DirectedWalk G s t) :
    p t≤p s+walk.edgeWeight w := by
  induction walk with
  | refl => rw [DirectedWalk.edgeWeight,add_zero]
  | @cons u v t adj rest ih =>
    rw [DirectedWalk.edgeWeight,← add_assoc]
    exact ih.trans (add_le_add (edges u v adj) le_rfl)

omit [Fintype V] in
theorem potential_le_distance (G : Digraph V) (w : V × V → ℝ≥0) (p : V → ℝ≥0)
    (s t : V) (start : p s=0) (edges : ∀ u v, G.Adj u v → p v≤p u+w (u,v)) :
    (p t : ℝ≥0∞)≤edgeDistance G w s t := by
  apply (le_edgeDistance_iff_all_walks G w s t _).mpr
  intro walk
  have width := walk_bound w p edges walk
  rw [start,zero_add] at width
  exact ENNReal.coe_le_coe.mpr width

noncomputable def capped (G : Digraph V) (w : V × V → ℝ≥0)
    (C : ℝ≥0) (s v : V) : ℝ≥0 :=
  (min (edgeDistance G w s v) (C : ℝ≥0∞)).toNNReal

omit [Fintype V] in
theorem capped_value (G : Digraph V) (w : V × V → ℝ≥0) (C : ℝ≥0) (s v : V) :
    (capped G w C s v : ℝ≥0∞)=min (edgeDistance G w s v) (C : ℝ≥0∞) := by
  apply ENNReal.coe_toNNReal
  exact ne_of_lt ((min_le_right _ _).trans_lt ENNReal.coe_lt_top)

theorem capped_arc (G : Digraph V) (w : V × V → ℝ≥0) (C : ℝ≥0) (s u v : V) (arc : G.Adj u v) :
    capped G w C s v≤capped G w C s u+w (u,v) := by
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_add,capped_value,capped_value]
  by_cases h : (C : ℝ≥0∞)≤edgeDistance G w s u
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (le_self_add)
  · rw [min_eq_left (le_of_not_ge h)]
    exact (min_le_left _ _).trans ((edgeDistance_triangle G w s u v).trans
      (add_le_add le_rfl (edgeDistance_le_of_adj w arc)))

private theorem capped_sum {d : Fin m → ℝ≥0} {C : ℝ≥0} (enough : C≤∑ i, d i) :
    C≤∑ i, min (d i) C := by
  by_cases respects : ∀ i, d i≤C
  · simpa only [fun i => min_eq_left (respects i)] using enough
  · obtain ⟨j,big⟩ := not_forall.mp respects
    have bound := Finset.single_le_sum (fun i _ => (zero_le : 0 ≤ min (d i) C)) (Finset.mem_univ j)
    rwa [min_eq_right (le_of_not_ge big)] at bound

theorem normalization_iff (G : Digraph V) (w : V × V → ℝ≥0) (P : Fin m → V × V) (target : ℝ≥0)
    (reachable : ∀ i, edgeDistance G w (P i).1 (P i).2≠⊤) :
    (∃ p, Feasible G w P target p) ↔ target≤∑ i, SparsestEdgeBridge.demandDistance G w (P i) := by
  constructor
  · rintro ⟨p,good⟩
    apply good.total.trans
    apply Finset.sum_le_sum
    intro i _
    have bound := potential_le_distance G w (p i) (P i).1 (P i).2 (good.start i) (good.arc i)
    unfold SparsestEdgeBridge.demandDistance
    exact ENNReal.coe_le_coe.mp (((ENNReal.coe_toNNReal (reachable i)).symm) ▸ bound)
  · intro enough
    refine ⟨fun i => capped G w target (P i).1,⟨?_,?_,?_⟩⟩
    · intro i
      simp [capped]
    · exact fun i u v edge => capped_arc G w target (P i).1 u v edge
    · have same (i : Fin m) : capped G w target (P i).1 (P i).2 =
          min (SparsestEdgeBridge.demandDistance G w (P i)) target := by
        apply ENNReal.coe_injective
        rw [capped_value,ENNReal.coe_min,SparsestEdgeBridge.demandDistance,ENNReal.coe_toNNReal (reachable i)]
      simp only [same]
      exact capped_sum enough

def table {n : ℕ} (A : Adjacency n) (w : Weights n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) : Vector (Vector ℚ≥0 n) m :=
  Vector.ofFn fun i => Vector.ofFn fun v => min ((distance A w ((P i).1,v)).getD target) target

theorem table_value {n : ℕ} (A : Adjacency n) (w : Weights n) (P : Fin m → Fin n × Fin n) (target : ℚ≥0)
    (i : Fin m) (v : Fin n) :
    ((table A w P target)[i.val][v.val] : ℝ≥0)=capped (graph A) (weights w) (target : ℝ≥0) (P i).1 v := by
  simp only [table,Vector.getElem_ofFn]
  apply ENNReal.coe_injective
  rw [capped_value,←distance_exact A w ((P i).1,v)]
  cases result : distance A w ((P i).1,v) with
  | none => simp [observe]
  | some d =>
    simp only [Option.getD_some,observe]
    congr 1
    by_cases fits : d≤target
    · rw [min_eq_left fits,min_eq_left ((NNRat.cast_le (K := ℝ≥0)).mpr fits)]
    · have back := le_of_not_ge fits
      rw [min_eq_right back,min_eq_right ((NNRat.cast_le (K := ℝ≥0)).mpr back)]

end DirectedFlowCutGap.SparsestNormalizedPotentials
