import MinorFreeSpanners.Greedy

/-! An actual family of three-vertex greedy outputs refutes the literal
weighted-girth inequality in Claim 19, for arbitrarily small sε > 0. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {V : Type*}

theorem length_mul_le_walkWeight {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (w : Sym2 V → ℝ) (m : ℝ)
    (hw : ∀ e ∈ p.edges, m ≤ w e) : p.length * m ≤ walkWeight w p := by
  induction p with
  | nil => simp
  | @cons u v z h p ih =>
    have hh := hw s(u,v) (by simp)
    have ht := ih (fun e he => hw e (by simp [he]))
    simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one, walkWeight_cons]
    nlinarith

/-- A positive lower edge weight makes sufficiently low-stretch spanners
rigid. The conclusion is equality of actual graphs, not a numeric model. -/
theorem spanner_eq_of_two_edge_gap {G H : SimpleGraph V} {w : Sym2 V → ℝ}
    {t m : ℝ} (hm : 0 < m) (hw : ∀ e, m ≤ w e)
    (hgap : ∀ e ∈ G.edgeSet, t * w e < 2*m)
    (hspan : IsSpanner G H w t) : H = G := by
  apply le_antisymm hspan.1
  intro u v huv
  obtain ⟨p, hp⟩ := hspan.2 u v huv.toWalk
  have hcost : walkWeight w p < 2*m := by
    simp only [SimpleGraph.Adj.toWalk, walkWeight_cons, walkWeight_nil, add_zero] at hp
    exact hp.trans_lt (hgap _ ((mem_edgeSet G).mpr huv))
  have hlen : (p.length : ℝ) < 2 :=
    (mul_lt_mul_iff_of_pos_right hm).mp
      ((length_mul_le_walkWeight p w m (fun e _ => hw e)).trans_lt hcost)
  have hlt : p.length < 2 := by exact_mod_cast hlen
  have hn : p.length ≠ 0 := fun hz => huv.ne (p.eq_of_length_eq_zero hz)
  exact Walk.adj_of_length_eq_one (p := p) (by omega)

/-- When each edge is no longer than two minimum-weight edges, its direct
walk realizes the weighted distance. This checks the source's metric-edge
normalization for the counterexample, rather than assuming it. -/
theorem metric_edge_of_two_edge_bound {G : SimpleGraph V} {w : Sym2 V → ℝ}
    {m : ℝ} (hm : 0 ≤ m) (hw : ∀ e, m ≤ w e)
    (hupper : ∀ e ∈ G.edgeSet, w e ≤ 2*m) {u v : V} (huv : G.Adj u v) :
    weightedDistance G w u v = ENNReal.ofReal (w s(u,v)) := by
  apply le_antisymm
  · exact (iInf_le_of_le huv.toWalk (by simp [SimpleGraph.Adj.toWalk]))
  · apply le_iInf
    intro p
    apply ENNReal.ofReal_le_ofReal
    cases p with
    | nil => exact (huv.ne rfl).elim
    | @cons u x v h p =>
      cases p with
      | nil => simp
      | @cons x y v h' q =>
        simp only [walkWeight_cons]
        have hq := walkWeight_nonneg w (fun e => hm.trans (hw e)) q
        have he := hupper s(u,v) ((mem_edgeSet G).mpr huv)
        linarith [hw s(u,x), hw s(x,y)]

abbrev triangle : SimpleGraph (Fin 3) := ⊤

noncomputable def triangleWeight (a : ℝ) (e : Sym2 (Fin 3)) : ℝ :=
  if e = s(0,1) then 1 else (1 + 3*a/2)/2

private theorem triangle_adj01 : triangle.Adj 0 1 := by decide
private theorem triangle_adj12 : triangle.Adj 1 2 := by decide
private theorem triangle_adj20 : triangle.Adj 2 0 := by decide

def triangleCycle : triangle.Walk 0 0 :=
  .cons triangle_adj01 (.cons triangle_adj12 (.cons triangle_adj20 .nil))

theorem triangleCycle_isCycle : triangleCycle.IsCycle := by
  simp [triangleCycle, Walk.cons_isCycle_iff, Walk.isPath_def, Sym2.eq_iff]

/-- For 0<a<2/3 every edge is retained by the actual greedy algorithm at
stretch 1+a. The family works for a=sε arbitrarily close to zero. -/
theorem triangle_greedy_eq (a : ℝ) (ha : 0 < a) (ha' : a < 2/3) :
    greedyOutput triangle (triangleWeight a) (1+a) = triangle := by
  have hm : 0 < (1+3*a/2)/2 := by linarith
  have hw : ∀ e, (1+3*a/2)/2 ≤ triangleWeight a e := by
    intro e
    unfold triangleWeight
    split_ifs <;> linarith
  apply spanner_eq_of_two_edge_gap (t := 1+a) hm hw
  · intro e he
    unfold triangleWeight
    split_ifs
    · nlinarith
    · exact mul_lt_mul_of_pos_right (by linarith) hm
  · exact greedy_spanner triangle (triangleWeight a) (1+a) (by linarith)
      (fun e => hm.le.trans (hw e))

/-- Literal Claim 19 is false already for k=1: its claimed threshold is
2(1+a), whereas this retained cycle has weight 2+3a/2 and maximum weight1. -/
theorem claim19_literal_false (a : ℝ) (ha : 0 < a) (ha' : a < 2/3) :
    ¬ WeightedGirthAbove (greedyOutput triangle (triangleWeight a) (1+a))
      (triangleWeight a) ((1+a)*2) := by
  rw [triangle_greedy_eq a ha ha']
  intro h
  have hh := h 0 triangleCycle triangleCycle_isCycle s(0,1) (by simp [triangleCycle])
  norm_num [triangleCycle, triangleWeight, walkWeight, Sym2.eq_iff] at hh
  linarith


theorem triangle_weights_positive (a : ℝ) (ha : 0 < a) :
    ∀ e, 0 < triangleWeight a e := by
  intro e
  unfold triangleWeight
  split_ifs <;> linarith

theorem triangle_minorFree : CliqueMinorFree triangle 4 :=
  cliqueMinorFree_of_card_lt triangle 4 (by decide)

theorem triangle_metric_edges (a : ℝ) (ha : 0 < a) (ha' : a < 2/3)
    (u v : Fin 3) (huv : triangle.Adj u v) :
    weightedDistance triangle (triangleWeight a) u v =
      ENNReal.ofReal (triangleWeight a s(u,v)) := by
  apply metric_edge_of_two_edge_bound (m := (1+3*a/2)/2) (by linarith) _ _ huv
  · intro e
    unfold triangleWeight
    split_ifs <;> linarith
  · intro e he
    unfold triangleWeight
    split_ifs <;> linarith

/-- Explicit ε-form: the literal weighted-girth claim fails with k=1,
for every positive sε<2/3, on a K₄-minor-free metric graph. -/
theorem claim19_counterexample_with_source_hypotheses (s ε : ℝ)
    (ha : 0 < s*ε) (ha' : s*ε < 2/3) :
    CliqueMinorFree triangle 4 ∧
    (∀ e, 0 < triangleWeight (s*ε) e) ∧
    (∀ u v, triangle.Adj u v → weightedDistance triangle (triangleWeight (s*ε)) u v =
      ENNReal.ofReal (triangleWeight (s*ε) s(u,v))) ∧
    ¬ WeightedGirthAbove (greedyOutput triangle (triangleWeight (s*ε)) (1+s*ε))
      (triangleWeight (s*ε)) ((1+s*ε)*2) :=
  ⟨triangle_minorFree, triangle_weights_positive (s*ε) ha,
    triangle_metric_edges (s*ε) ha ha', claim19_literal_false (s*ε) ha ha'⟩

end MinorFreeSpanners
