import DirectedFlowCutGap.WeakCutExactMarginal

/-! Padding one self-loop preserves edge threshold demands and bounds the
original weighted cost even when the total is increased. -/
namespace DirectedFlowCutGap.ExactFlowCutGap

noncomputable section

open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

private def addLoop {V : Type*} (G : Digraph V) (v : V) : Digraph V :=
  ⟨fun s t => G.Adj s t ∨ (s,t)=(v,v)⟩

private theorem edgeSet_addLoop {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (v : V) :
    graphEdges (addLoop G v)=insert (v,v) ((graphEdges G).erase (v,v)) := by
  ext e
  simp only [mem_graphEdges,addLoop,Finset.mem_insert,Finset.mem_erase]
  tauto

private theorem oldAdj_of_path {V : Type*} [DecidableEq V] {G : Digraph V} {v s t : V}
    (p : SimplePath (addLoop G v) s t) (i : Fin p.edgeLength) :
    G.Adj (p.vertex i.castSucc) (p.vertex i.succ) := by
  rcases p.adjacent i with old | new
  · exact old
  · exact (p.edge_ne (p.edgeAt_mem_edges i) (by
      change (p.vertex i.castSucc)=(p.vertex i.succ)
      rw [show (p.vertex i.castSucc)=(p.vertex i.succ) from
        (congrArg Prod.fst new).trans (congrArg Prod.snd new).symm])).elim

private theorem transport_factor {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) (w : V × V → ℝ≥0) (v : V) (W : ℝ≥0) (α : ℝ)
    (le_W : totalEdgeWeight G w ≤ W)
    (bound : ∀ H : Digraph V, ∀ q : V × V → ℝ≥0, totalEdgeWeight H q=W →
       HasEdgeRoundingFactor H q α) : HasEdgeRoundingFactor G w α := by
  classical
  let l : V × V := (v,v)
  let E := (graphEdges G).erase l
  let H := addLoop G v
  let pad := W-totalEdgeWeight G w
  let q (e : V × V) := if e=l then actualEdgeWeight G w l+pad else w e
  have edges : graphEdges H=insert l E := edgeSet_addLoop G v
  have outside (e : V × V) (he : e ∈ E) : e≠l := (Finset.mem_erase.mp he).1
  have orig : (∑ e ∈ E, w e)+actualEdgeWeight G w l=totalEdgeWeight G w := by
    by_cases h : l ∈ graphEdges G
    · rw [actualEdgeWeight_of_adj G w ((mem_graphEdges G l).mp h)]
      exact Finset.sum_erase_add _ _ h
    · rw [actualEdgeWeight_of_not_adj G w (fun a => h ((mem_graphEdges G l).mpr a)),add_zero]
      have hE : E=graphEdges G := Finset.erase_eq_of_notMem h
      rw [hE,totalEdgeWeight]
  have exact_weight : totalEdgeWeight H q=W := by
    have sum_eq : (∑ e ∈ E, q e)=(∑ e ∈ E, w e) :=
      Finset.sum_congr rfl fun e he => ite_eq_right (outside e he)
    rw [totalEdgeWeight,edges,Finset.sum_insert (Finset.notMem_erase _ _),sum_eq]
    calc
      _ = ((∑ e ∈ E, w e)+actualEdgeWeight G w l)+pad := by rw [show q l=actualEdgeWeight G w l+pad by simp [q]]; ac_rfl
      _ = W := by rw [orig,add_comm]; exact tsub_add_cancel_of_le le_W
  have oracle := bound H q exact_weight
  refine ⟨oracle.nonneg,?_⟩
  intro c
  let price (e : V × V) := if e=l then (0 : ℝ≥0) else c e
  have query_cost : weightedEdgeCost H price q ≤ weightedEdgeCost G c w := by
    unfold weightedEdgeCost
    rw [edges,Finset.sum_insert (Finset.notMem_erase _ _)]
    simp only [price,ite_true,zero_mul,zero_add]
    calc
      _ = ∑ e ∈ E, c e*w e := Finset.sum_congr rfl fun e he => by
        rw [ite_eq_right (outside e he),show q e=w e from ite_eq_right (outside e he)]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.erase_subset ..)
  obtain ⟨X,actual,hit,cost⟩ := oracle.round price
  let Y := X.filter fun e => e ≠ l
  have Yreal : Y ⊆ graphEdges G := by
    intro e he
    obtain ⟨inX,notLoop⟩ := Finset.mem_filter.mp he
    have same := actual inX
    rw [edges,Finset.mem_insert] at same
    exact (Finset.mem_erase.mp (same.resolve_left notLoop)).2
  have thresholds : edgeThresholdDemands G w ⊆ edgeThresholdDemands H q := by
    rintro ⟨s,t⟩ demanded
    apply (coe_le_edgeDistance_iff H q s t 1).mpr
    intro p
    let old := p.changeGraph (oldAdj_of_path p)
    have hp := (coe_le_edgeDistance_iff G w s t 1).mp demanded old
    have eq : old.edgeWeight w=p.edgeWeight q := by
      rw [SimplePath.edgeWeight,SimplePath.edgeWeight,SimplePath.changeGraph_edges]
      apply Finset.sum_congr rfl
      intro e he
      have h : e≠l := fun eL => (p.edge_ne he) (by rw [eL])
      exact (ite_eq_right h).symm
    exact hp.trans_eq eq
  have Ycut : IsIntegralEdgeCut G Y (edgeThresholdDemands G w) := by
    intro s t demand p
    let lifted : SimplePath H s t := p.changeGraph fun i => Or.inl (p.adjacent i)
    obtain ⟨e,hpath,hX⟩ := hit s t (thresholds demand) lifted
    change e ∈ p.edges at hpath
    have h : e≠l := fun eL => (p.edge_ne hpath) (by rw [eL])
    exact ⟨e,hpath,Finset.mem_filter.mpr ⟨hX,h⟩⟩
  have answer_cost : edgeCutCost G c Y=edgeCutCost H price X := by
    rw [edgeCutCost_eq_sum_of_subset G c Yreal,edgeCutCost_eq_sum_of_subset H price actual]
    simp only [Y,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hl : e=l <;> simp [price,hl]
  refine ⟨Y,Yreal,Ycut,?_⟩
  rw [answer_cost]
  exact cost.trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr query_cost) oracle.nonneg)

/-- A factor valid at a larger total also applies at the original total. -/
theorem edgeBound_of_le {n k : ℕ} (hn : 0<n) {W U : ℝ≥0} (le : W≤U)
    (bound : EdgeBound n U k) : EdgeBound n W k := by
  intro G w exact_W
  exact transport_factor G w ⟨0,hn⟩ U (k : ℝ) (exact_W ▸ le) bound

theorem efg_mono_weight {n : ℕ} (hn : 0<n) {W U : ℝ≥0} (le : W≤U) :
    efg n W ≤ efg n U := efg_le (edgeBound_of_le hn le (efg_bound n U))

/-- The exact factor at `W` supplies the oracle for any instance with total at most `W`. -/
theorem efg_round_atMost {n : ℕ} (hn : 0<n) (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0)
    {W : ℝ≥0} (le : totalEdgeWeight G w≤W) : HasEdgeRoundingFactor G w (efg n W : ℝ) :=
  transport_factor G w ⟨0,hn⟩ W _ le (efg_bound n W)

end
end DirectedFlowCutGap.ExactFlowCutGap
