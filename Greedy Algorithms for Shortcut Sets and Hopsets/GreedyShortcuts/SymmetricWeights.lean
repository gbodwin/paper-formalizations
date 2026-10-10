import GreedyShortcuts.WeightedTransfer

/-! Symmetric weighted-walk foundations for the undirected extension.
The perturbation uses unordered edge codes and preserves symmetric weights. -/
namespace GreedyShortcuts.WeightedPaths

open SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem allowed_reverse {G : V → V → Prop} (hG : Symmetric G)
    {s t : V} {p : DWalk s t} (hp : Allowed G p) : Allowed G p.reverse := by
  intro d hd
  have hm := Walk.mem_darts_reverse.mp hd
  exact hG (hp d.symm hm)

theorem cost_reverse (w : V → V → ℝ≥0) (hw : ∀ s t, w s t = w t s)
    {s t : V} (p : DWalk s t) : cost w p.reverse = cost w p := by
  simp only [cost, Walk.darts_reverse, List.map_reverse, List.map_map, List.sum_reverse]
  congr 1
  apply List.map_congr_left
  intro d hd
  exact congrArg (fun x : ℝ≥0 => (x : ℝ)) (hw d.snd d.fst)

theorem Shortest.reverse {G : V → V → Prop} {w : V → V → ℝ≥0}
    (hG : Symmetric G) (hw : ∀ s t, w s t = w t s)
    {s t : V} {p : DWalk s t} (hp : Shortest G w p) : Shortest G w p.reverse := by
  refine ⟨allowed_reverse hG hp.1, ?_⟩
  intro q hq
  have hh := hp.2 q.reverse (allowed_reverse hG hq)
  simpa only [cost_reverse w hw] using hh

theorem MinHopShortest.reverse {G : V → V → Prop} {w : V → V → ℝ≥0}
    (hG : Symmetric G) (hw : ∀ s t, w s t = w t s)
    {s t : V} {p : DWalk s t} (hp : MinHopShortest G w p) : MinHopShortest G w p.reverse := by
  refine ⟨hp.1.reverse hG hw, ?_⟩
  intro q hq
  simpa only [Walk.length_reverse] using hp.2 q.reverse (hq.reverse hG hw)

theorem reachable_symm {G : V → V → Prop} (hG : Symmetric G)
    {s t : V} (hr : Reachable G s t) : Reachable G t s := by
  obtain ⟨p,hp⟩ := hr
  exact ⟨p.reverse, allowed_reverse hG hp⟩

theorem distance_symm (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (hw : ∀ s t, w s t = w t s) (s t : V) :
    distance G w s t = distance G w t s := by
  classical
  by_cases hr : Reachable G s t
  · have hp := (minHopPath_spec G w s t hr).1
    apply NNReal.coe_injective
    rw [← hp.cost_eq_distance, ← (hp.reverse hG hw).cost_eq_distance, cost_reverse w hw]
  · have hn : ¬ Reachable G t s := fun h => hr (reachable_symm hG h)
    simp [distance, hr, hn]

theorem hopDistance_symm (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (hw : ∀ s t, w s t = w t s) (s t : V) :
    hopDistance G w s t = hopDistance G w t s := by
  classical
  by_cases hr : Reachable G s t
  · have hp := minHopPath_spec G w s t hr
    rw [← hp.length_eq_hopDistance, ← (hp.reverse hG hw).length_eq_hopDistance, Walk.length_reverse]
  · have hn : ¬ Reachable G t s := fun h => hr (reachable_symm hG h)
    simp [hopDistance, hr, hn]

@[simp] theorem codeWeight_symm (s t : V) : codeWeight s t = codeWeight t s := by
  simp only [codeWeight, Sym2.eq_swap]

/-- Lemma 4.2 with the additional symmetry required by an undirected benchmark. -/
theorem exists_symmetric_minhop_reweighting (G : V → V → Prop)
    (w : V → V → ℝ≥0) (hw : ∀ s t, w s t = w t s) :
    ∃ w' : V → V → ℝ≥0, (∀ s t, w' s t = w' t s) ∧
      (∀ s t, 0 < w' s t) ∧ CompatibleReweighting G w w' := by
  obtain ⟨ε,hε,hfirst⟩ := exists_path_perturbation w (fun _ _ => 1)
  let w₁ : V → V → ℝ≥0 := fun u v => w u v + ε * 1
  have hfirst' : ∀ s t (p q : (⊤ : SimpleGraph V).Path s t),
      (cost w p.val < cost w q.val ∨ (cost w p.val = cost w q.val ∧ p.val.length < q.val.length)) →
      cost w₁ p.val < cost w₁ q.val := by
    intro s t p q hpq
    apply hfirst ε hε le_rfl s t p q
    simpa only [cost_unit, Nat.cast_lt] using hpq
  obtain ⟨δ,hδ,hsecond⟩ := exists_path_perturbation w₁ codeWeight
  let w' : V → V → ℝ≥0 := fun u v => w₁ u v + δ * codeWeight u v
  have hpos : ∀ u v, 0 < w' u v := by
    intro u v
    dsimp [w',w₁]
    positivity
  refine ⟨w', ?_, hpos, ?_⟩
  · intro s t
    simp only [w',w₁,hw s t,codeWeight_symm s t]
  · intro s t hr
    obtain ⟨p,hp⟩ := exists_optimal G w₁ s t hr
    refine ⟨p, ?_, minHopShortest_of_comparison hfirst' hp.2.1 (optimal_shortest hp)⟩
    apply uniqueShortest_of_path_comparison (fun u v _ => hpos u v) hp.1
    intro q hq hpath hne
    exact hsecond δ hδ le_rfl s t ⟨p,hp.2.1⟩ ⟨q,hpath⟩
      (optimal_strict_comparison hp hq hpath hne)

end GreedyShortcuts.WeightedPaths
