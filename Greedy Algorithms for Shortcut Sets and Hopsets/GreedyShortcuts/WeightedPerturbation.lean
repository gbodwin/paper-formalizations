import GreedyShortcuts.WeightedPaths
import LinearDistancePreservers.FinitePerturbation

/-!
Lemma 4.2 of Bodwin et al., Greedy Algorithms for Shortcut Sets and Hopsets.
A single actual positive real edge reweighting simultaneously gives every
reachable ordered vertex pair a unique shortest walk, and that walk is an
original minimum-hop shortest path. Two finite perturbations realize the
paper's hop penalty and tie-breaking. The tie-break is deterministic.
-/
namespace GreedyShortcuts.WeightedPaths

open SimpleGraph
open GreedyShortcuts.DirectedPaths
open LinearDistancePreservers
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite comparison set includes native simple paths for every pair of
endpoints, so one edge-weight perturbation works throughout the graph. -/
theorem exists_path_perturbation (w₀ w₁ : V → V → ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ ε →
      ∀ s t (p q : (⊤ : SimpleGraph V).Path s t),
      (cost w₀ p.val < cost w₀ q.val ∨
        (cost w₀ p.val = cost w₀ q.val ∧ cost w₁ p.val < cost w₁ q.val)) →
      cost (fun u v => w₀ u v + δ * w₁ u v) p.val <
        cost (fun u v => w₀ u v + δ * w₁ u v) q.val := by
  classical
  let X := Σ s : V, Σ t : V, (⊤ : SimpleGraph V).Path s t
  let f : X → ℝ := fun p => cost w₀ p.2.2.val
  let g : X → ℝ := fun p => cost w₁ p.2.2.val
  obtain ⟨ε, hε, hcompare⟩ := exists_uniform_perturbation f g
  refine ⟨⟨ε, hε.le⟩, ?_, ?_⟩
  · exact_mod_cast hε
  · intro δ hδ hδε s t p q hpq
    rw [cost_add_scale, cost_add_scale]
    exact hcompare (δ : ℝ) (by exact_mod_cast hδ) (by exact_mod_cast hδε)
      ⟨s,t,p⟩ ⟨s,t,q⟩ hpq

/-- Any simple path shortest after a perturbation preserving weight then hop
comparisons is an original minimum-hop shortest walk. -/
theorem minHopShortest_of_comparison {G : V → V → Prop}
    {w w₁ : V → V → ℝ≥0}
    (hcompare : ∀ s t (p q : (⊤ : SimpleGraph V).Path s t),
      (cost w p.val < cost w q.val ∨
        (cost w p.val = cost w q.val ∧ p.val.length < q.val.length)) →
      cost w₁ p.val < cost w₁ q.val)
    {s t : V} {p : DWalk s t} (hpath : p.IsPath) (hp : Shortest G w₁ p) :
    MinHopShortest G w p := by
  have hshort : Shortest G w p := by
    refine ⟨hp.1, ?_⟩
    intro q hq
    by_contra hle
    have hlt : cost w q.bypass < cost w p :=
      (cost_bypass_le w q).trans_lt (lt_of_not_ge hle)
    exact (hcompare s t ⟨q.bypass, q.bypass_isPath⟩ ⟨p, hpath⟩ (Or.inl hlt)).not_ge
      (hp.2 q.bypass (allowed_bypass hq))
  refine ⟨hshort, ?_⟩
  intro q hq
  by_contra hle
  have hcost : cost w q.bypass = cost w p := le_antisymm
    ((cost_bypass_le w q).trans (hq.2 p hshort.1))
    (hshort.2 q.bypass (allowed_bypass hq.1))
  have hlen : q.bypass.length < p.length :=
    q.length_bypass_le_length.trans_lt (Nat.lt_of_not_ge hle)
  exact (hcompare s t ⟨q.bypass, q.bypass_isPath⟩ ⟨p, hpath⟩
    (Or.inr ⟨hcost, hlen⟩)).not_ge (hp.2 q.bypass (allowed_bypass hq.1))

noncomputable def codeWeight (u v : V) : ℝ≥0 := edgeCode s(u,v)

theorem cost_codeWeight {s t : V} (p : DWalk s t) :
    cost codeWeight p = ((p.edges.map edgeCode).sum : ℕ) := by
  induction p with
  | nil => simp [cost, codeWeight]
  | cons h p ih => simpa [cost_cons, codeWeight, Nat.cast_add] using ih

/-- Lexicographic optimality yields a strict weight/code comparison against
every different simple path with the same endpoints. -/
theorem optimal_strict_comparison {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p q : DWalk s t} (hp : Optimal G w p)
    (hq : Allowed G q) (hqpath : q.IsPath) (hne : q ≠ p) :
    cost w p < cost w q ∨
      (cost w p = cost w q ∧ cost codeWeight p < cost codeWeight q) := by
  have hlt : score w p < score w q := lt_of_le_of_ne (hp.2.2 q hq)
    (fun he => hne (score_injective_on_paths w p q hp.2.1 hqpath he).symm)
  change toLex (ofLex (score w p)) < toLex (ofLex (score w q)) at hlt
  rw [Prod.Lex.toLex_lt_toLex] at hlt
  simp only [score_primary, score_secondary] at hlt
  rcases hlt with hlt | ⟨he, hlt⟩
  · exact Or.inl hlt
  · refine Or.inr ⟨he, ?_⟩
    rw [cost_codeWeight, cost_codeWeight]
    exact_mod_cast hlt

/-- Lemma 4.2: the same positive real reweighting works for every reachable
pair. Uniqueness quantifies over all walks; the selected walk minimizes the
original cost, then the original hop count. The directed edge relation is
unchanged, and no uniqueness or shortest-path oracle is assumed. -/
theorem exists_unique_minhop_reweighting (G : V → V → Prop)
    (w : V → V → ℝ≥0) :
    ∃ w' : V → V → ℝ≥0,
      (∀ u v, 0 < w' u v) ∧
      ∀ s t, Reachable G s t → ∃ p : DWalk s t,
        UniqueShortest G w' p ∧ MinHopShortest G w p := by
  obtain ⟨ε, hε, hfirst⟩ := exists_path_perturbation w (fun _ _ => 1)
  let w₁ : V → V → ℝ≥0 := fun u v => w u v + ε * 1
  have hfirst' : ∀ s t (p q : (⊤ : SimpleGraph V).Path s t),
      (cost w p.val < cost w q.val ∨
        (cost w p.val = cost w q.val ∧ p.val.length < q.val.length)) →
      cost w₁ p.val < cost w₁ q.val := by
    intro s t p q hpq
    apply hfirst ε hε le_rfl s t p q
    simpa only [cost_unit, Nat.cast_lt] using hpq
  obtain ⟨δ, hδ, hsecond⟩ := exists_path_perturbation w₁ codeWeight
  let w' : V → V → ℝ≥0 := fun u v => w₁ u v + δ * codeWeight u v
  have hpos : ∀ u v, 0 < w' u v := by
    intro u v
    dsimp [w', w₁]
    positivity
  refine ⟨w', hpos, ?_⟩
  intro s t hreach
  obtain ⟨p, hp⟩ := exists_optimal G w₁ s t hreach
  refine ⟨p, ?_, minHopShortest_of_comparison hfirst' hp.2.1 (optimal_shortest hp)⟩
  apply uniqueShortest_of_path_comparison (fun u v _ => hpos u v) hp.1
  intro q hq hqpath hne
  exact hsecond δ hδ le_rfl s t ⟨p, hp.2.1⟩ ⟨q, hqpath⟩
    (optimal_strict_comparison hp hq hqpath hne)

end GreedyShortcuts.WeightedPaths
