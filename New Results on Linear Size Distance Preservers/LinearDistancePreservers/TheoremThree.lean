import LinearDistancePreservers.ModularObstacleMetric

/-! Explicit finite weighted lower-bound witnesses for Section 4.2.
The graph, positive symmetric weights, terminals, and the universal
preserver quantifier are all concrete. The unrestricted asymptotic
rounding/padding statement of Theorem 3 is a separate parameter question. -/
namespace LinearDistancePreservers.ModularObstacle
open SimpleGraph Finset ObstacleProduct WeightedDigraph
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {n k x σ : ℕ} [NeZero n] [NeZero σ]

def boundary : ZMod σ ⊕ ZMod σ → ProductVertex n k σ
  | .inl a => .inl a
  | .inr c => .inr (.inr c)

theorem boundary_injective : Function.Injective (boundary (n := n) (k := k) (σ := σ)) := by
  rintro (a | c) (a' | c') h <;> simp_all [boundary]

noncomputable def terminals (n k σ : ℕ) [NeZero n] [NeZero σ] : Finset (ProductVertex n k σ) :=
  univ.image boundary

theorem terminals_card : (terminals n k σ).card = 2*σ := by
  rw [terminals,card_image_of_injective _ boundary_injective,card_univ]
  simp [ZMod.card,two_mul]

theorem left_mem_terminals (a : ZMod σ) : (.inl a : ProductVertex n k σ) ∈ terminals n k σ :=
  mem_image.mpr ⟨.inl a,mem_univ _,rfl⟩

theorem right_mem_terminals (c : ZMod σ) : (.inr (.inr c) : ProductVertex n k σ) ∈ terminals n k σ :=
  mem_image.mpr ⟨.inr c,mem_univ _,rfl⟩

/-- Every preserving subgraph equals the entire product. Attainment of
weighted distances and unique shortest paths are proved, not hypotheses. -/
theorem preserver_eq (hx : x ≤ n) (hsize : n*x ≤ σ)
    (hn : (k+1)*x ≤ n) (houter : 3*(n*x) ≤ σ)
    (H : SimpleGraph (ProductVertex n k σ)) (hsub : H ≤ graph (data hx hsize))
    (hpres : ∀ s ∈ terminals n k σ, ∀ t ∈ terminals n k σ,
      distance H.Adj (fun u v => (weight n k x σ u v : ℝ≥0∞)) s t =
        distance (graph (data hx hsize)).Adj (fun u v => (weight n k x σ u v : ℝ≥0∞)) s t) :
    H = graph (data hx hsize) := by
  classical
  apply WeightedNativeForcing.eq_of_covers (weight n k x σ)
    (fun p : ZMod σ × (ZMod n × Fin x) => .inl ((data hx hsize).left p.1 p.2))
    (fun p : ZMod σ × (ZMod n × Fin x) => .inr (.inr ((data hx hsize).right p.1 p.2)))
    (fun p => fullWalk (data hx hsize) p.1 p.2)
  · intro p q
    exact (full_optimal hx hsize hn houter p.1 p.2 q).1
  · intro p q
    exact (full_optimal hx hsize hn houter p.1 p.2 q).2
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      obtain ⟨i,hi⟩ := he
      have hie : edge (data hx hsize) i = s(u,v) := Sym2.mk_eq_mk_iff.mpr hi
      obtain ⟨b,j,hbj⟩ := indexed_edge_covered (data hx hsize) i
      exact ⟨(b,j),hie ▸ hbj⟩
  · exact hsub
  · intro p
    exact hpres _ (left_mem_terminals _) _ (right_mem_terminals _)

/-- Exact finite lower bound, for all legal modular parameters. -/
theorem preserver_edge_count (hx : x ≤ n) (hsize : n*x ≤ σ)
    (hn : (k+1)*x ≤ n) (houter : 3*(n*x) ≤ σ)
    (H : SimpleGraph (ProductVertex n k σ)) (hsub : H ≤ graph (data hx hsize))
    (hpres : ∀ s ∈ terminals n k σ, ∀ t ∈ terminals n k σ,
      distance H.Adj (fun u v => (weight n k x σ u v : ℝ≥0∞)) s t =
        distance (graph (data hx hsize)).Adj (fun u v => (weight n k x σ u v : ℝ≥0∞)) s t) :
    H.edgeFinset.card = σ*n*x*(k+2) := by
  rw [preserver_eq hx hsize hn houter H hsub hpres]
  exact edge_count hx hsize

end LinearDistancePreservers.ModularObstacle

namespace LinearDistancePreservers.TheoremThree
open SimpleGraph Finset ObstacleProduct WeightedDigraph ModularObstacle
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Parameter arithmetic for an unbounded two-parameter family. Cubing
the lower bound avoids any convention about real fractional powers. -/
theorem family_arithmetic (k x : ℕ) (hx : 0 < x) :
    let n := (k+1)*x
    let σ := 3*(k+1)*x^2
    (2*σ)^3 * (2*σ+σ*(k+1)*n)^2 ≤ 648*(σ*n*x*(k+2))^3 := by
  dsimp only
  have hunit : 0 < (k+1)^2*x := by positivity
  have hsmall : 6*(k+1)*x^2 ≤ 6*(k+1)^3*x^3 := by
    calc
      _ ≤ (6*(k+1)*x^2)*((k+1)^2*x) := Nat.le_mul_of_pos_right _ hunit
      _ = _ := by ring
  have hN : 2*(3*(k+1)*x^2)+(3*(k+1)*x^2)*(k+1)*((k+1)*x) ≤
      9*(k+1)^3*x^3 := by nlinarith only [hsmall]
  have hE : 3*(k+1)^3*x^4 ≤ (3*(k+1)*x^2)*((k+1)*x)*x*(k+2) := by
    nlinarith [Nat.zero_le (3*(k+1)^2*x^4)]
  calc
    _ ≤ (2*(3*(k+1)*x^2))^3 * (9*(k+1)^3*x^3)^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN 2)
    _ = 648*(3*(k+1)^3*x^4)^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hE 3)

/-- Actual weighted graphs achieve the Theorem 3 growth rate on this
explicit family: T^3 N^2 ≤ 648 E^3, hence E ≥ 648^(-1/3) T N^(2/3).
The statement quantifies over every subset distance preserver. -/
theorem family_lower_bound (k x : ℕ) (hx : 0 < x) :
    let n := (k+1)*x
    let σ := 3*(k+1)*x^2
    letI : NeZero n := ⟨Nat.ne_of_gt (by dsimp [n]; positivity)⟩
    letI : NeZero σ := ⟨Nat.ne_of_gt (by dsimp [σ]; positivity)⟩
    ∃ (G : SimpleGraph (ProductVertex n k σ))
      (w : ProductVertex n k σ → ProductVertex n k σ → ℝ≥0)
      (S : Finset (ProductVertex n k σ)),
      S.card = 2*σ ∧
      Fintype.card (ProductVertex n k σ) = 2*σ+σ*(k+1)*n ∧
      (∀ u v, G.Adj u v → 0 < w u v ∧ w u v = w v u) ∧
      ∀ H : SimpleGraph (ProductVertex n k σ), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S,
          distance H.Adj (fun u v => (w u v : ℝ≥0∞)) s t =
            distance G.Adj (fun u v => (w u v : ℝ≥0∞)) s t) →
        H.edgeFinset.card = σ*n*x*(k+2) ∧
        S.card^3 * (Fintype.card (ProductVertex n k σ))^2 ≤ 648*H.edgeFinset.card^3 := by
  dsimp only
  let n := (k+1)*x
  let σ := 3*(k+1)*x^2
  have hnpos : 0 < n := by dsimp [n]; positivity
  have hσpos : 0 < σ := by dsimp [σ]; positivity
  letI : NeZero n := ⟨by omega⟩
  letI : NeZero σ := ⟨by omega⟩
  have hn : (k+1)*x ≤ n := le_rfl
  have hxn : x ≤ n := Nat.le_mul_of_pos_left x (by omega)
  have houter : 3*(n*x) ≤ σ := by dsimp [n,σ]; nlinarith
  have hsize : n*x ≤ σ := by omega
  refine ⟨graph (data (k := k) hxn hsize), weight n k x σ, terminals n k σ,
    terminals_card, ModularObstacle.vertex_count, ?_, ?_⟩
  · intro u v huv
    exact ⟨weight_pos hxn hsize huv, weight_symm hxn hsize u v huv⟩
  · intro H hH hp
    have hc := ModularObstacle.preserver_edge_count hxn hsize hn houter H hH hp
    refine ⟨hc,?_⟩
    rw [terminals_card,ModularObstacle.vertex_count,hc]
    exact family_arithmetic k x hx

end LinearDistancePreservers.TheoremThree
