import LinearDistancePreservers.TheoremThree
import LinearDistancePreservers.LowerBoundParameters
import LinearDistancePreservers.PathLowerBound

/-! Exact-size weighted subset-preserver lower bounds. The graph has
exactly N vertices and the terminal set exactly T elements. Floors,
small parameters, isolated vertices, and extra terminals are handled. -/
namespace LinearDistancePreservers.TheoremThree
open SimpleGraph Finset ObstacleProduct WeightedDigraph ModularObstacle PreserverPadding
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

/-- Uniform finite Theorem 3 witness throughout 2≤T≤N and T³≤N².
The absolute constant is deliberately loose to include all integer sizes. -/
theorem exact_size_rigid {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) (hrange : T^3 ≤ N^2) :
    ∃ (G : SimpleGraph (Fin N)) (w : Fin N → Fin N → ℝ≥0) (S : Finset (Fin N)),
      S.card = T ∧ Rigid G w S ∧ T^3*N^2 ≤ 8192^3*G.edgeFinset.card^3 ∧
      ∀ u v, G.Adj u v → 0 < w u v ∧ w u v = w v u := by
  obtain ⟨q,hq,hqN,hNq,hTq⟩ := LowerBoundParameters.cube_scale hT hTN hrange
  by_cases hsmall : T ≤ 192*q
  · obtain ⟨G,w,S,hS,hr,hE,hw⟩ := PathLowerBound.exists_path_witness hT hTN
    refine ⟨G,w,S,hS,hr,?_,hw⟩
    rw [hE]
    exact LowerBoundParameters.path_rate (by omega) hqN hsmall
  · obtain ⟨σ,k,x,hσ,hx,hxq,hinner,houter,hterm,hvert,hedge⟩ :=
      LowerBoundParameters.product_parameters hq (by omega) hTq
    letI : NeZero q := ⟨by omega⟩
    letI : NeZero σ := ⟨by omega⟩
    have hsize : q*x ≤ σ := by omega
    have hrigid : Rigid (graph (data (k := k) hxq hsize)) (weight q k x σ) (terminals q k σ) :=
      fun H hH hp => preserver_eq hxq hsize hinner houter H hH hp
    obtain ⟨G,w,S,hS,hr,hE,hw⟩ := PreserverPadding.pad
      (graph (data (k := k) hxq hsize)) (weight q k x σ) (terminals q k σ) hrigid
      (fun u v huv => ⟨weight_pos hxq hsize huv,weight_symm hxq hsize u v huv⟩)
      (N := N) (T := T)
      (by rw [ModularObstacle.vertex_count]; exact hvert.trans hqN)
      (by rw [terminals_card]; exact hterm) hTN
    refine ⟨G,w,S,hS,hr,?_,hw⟩
    rw [hE,edge_count hxq hsize]
    exact LowerBoundParameters.product_rate hNq hedge

/-- Exact-size Theorem 3, with the original all-terminal-pairs distance
condition and quantification over every preserving subgraph. -/
theorem exact_size_lower_bound {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) (hrange : T^3 ≤ N^2) :
    ∃ (G : SimpleGraph (Fin N)) (w : Fin N → Fin N → ℝ≥0) (S : Finset (Fin N)),
      S.card = T ∧ (∀ u v, G.Adj u v → 0 < w u v ∧ w u v = w v u) ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S,
          distance H.Adj (fun u v => (w u v : ℝ≥0∞)) s t =
            distance G.Adj (fun u v => (w u v : ℝ≥0∞)) s t) →
        T^3*N^2 ≤ 8192^3*H.edgeFinset.card^3 := by
  obtain ⟨G,w,S,hS,hr,hbound,hw⟩ := exact_size_rigid hT hTN hrange
  refine ⟨G,w,S,hS,hw,?_⟩
  intro H hH hp
  rw [hr H hH hp]
  exact hbound

/-- Arbitrary fixed constants in T=O(N^(2/3)) are permitted. The resulting
lower-bound constant depends only on the range constant C. -/
theorem bounded_range_rigid {N T C : ℕ} (hC : 0 < C)
    (hT : 2 ≤ T) (hTN : T ≤ N) (hrange : T^3 ≤ C^3*N^2) :
    ∃ (G : SimpleGraph (Fin N)) (w : Fin N → Fin N → ℝ≥0) (S : Finset (Fin N)),
      S.card = T ∧ Rigid G w S ∧ T^3*N^2 ≤ (32768*C)^3*G.edgeFinset.card^3 ∧
      ∀ u v, G.Adj u v → 0 < w u v ∧ w u v = w v u := by
  obtain ⟨q,hq,hqN,hNq,hTq⟩ := LowerBoundParameters.cube_scale_mul hT hTN hrange
  by_cases hq2 : 2 ≤ q
  · let U := min T (q^2)
    have hqpow : 2 ≤ q^2 := by nlinarith only [hq2]
    have hU : 2 ≤ U := le_min hT hqpow
    have hUT : U ≤ T := min_le_left _ _
    have hUq : U ≤ q^2 := min_le_right _ _
    have hUN : U ≤ N := hUT.trans hTN
    have hUc : U^3 ≤ N^2 := by
      calc
        _ ≤ (q^2)^3 := Nat.pow_le_pow_left hUq 3
        _ = (q^3)^2 := by ring
        _ ≤ _ := Nat.pow_le_pow_left hqN 2
    have hTU : T ≤ (4*C)*U := by
      rcases le_total T (q^2) with h | h
      · rw [show U = T from min_eq_left h]
        exact Nat.le_mul_of_pos_left _ (by omega)
      · rw [show U = q^2 from min_eq_right h]
        exact hTq
    obtain ⟨G,w,S,hS,hr,hbound,hw⟩ := exact_size_rigid hU hUN hUc
    obtain ⟨S',hSS',_,hcard⟩ := exists_subsuperset_card_eq (subset_univ S)
      (by omega : S.card ≤ T) (by simpa using hTN)
    refine ⟨G,w,S',hcard,rigid_mono_terminals hr hSS',?_,hw⟩
    calc
      _ ≤ ((4*C)*U)^3*N^2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hTU 3)
      _ = (4*C)^3*(U^3*N^2) := by ring
      _ ≤ (4*C)^3*(8192^3*G.edgeFinset.card^3) := Nat.mul_le_mul_left _ hbound
      _ = _ := by ring
  · have hq1 : q = 1 := by omega
    have hsmall : T ≤ 192*q := by rw [hq1] at hNq ⊢; norm_num at hNq ⊢; omega
    obtain ⟨G,w,S,hS,hr,hE,hw⟩ := PathLowerBound.exists_path_witness hT hTN
    refine ⟨G,w,S,hS,hr,?_,hw⟩
    rw [hE]
    exact (LowerBoundParameters.path_rate (by omega) hqN hsmall).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 3))

/-- Finite quantified form of the full weighted lower bound (Theorem 3).
For each fixed C≥1 and all 2≤T≤N with T³≤C³N², there is an actual
undirected graph with finite positive symmetric edge weights such that
every S×S distance preserver requires E with T³N²≤(32768C)³E³.
The natural restriction T≥2 excludes the vacuous zero/one-terminal cases. -/
theorem bounded_range_lower_bound {N T C : ℕ} (hC : 0 < C)
    (hT : 2 ≤ T) (hTN : T ≤ N) (hrange : T^3 ≤ C^3*N^2) :
    ∃ (G : SimpleGraph (Fin N)) (w : Fin N → Fin N → ℝ≥0) (S : Finset (Fin N)),
      S.card = T ∧ (∀ u v, G.Adj u v → 0 < w u v ∧ w u v = w v u) ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S,
          distance H.Adj (fun u v => (w u v : ℝ≥0∞)) s t =
            distance G.Adj (fun u v => (w u v : ℝ≥0∞)) s t) →
        T^3*N^2 ≤ (32768*C)^3*H.edgeFinset.card^3 := by
  obtain ⟨G,w,S,hS,hr,hbound,hw⟩ := bounded_range_rigid hC hT hTN hrange
  refine ⟨G,w,S,hS,hw,?_⟩
  intro H hH hp
  rw [hr H hH hp]
  exact hbound

end LinearDistancePreservers.TheoremThree
