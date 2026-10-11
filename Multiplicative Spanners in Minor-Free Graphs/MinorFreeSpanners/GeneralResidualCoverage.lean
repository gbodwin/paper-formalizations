import MinorFreeSpanners.GeneralResidualCounting

/-! Actual residual-to-covered incidence forces a small exceptional residual
set. The neighbor threshold retains its explicit factor of k; no stronger
source-paper crossing bound is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def originalLargeVertices (G : SimpleGraph V) (D : ℝ) : Finset V :=
  Finset.univ.filter (fun x => D < (G.degree x:ℝ))

noncomputable def residualTargetVertices (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (D threshold : ℝ) : Finset V :=
  originalLargeVertices G D ∪ exceptionalCoveredVertices G C L D threshold

noncomputable def weakResidualVertices (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (D threshold targetDegree : ℝ) : Finset V :=
  (smallResidualVertices G C L D).filter (fun x =>
    (((residualTargetVertices G C L D threshold).filter (G.Adj x)).card:ℝ) < targetDegree)

theorem residual_three_part_cover (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (D threshold : ℝ) (x : V) :
    x ∈ smallResidualVertices G C L D ∨ x ∈ residualTargetVertices G C L D threshold ∨
      x ∈ (C.biUnion (fun b => insert b (L b))) \ exceptionalCoveredVertices G C L D threshold := by
  by_cases hxF : x ∈ C.biUnion (fun b => insert b (L b))
  · by_cases hxH : x ∈ exceptionalCoveredVertices G C L D threshold
    · exact Or.inr (Or.inl (Finset.mem_union_right _ hxH))
    · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hxF,hxH⟩))
  · have hxR : x ∈ starResidual C L := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,hxF⟩
    by_cases hxD : (G.degree x:ℝ) ≤ D
    · exact Or.inl (Finset.mem_filter.mpr ⟨hxR,hxD⟩)
    · exact Or.inr (Or.inl (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ x,lt_of_not_ge hxD⟩)))

theorem degree_le_three_neighbor_counts (G : SimpleGraph V) (A B C : Finset V)
    (hcover : ∀ y, y ∈ A ∨ y ∈ B ∨ y ∈ C) (x : V) :
    G.degree x ≤ (A.filter (G.Adj x)).card+(B.filter (G.Adj x)).card+(C.filter (G.Adj x)).card := by
  classical
  have hs : G.neighborFinset x ⊆
      ((A.filter (G.Adj x)) ∪ (B.filter (G.Adj x))) ∪ (C.filter (G.Adj x)) := by
    intro y hy
    have he := (G.mem_neighborFinset x y).mp hy
    rcases hcover y with ha | hb | hc
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha,he⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb,he⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc,he⟩)
  calc
    _ = (G.neighborFinset x).card := rfl
    _ ≤ _ := Finset.card_le_card hs
    _ ≤ _ := (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)

omit [Fintype V] [DecidableEq V] in
theorem graphCrossingCount_mono_left (G : SimpleGraph V) {A A' B : Finset V}
    (h : A ⊆ A') : graphCrossingCount G A B ≤ graphCrossingCount G A' B :=
  Finset.sum_le_sum_of_subset h

/-- Few neighbors in the actual large-or-exceptional target force many edges
into ordinary covered vertices. Double-counting those real edges bounds the
number of such residual vertices. -/
theorem weakResidualVertices_card_bound (G : SimpleGraph V) (k : ℕ)
    (C : Finset V) (L : V → Finset V) (D eps1 d : ℝ)
    (hp : 0 < eps1*d)
    (hmin : ∀ x ∈ smallResidualVertices G C L D, d ≤ (G.degree x:ℝ))
    (hres : ∀ x ∈ smallResidualVertices G C L D,
      ((smallResidualNeighbors G C L D x).card:ℝ) ≤ 2*eps1*d) :
    k*(weakResidualVertices G C L D (3*eps1*d) (d-(2+3*(k:ℝ))*eps1*d)).card ≤
      (C.biUnion (fun b => insert b (L b))).card := by
  classical
  let U := smallResidualVertices G C L D
  let Y := residualTargetVertices G C L D (3*eps1*d)
  let Z := (C.biUnion (fun b => insert b (L b))) \ exceptionalCoveredVertices G C L D (3*eps1*d)
  let W := weakResidualVertices G C L D (3*eps1*d) (d-(2+3*(k:ℝ))*eps1*d)
  have hWU : W ⊆ U := fun _ hx => (Finset.mem_filter.mp hx).1
  have hpoint : ∀ x ∈ W, 3*(k:ℝ)*eps1*d ≤ ((Z.filter (G.Adj x)).card:ℝ) := by
    intro x hx
    have hm := hmin x (hWU hx)
    have hr := hres x (hWU hx)
    rw [smallResidualNeighbors_eq_filter] at hr
    have hy : ((Y.filter (G.Adj x)).card:ℝ) < d-(2+3*(k:ℝ))*eps1*d := (Finset.mem_filter.mp hx).2
    have hc : (G.degree x:ℝ) ≤ ((U.filter (G.Adj x)).card:ℝ)+
        ((Y.filter (G.Adj x)).card:ℝ)+((Z.filter (G.Adj x)).card:ℝ) := by
      exact_mod_cast degree_le_three_neighbor_counts G U Y Z
        (residual_three_part_cover G C L D (3*eps1*d)) x
    dsimp [U] at hc
    nlinarith
  have hlow : 3*(k:ℝ)*eps1*d*(W.card:ℝ) ≤ (graphCrossingCount G W Z:ℝ) := by
    unfold graphCrossingCount
    rw [Nat.cast_sum]
    calc
      _ = ∑ _x ∈ W, 3*(k:ℝ)*eps1*d := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hpoint
  have hmono : (graphCrossingCount G W Z:ℝ) ≤ (graphCrossingCount G U Z:ℝ) := by
    exact_mod_cast graphCrossingCount_mono_left G hWU
  have hhigh := lowCovered_crossing_budget G C L D (3*eps1*d) (by nlinarith)
  have hh : (3*eps1*d)*((k:ℝ)*(W.card:ℝ)) ≤
      (3*eps1*d)*((C.biUnion (fun b => insert b (L b))).card:ℝ) := by
    calc
      _ = 3*(k:ℝ)*eps1*d*(W.card:ℝ) := by ring
      _ ≤ _ := hlow.trans (hmono.trans hhigh)
  have hh' := le_of_mul_le_mul_left hh (show 0 < 3*eps1*d by nlinarith)
  have hhNat : k*W.card ≤ (C.biUnion (fun b => insert b (L b))).card := by
    exact_mod_cast hh'
  exact hhNat

end MinorFreeSpanners
