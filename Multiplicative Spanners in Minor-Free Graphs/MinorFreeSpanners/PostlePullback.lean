import MinorFreeSpanners.BoundedMinor
import MinorFreeSpanners.PostleMates

/-! Corollary 3.3: pull the actual small dense subgraph back through a
bounded genuine branch-set model. No density increment is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem postle_bounded_minor_dense_or_unmated
    (F : SimpleGraph I) (G : SimpleGraph V) (M : MinorModel F G) (m : ℕ)
    (hM : M.IsBounded m) (K d ε₁ ε₂ : ℝ) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1) (hε₂0 : 0 ≤ ε₂) :
    (∃ T : Finset V, (T.card:ℝ) ≤ 3*m*K*d ∧
      ε₁*ε₂*d^2/2 ≤ ((G.induce (T:Set V)).edgeFinset.card:ℝ)) ∨
      Unmated F K ε₁ ε₂ d := by
  classical
  rcases postle_small_dense_or_unmated F K d ε₁ ε₂ hK hd hε₁0 hε₁1 hε₂0 with ⟨S,hS,hE⟩ | hu
  · obtain ⟨T,hT,hTE⟩ := MinorModel.IsBounded.exists_host_subgraph
      (M.induceTarget (S:Set I)) (MinorModel.IsBounded.induceTarget M hM (S:Set I))
    have hcard : Fintype.card (S:Set I) = S.card := Fintype.card_coe S
    rw [hcard] at hT
    have hTr : (T.card:ℝ) ≤ (m:ℝ)*(S.card:ℝ) := by exact_mod_cast hT
    have hTEr : ((F.induce (S:Set I)).edgeFinset.card:ℝ) ≤
        ((G.induce (T:Set V)).edgeFinset.card:ℝ) := by exact_mod_cast hTE
    refine Or.inl ⟨T,?_,hE.trans hTEr⟩
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  · exact Or.inr hu

end MinorFreeSpanners
