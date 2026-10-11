import MinorFreeSpanners.MinorSingletonDeletion
import MinorFreeSpanners.GeneralLargeVertexBudget
import MinorFreeSpanners.ResidualMinorDensityAlgebra

/-! The actual half-covered canonical star quotient, after deleting its
small residual singleton branches, has density at least (k-7)d. The edge
and vertex estimates refer to that one concrete bounded host minor. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No output graph or density certificate is supplied. The retained minor
is constructed by deleting exactly the original-small residual singletons. -/
theorem clean_coverage_retained_minor_density (G : SimpleGraph V) (k : ℕ)
    (C : Finset V) (L : V → Finset V) (K eps1 eps2 d : ℝ)
    (hk : 8 ≤ k) (hn : 0 < Fintype.card V) (hd : 0 < d)
    (he1 : 0 ≤ eps1) (hK : 4*(k:ℝ)^2 ≤ K)
    (hcoef : (3*eps1+4*eps2)*(k:ℝ) ≤ 5)
    (hF : SmallCleanStarForest G k (K*d) (4*(eps2*d)) C L)
    (hbranch : ∀ b∈C, (largeResidualStarVertices G C L (K*d) (3*eps1*d) b).card ≤ 1)
    (hhalf : 2*(smallResidualVertices G C L (K*d)).card ≤ Fintype.card V)
    (hE : d*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ))
    (hglobal : ∀ W : Finset V, ((G.induce (W:Set V)).edgeFinset.card:ℝ) ≤ d*(W.card:ℝ))
    (hupper : (G.edgeFinset.card:ℝ) ≤ d*(Fintype.card V:ℝ)) :
    let U := smallResidualVertices G C L (K*d)
    let R := Finset.univ\residualDeletionLabels C L U (Finset.filter_subset _ _)
    ∃ M : MinorModel ((fullStarContraction G C L).induce (R:Set (StarContractionVertex C L))) G,
      M.IsBounded k ∧ 0<R.card ∧
      ((k:ℝ)-7)*d*(R.card:ℝ) ≤
        (((fullStarContraction G C L).induce (R:Set (StarContractionVertex C L))).edgeFinset.card:ℝ) := by
  classical
  let U := smallResidualVertices G C L (K*d)
  let B := originalLargeVertices G (K*d)
  let H := exceptionalCoveredVertices G C L (K*d) (3*eps1*d)
  let Y := residualTargetVertices G C L (K*d) (3*eps1*d)
  let F := C.biUnion (fun b => insert b (L b))
  let Z := F\H
  have hU : U ⊆ starResidual C L := Finset.filter_subset _ _
  let R := Finset.univ\residualDeletionLabels C L U hU
  let r := (starResidual C L\U).card
  have hrB : r ≤ B.card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxR,hxU⟩ := Finset.mem_sdiff.mp hx
    have hxd : K*d < (G.degree x:ℝ) := lt_of_not_ge (fun hh => hxU (Finset.mem_filter.mpr ⟨hxR,hh⟩))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxd⟩
  have hres : r+U.card=(starResidual C L).card := Finset.card_sdiff_add_card_eq_card hU
  have hcov : (starResidual C L).card+k*C.card=Fintype.card V := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ F)
    simpa only [F,starResidual,Finset.card_univ,hF.1.covered_card] using h
  have hN : k*C.card+r+U.card=Fintype.card V := by omega
  have hR := retained_star_quotient_card G k C L hF.1 (by omega) U hU
  have hprod : (k-1)*C.card+C.card=k*C.card := by
    calc
      _ = ((k-1)+1)*C.card := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega)]
  have hRc : R.card=C.card+r := by dsimp [R];omega
  have hRpos : 0<R.card := by
    by_contra hh
    have hz : R.card=0 := by omega
    have hc0 : C.card=0 := by omega
    have hr0 : r=0 := by omega
    simp only [hc0,hr0,mul_zero,zero_add,add_zero] at hN
    change 2*U.card ≤ Fintype.card V at hhalf
    omega
  have hB := originalLargeVertices_scaled_card G k K d hd hK hupper
  have hlarge : k^2*B.card ≤ k*C.card+r := by
    change 2*k^2*B.card ≤ Fintype.card V at hB
    change 2*U.card ≤ Fintype.card V at hhalf
    nlinarith only [hB,hhalf,hN]
  have hH : H.card ≤ C.card := exceptionalCoveredVertices_card_le G C L (K*d) (3*eps1*d) hbranch
  have hY : Y.card ≤ B.card+C.card := (Finset.card_union_le B H).trans (Nat.add_le_add_left hH _)
  have hinc := incidentEdges_real_bound G U Y Z d (3*eps1*d*F.card) hd.le
    (residual_three_part_cover G C L (K*d) (3*eps1*d)) hglobal
    (lowCovered_crossing_budget G C L (K*d) (3*eps1*d) (by positivity))
  have hYreal : (Y.card:ℝ) ≤ (B.card:ℝ)+C.card := by exact_mod_cast hY
  have hYscale := mul_le_mul_of_nonneg_left hYreal hd.le
  have hFcard : F.card=k*C.card := hF.1.covered_card
  have hinc' : ((incidentEdges G U).card:ℝ) ≤
      d*((U.card:ℝ)+B.card+C.card)+3*eps1*d*((k:ℝ)*C.card) := by
    rw [hFcard] at hinc
    push_cast at hinc
    nlinarith only [hinc,hYscale]
  obtain ⟨M,hM,hdel⟩ := retained_star_quotient_budget G k C L hF.1 (by omega) U hU
  have hdelR : ((fullStarContraction G C L).edgeFinset.card:ℝ) ≤
      (((fullStarContraction G C L).induce (R:Set (StarContractionVertex C L))).edgeFinset.card:ℝ)+
        (incidentEdges G U).card := by exact_mod_cast hdel
  have hclean := hF.2.2
  push_cast at hclean
  have hnR : (k:ℝ)*C.card+r+U.card=(Fintype.card V:ℝ) := by exact_mod_cast hN
  have hdN := congrArg (fun t : ℝ => d*t) hnR
  have he : d*((k:ℝ)*C.card+r-B.card-C.card-(3*eps1+4*eps2)*k*C.card) ≤
      (((fullStarContraction G C L).induce (R:Set (StarContractionVertex C L))).edgeFinset.card:ℝ) := by
    nlinarith only [hE,hclean,hdelR,hinc',hdN]
  have hkR : (8:ℝ) ≤ k := by exact_mod_cast hk
  have hbigR : (k:ℝ)^2*B.card ≤ (k:ℝ)*C.card+r := by exact_mod_cast hlarge
  have hrR : (r:ℝ) ≤ B.card := by exact_mod_cast hrB
  have final := retained_minor_density_algebra (k:ℝ) d (3*eps1+4*eps2)
    C.card B.card r _ hkR hd.le (Nat.cast_nonneg _) (Nat.cast_nonneg _) hrR hbigR hcoef he
  refine ⟨M,hM,hRpos,?_⟩
  change ((k:ℝ)-7)*d*(R.card:ℝ) ≤
    (((fullStarContraction G C L).induce (R:Set (StarContractionVertex C L))).edgeFinset.card:ℝ)
  rw [hRc,Nat.cast_add]
  exact final

end MinorFreeSpanners
