import MinorFreeSpanners.RadiusTwoClusterWalks
import MinorFreeSpanners.GirthMinorFreeUpper

/-! Conserved pooled credits for the actual high-degree groups. The proof
uses the total number of genuine induced edges and disjoint vertex credits;
it does not infer a pointwise degree bound from an average degree bound. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Half of each actual group's old credits can be kept as the new reserve;
the other half pays all marked quotient edges. The graph density premise
is instantiated from the proved high-girth minor-free bound below. -/
theorem high_degree_credit_accounting {I : Type*} [Fintype I]
    (H : SimpleGraph I) (centers : Finset I) (groups : I → Finset I)
    (hdis : ∀ c∈centers, ∀ d∈centers, c≠d → Disjoint (groups c) (groups d))
    (q : ℕ) (hsize : ∀ c∈centers, q+1 ≤ (groups c).card)
    (credit : I → ℝ) (a L b R : ℝ) (hL : 0≤L) (hb : 0≤b)
    (hc : ∀ i∈centers.biUnion groups, b ≤ credit i)
    (hreserve : 2*R ≤ (q+1:ℕ)*b) (hpay : 2*a*L ≤ b)
    (hedges : ((H.induce (centers.biUnion groups : Set I)).edgeFinset.card : ℝ) ≤
      a*(centers.biUnion groups).card) :
    (∀ c∈centers, R ≤ (∑ i∈groups c, credit i)/2) ∧
    ((H.induce (centers.biUnion groups : Set I)).edgeFinset.card : ℝ)*L +
      (∑ c∈centers, (∑ i∈groups c, credit i)/2) ≤
      ∑ i∈centers.biUnion groups, credit i := by
  classical
  have hpart (c : I) (hcC : c∈centers) :
      (groups c).card*b ≤ ∑ i∈groups c, credit i := by
    calc
      _ = ∑ _i∈groups c, b := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => hc i (Finset.mem_biUnion.mpr ⟨c,hcC,hi⟩)
  have hall : (centers.biUnion groups).card*b ≤ ∑ i∈centers.biUnion groups, credit i := by
    calc
      _ = ∑ _i∈centers.biUnion groups, b := by simp
      _ ≤ _ := Finset.sum_le_sum hc
  have hsum : (∑ c∈centers, ∑ i∈groups c, credit i) =
      ∑ i∈centers.biUnion groups, credit i :=
    (Finset.sum_biUnion (fun c hc d hd hcd => hdis c hc d hd hcd)).symm
  constructor
  · intro c hcC
    have hs : ((q+1:ℕ):ℝ) ≤ (groups c).card := by exact_mod_cast hsize c hcC
    have hm := mul_le_mul_of_nonneg_right hs hb
    have hp := hpart c hcC
    linarith
  · rw [← Finset.sum_div,hsum]
    have he := mul_le_mul_of_nonneg_right hedges hL
    have hp := mul_le_mul_of_nonneg_left hpay (Nat.cast_nonneg (centers.biUnion groups).card :
      (0:ℝ) ≤ (centers.biUnion groups).card)
    nlinarith only [he,hp,hall]

/-- The only edge-density input above is supplied by the actual induced
minor-free, high-girth quotient, including the empty marked set. -/
theorem marked_girth_minor_free_edge_bound {I : Type*} [Fintype I]
    (H : SimpleGraph I) (S : Finset I) (r h : ℕ) (hr : 1≤r) (hh : 0<h)
    (hfree : CliqueMinorFree H h) (hg : GirthAbove H (2*r)) :
    ((H.induce (S:Set I)).edgeFinset.card : ℝ) ≤
      (2*fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ)))*S.card := by
  classical
  let f : H.induce (S:Set I) →g H := {toFun := Subtype.val,map_rel' := fun a => a}
  have hF := hfree.of_minor (MinorModel.ofEmbedding (H.induce (S:Set I)) H ⟨Subtype.val,Subtype.val_injective⟩ (fun _ _ h => h))
  have hG := hg.of_embedding f Subtype.val_injective
  have hb := girth_minor_free_edge_bound (H.induce (S:Set I)) r h hr hh hF hG
  simp only [← Set.toFinset_card,Finset.toFinset_coe] at hb
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hb ⊢
  exact hb

end MinorFreeSpanners
