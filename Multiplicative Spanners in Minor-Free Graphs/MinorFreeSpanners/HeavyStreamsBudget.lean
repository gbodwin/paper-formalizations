import MinorFreeSpanners.DyadicStreamCover
import MinorFreeSpanners.FiniteCoverBudget

/-! Cover all heavy edges by actual integer-start streams. Overlapping band
boundaries are harmless because weights are nonnegative. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem heavy_edges_stream_budget {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h ell N : ℕ) (ht : 4096≤t) (hr : 1≤r) (hh : 0<h)
    (hell : (t:ℝ)≤(2:ℝ)^ell)
    (hT : T≤G) (hTree : T.IsTree) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hfree : CliqueMinorFree G h) (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e) (hcut : ∀ e∈G.edgeSet,w e<(t:ℝ)^(N+1)) :
    (∑ e∈G.edgeFinset.filter (fun e => (t:ℝ)≤w e),w e)≤
      42*(ell:ℝ)*canonicalPhaseCredit t r h*(T.edgeFinset.card:ℝ) := by
  classical
  let E := G.edgeFinset.filter (fun e => (t:ℝ)≤w e)
  let B := fun j k => weightBand G w ((t:ℝ)^(k+1)*((2^j:ℕ):ℝ))
    (2*((t:ℝ)^(k+1)*((2^j:ℕ):ℝ)))
  have htR : (1:ℝ)<t := by exact_mod_cast (show 1<t by omega)
  have hB (j k : ℕ) : B j k≤G := fun _ _ hxy => hxy.1
  have hcover : ∀ e∈E,∃ p∈(range ell).product (range N),e∈(B p.1 p.2).edgeFinset := by
    intro e he
    have heG : e∈G.edgeSet := by simpa using (Finset.mem_filter.mp he).1
    have helow : (t:ℝ)≤w e := (Finset.mem_filter.mp he).2
    obtain ⟨j,hj,k,hk,hlo,hhi⟩ := exists_dyadic_stream_band (t:ℝ) (w e) ell N htR helow (hcut e heG) hell
    refine ⟨(j,k),Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj,Finset.mem_range.mpr hk⟩,?_⟩
    have hm : e∈(B j k).edgeSet := by
      induction e using Sym2.inductionOn with
      | _ x y =>
        refine ⟨heG,?_,?_⟩
        · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hlo
        · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hhi
    simpa using hm
  have hpaid := finite_cover_budget E ((range ell).product (range N))
    (fun p => (B p.1 p.2).edgeFinset) w
    (fun e he => hw e (by simpa using (Finset.mem_filter.mp he).1))
    (fun p _ e he => hw e (edgeSet_mono (hB p.1 p.2) (by simpa using he))) hcover
  have hsum : (∑ p∈(range ell).product (range N),∑ e∈(B p.1 p.2).edgeFinset,w e)=
      ∑ j∈range ell,∑ k∈range N,∑ e∈(B j k).edgeFinset,w e := Finset.sum_product _ _ _
  rw [hsum] at hpaid
  have hstreams : (∑ j∈range ell,∑ k∈range N,∑ e∈(B j k).edgeFinset,w e)≤
      ∑ _j∈range ell,42*canonicalPhaseCredit t r h*(T.edgeFinset.card:ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact finite_geometric_stream_bound t r h (2^j) ht (by positivity) hr hh
      hT hTree hunit hfree hG hw N
  have out := hpaid.trans hstreams
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at out
  nlinarith only [out]

end MinorFreeSpanners
