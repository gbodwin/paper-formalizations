import MinorFreeSpanners.ConstructedGeometricStream

/-! Trim only the trailing empty bands of a finite stream. No nonempty-band
premise remains in the resulting actual geometric-stream weight bound. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem finite_geometric_stream_bound {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h b : ℕ) (ht : 4096≤t) (hb : 0<b) (hr : 1≤r) (hh : 0<h)
    (hT : T≤G) (hTree : T.IsTree) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hfree : CliqueMinorFree G h) (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e) (n : ℕ) :
    (∑ k∈range n,∑ e∈(weightBand G w ((t:ℝ)^(k+1)*(b:ℝ))
      (2*((t:ℝ)^(k+1)*(b:ℝ)))).edgeFinset,w e)≤
        42*canonicalPhaseCredit t r h*(T.edgeFinset.card:ℝ) := by
  classical
  let B := fun k => weightBand G w ((t:ℝ)^(k+1)*(b:ℝ)) (2*((t:ℝ)^(k+1)*(b:ℝ)))
  let good := (range n).filter (fun k => (B k).edgeSet.Nonempty)
  have hempty (i : ℕ) (hn : ¬(B i).edgeSet.Nonempty) : (∑ e∈(B i).edgeFinset,w e)=0 := by
    apply Finset.sum_eq_zero
    intro e he
    exact False.elim (hn ⟨e,by simpa using he⟩)
  by_cases hgood : good.Nonempty
  · let k := good.max' hgood
    have hk : k∈good := Finset.max'_mem good hgood
    have hkn : k<n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hne : (B k).edgeSet.Nonempty := (Finset.mem_filter.mp hk).2
    have heq : (∑ i∈range (k+1),∑ e∈(B i).edgeFinset,w e)=
        ∑ i∈range n,∑ e∈(B i).edgeFinset,w e := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i hi hnot
      apply hempty
      intro hin
      have himem : i∈good := Finset.mem_filter.mpr ⟨hi,hin⟩
      have hle : i≤k := Finset.le_max' good i himem
      exact hnot (Finset.mem_range.mpr (by omega))
    have hp := constructed_geometric_stream_bound t r h b ht hb hr hh hT hTree hunit hfree hG hw k hne
    rw [←heq]
    exact hp
  · have hz : (∑ i∈range n,∑ e∈(B i).edgeFinset,w e)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply hempty
      intro hin
      exact hgood ⟨i,Finset.mem_filter.mpr ⟨hi,hin⟩⟩
    change (∑ i∈range n,∑ e∈(B i).edgeFinset,w e)≤_
    rw [hz]
    unfold canonicalPhaseCredit
    positivity

end MinorFreeSpanners
