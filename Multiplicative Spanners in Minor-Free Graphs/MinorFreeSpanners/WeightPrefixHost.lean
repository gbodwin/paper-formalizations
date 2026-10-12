import MinorFreeSpanners.ClusterGraph

/-! The actual phase can run inside a weight-prefix subgraph. Its returned
intrinsic walks then consist of edges below the following scale, rather than
merely lying in the full spanner. Girth and minor exclusion restrict exactly. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners

 def weightPrefix {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (M : ℝ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ w s(x,y)≤M
  symm := ⟨by rintro x y ⟨hxy,hw⟩; exact ⟨hxy.symm,by simpa only [Sym2.eq_swap] using hw⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

 theorem weightPrefix_le {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (M : ℝ) :
    weightPrefix G w M≤G := fun _ _ h => h.1

 theorem le_weightPrefix {V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {M : ℝ}
    (hA : A≤G) (hw : ∀ e∈A.edgeSet,w e≤M) : A≤weightPrefix G w M :=
  fun _ _ h => ⟨hA h,hw _ h⟩

 theorem weightPrefix_edge_bound {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (M : ℝ) :
    ∀ e∈(weightPrefix G w M).edgeSet,w e≤M := by
  intro e
  induction e using Sym2.inductionOn with
  | _ x y => exact fun h => h.2

 theorem weightedGirth_restrict {V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {g : ℝ}
    (hA : A≤G) (hG : WeightedGirthAbove G w g) : WeightedGirthAbove A w g := by
  intro a p hp e he
  have h := hG a (p.mapLe hA) (hp.mapLe hA) e (by simpa using he)
  simpa only [walkWeight_mapLe] using h

 theorem weightPrefix_phase_properties {V : Type*} {G : SimpleGraph V} {w : Sym2 V → ℝ}
    {M g cutoff : ℝ} {h : ℕ} (hG : WeightedGirthAbove G w g) (hfree : CliqueMinorFree G h)
    (hcutoff : M<cutoff) :
    WeightedGirthAbove (weightPrefix G w M) w g ∧ CliqueMinorFree (weightPrefix G w M) h ∧
      (∀ e∈(weightPrefix G w M).edgeSet,w e<cutoff) := by
  exact ⟨weightedGirth_restrict (weightPrefix_le G w M) hG,
    hfree.mono (weightPrefix_le G w M),fun e he => (weightPrefix_edge_bound G w M e he).trans_lt hcutoff⟩

end MinorFreeSpanners
