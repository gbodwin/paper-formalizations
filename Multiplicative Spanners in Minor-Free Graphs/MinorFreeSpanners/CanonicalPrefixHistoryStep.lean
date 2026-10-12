import MinorFreeSpanners.CanonicalHistoryStep
import MinorFreeSpanners.WeightPrefixHost

/-! The actual next phase runs in the literal next weight prefix and pays its
literal weight band. Its intrinsic paths are therefore light at the following
scale, allowing another invocation without a supplied host-closure premise. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 def weightBand {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (lo hi : ℝ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ lo≤w s(x,y) ∧ w s(x,y)≤hi
  symm := ⟨by rintro x y ⟨hxy,hlo,hhi⟩;exact ⟨hxy.symm,by simpa only [Sym2.eq_swap] using hlo,
    by simpa only [Sym2.eq_swap] using hhi⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

 theorem canonical_prefix_history_step {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h : ℕ) (u : ℝ) (ht : 4096≤t) (hu : 1≤u) (hr : 1≤r) (hh : 0<h)
    (S : FiniteScaleState (weightPrefix G w (2*u)) w (200*u) (canonicalPhaseCredit t r h) u)
    (hT : T≤G) (hTconn : T.Connected) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hfree : CliqueMinorFree G h) (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e)
    (earlier : Finset (Sym2 V)) (hearlierT : ∀ e∈earlier,e∈T.edgeSet)
    (hearlier : ∀ e∈earlier,∃ i x y,x∈S.family.branch i ∧ y∈S.family.branch i ∧ e=s(x,y)) :
    ∃ next : FiniteScaleState (weightPrefix G w (2*((t:ℝ)*u))) w
        (200*((t:ℝ)*u)) (canonicalPhaseCredit t r h) ((t:ℝ)*u),
    ∃ injection : ℝ,0≤ injection ∧ injection≤10*canonicalPhaseCredit t r h*(2*((t:ℝ)*u)) ∧
    ∃ current : Finset (Sym2 V),Disjoint earlier current ∧ (∀ e∈earlier∪current,e∈T.edgeSet) ∧
      (∀ i,∃ j,S.family.branch i⊆next.family.branch j) ∧
      (∀ e∈earlier∪current,∃ j x y,x∈next.family.branch j ∧ y∈next.family.branch j ∧ e=s(x,y)) ∧
      (∑ e∈(weightBand G w ((t:ℝ)*u) (2*((t:ℝ)*u))).edgeFinset,w e)+(∑ j,next.credit j)≤
        (∑ i,S.credit i)+injection+canonicalPhaseCredit t r h*(∑ e∈current,w e) := by
  have htR : (4096:ℝ)≤t := by exact_mod_cast ht
  have hu0 : 0≤u := by linarith only [hu]
  have hlightScale : 2*u<(t:ℝ)*u := by nlinarith only [htR,hu]
  have hnext : 1≤(t:ℝ)*u := by nlinarith only [htR,hu]
  have hA : weightPrefix G w (2*u)≤weightPrefix G w (2*((t:ℝ)*u)) := by
    intro x y hxy
    exact ⟨hxy.1,hxy.2.trans (by linarith only [hlightScale,hu0])⟩
  have hB : weightBand G w ((t:ℝ)*u) (2*((t:ℝ)*u))≤weightPrefix G w (2*((t:ℝ)*u)) :=
    fun _ _ hxy => ⟨hxy.1,hxy.2.2⟩
  have hTree : T≤weightPrefix G w (2*((t:ℝ)*u)) := le_weightPrefix hT
    (fun e he => by rw [hunit e he];linarith only [hnext])
  have hlow : ∀ e∈(weightBand G w ((t:ℝ)*u) (2*((t:ℝ)*u))).edgeSet,(t:ℝ)*u≤w e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ x y => exact fun he => he.2.1
  have hhigh : ∀ e∈(weightBand G w ((t:ℝ)*u) (2*((t:ℝ)*u))).edgeSet,w e≤2*(t:ℝ)*u := by
    intro e
    induction e using Sym2.inductionOn with
    | _ x y => intro he;simpa only [mul_assoc] using he.2.2
  have out := canonical_history_step t r h u ht hu hr hh S hA hB hTree hTconn hunit
    (hfree.mono (weightPrefix_le G w _)) (weightedGirth_restrict (weightPrefix_le G w _) hG)
    (fun e he => hw e (edgeSet_mono (weightPrefix_le G w _) he))
    (fun e he => (weightPrefix_edge_bound G w (2*u) e he).trans_lt hlightScale)
    hlow hhigh earlier hearlierT hearlier
  simpa only [mul_assoc] using out

end MinorFreeSpanners
