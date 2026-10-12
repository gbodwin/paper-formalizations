import MinorFreeSpanners.CanonicalPrefixHistoryStep

/-! Iterate the actual fresh paid prefix phase. Every finite geometric stream
has a constructed endpoint family and a literal disjoint tree-edge history;
all phase injections are bounded by their explicit geometric allowances. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem canonical_finite_stream {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h : ℕ) (u : ℝ) (ht : 4096≤t) (hu : 1≤u) (hr : 1≤r) (hh : 0<h)
    (S0 : FiniteScaleState (weightPrefix G w (2*u)) w (200*u) (canonicalPhaseCredit t r h) u)
    (hT : T≤G) (hTconn : T.Connected) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hfree : CliqueMinorFree G h) (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e) (n : ℕ) :
    ∃ last : FiniteScaleState (weightPrefix G w (2*((t:ℝ)^n*u))) w
        (200*((t:ℝ)^n*u)) (canonicalPhaseCredit t r h) ((t:ℝ)^n*u),
    ∃ history : Finset (Sym2 V),(∀ e∈history,e∈T.edgeSet) ∧
      (∀ i,∃ j,S0.family.branch i⊆last.family.branch j) ∧
      (∀ e∈history,∃ j x y,x∈last.family.branch j ∧ y∈last.family.branch j ∧ e=s(x,y)) ∧
      (∑ k∈range n,∑ e∈(weightBand G w ((t:ℝ)^(k+1)*u) (2*((t:ℝ)^(k+1)*u))).edgeFinset,w e)+
        (∑ j,last.credit j)≤(∑ i,S0.credit i)+
        (∑ k∈range n,10*canonicalPhaseCredit t r h*(2*((t:ℝ)^(k+1)*u)))+
        canonicalPhaseCredit t r h*(∑ e∈history,w e) := by
  have ht1 : (1:ℝ)≤t := by exact_mod_cast (show 1≤t by omega)
  have huall (k : ℕ) : 1≤(t:ℝ)^k*u := by
    have hp : 1≤(t:ℝ)^k := one_le_pow₀ ht1
    nlinarith only [hp,hu]
  induction n with
  | zero =>
    rw [pow_zero,one_mul]
    refine ⟨S0,∅,by simp,fun i => ⟨i,fun _ hx => hx⟩,by simp,?_⟩
    simp only [Finset.range_zero,Finset.sum_empty,mul_zero,add_zero,zero_add]
    exact le_rfl
  | succ n ih =>
    obtain ⟨last,history,histT,hcoarse,hinternal,hpaid⟩ := ih
    have scale : (t:ℝ)*((t:ℝ)^n*u)=(t:ℝ)^(n+1)*u := by rw [pow_succ];ring
    have phase := canonical_prefix_history_step t r h ((t:ℝ)^n*u) ht (huall n) hr hh last
      hT hTconn hunit hfree hG hw history histT hinternal
    rw [scale] at phase
    obtain ⟨next,injection,hi,hbound,current,hdis,hTree,hcoarseNext,hint,hstep⟩ := phase
    refine ⟨next,history∪current,hTree,?_,hint,?_⟩
    · intro i
      obtain ⟨j,hj⟩ := hcoarse i
      obtain ⟨k,hk⟩ := hcoarseNext j
      exact ⟨k,hj.trans hk⟩
    · rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_union hdis]
      nlinarith only [hpaid,hstep,hbound]

end MinorFreeSpanners
