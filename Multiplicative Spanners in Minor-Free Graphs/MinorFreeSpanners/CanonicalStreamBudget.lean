import MinorFreeSpanners.CanonicalFiniteStream
import MinorFreeSpanners.EmptyRootStreamBudget

/-! The constructed finite stream is paid by its actual unit spanning tree.
Only the last processed band needs an edge witness; earlier empty bands and
their possible singleton injections are all included. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem canonical_stream_weight_bound {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (t r h : ℕ) (u : ℝ) (ht : 4096≤t) (hu : 1≤u) (hr : 1≤r) (hh : 0<h)
    (S0 : FiniteScaleState (weightPrefix G w (2*u)) w (200*u) (canonicalPhaseCredit t r h) u)
    (hinitial : (∑ i,S0.credit i)≤canonicalPhaseCredit t r h*(T.edgeFinset.card:ℝ))
    (hT : T≤G) (hTconn : T.Connected) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hfree : CliqueMinorFree G h) (hG : WeightedGirthAbove G w (2*(r:ℝ)*(1+2000/(t:ℝ))))
    (hw : ∀ e∈G.edgeSet,0≤w e) (n : ℕ)
    (hne : (weightBand G w ((t:ℝ)^(n+1)*u) (2*((t:ℝ)^(n+1)*u))).edgeSet.Nonempty) :
    (∑ k∈range (n+1),∑ e∈(weightBand G w ((t:ℝ)^(k+1)*u)
      (2*((t:ℝ)^(k+1)*u))).edgeFinset,w e)≤42*canonicalPhaseCredit t r h*(T.edgeFinset.card:ℝ) := by
  have hc : 0≤canonicalPhaseCredit t r h := by unfold canonicalPhaseCredit;positivity
  have hg := (canonical_phase_girth t r u ht hr hu).1
  have ht2 : (2:ℝ)≤t := by exact_mod_cast (show 2≤t by omega)
  have hu0 : 0≤u := by linarith only [hu]
  have hB : weightBand G w ((t:ℝ)^(n+1)*u) (2*((t:ℝ)^(n+1)*u))≤G := fun _ _ hxy => hxy.1
  have hband : ∀ e∈(weightBand G w ((t:ℝ)^(n+1)*u) (2*((t:ℝ)^(n+1)*u))).edgeSet,
      (2*(t:ℝ)*u*(t:ℝ)^n)/2≤w e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
      intro he
      have hl := he.2.1
      rw [pow_succ] at hl
      nlinarith only [hl]
  have hi := empty_root_stream_injections_le_tree hT hTconn hunit hg hG hw hB ht2
    (show 0≤2*(t:ℝ)*u by positivity) hc n hband hne
  have hinjection : (∑ k∈range (n+1),10*canonicalPhaseCredit t r h*(2*((t:ℝ)^(k+1)*u)))≤
      40*canonicalPhaseCredit t r h*(T.edgeFinset.card:ℝ) := by
    convert hi using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  obtain ⟨last,history,histT,hcoarse,hinternal,hpaid⟩ := canonical_finite_stream t r h u ht hu hr hh
    S0 hT hTconn hunit hfree hG hw (n+1)
  have hs : (∑ e∈history,w e)≤(T.edgeFinset.card:ℝ) := by
    have hsub : history⊆T.edgeFinset := fun e he => by simpa using histT e he
    calc
      (∑ e∈history,w e)≤∑ e∈T.edgeFinset,w e := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun e he _ => hw e (edgeSet_mono hT (by simpa using he)))
      _=(T.edgeFinset.card:ℝ) := by
        calc
          (∑ e∈T.edgeFinset,w e)=∑ _e∈T.edgeFinset,(1:ℝ) := Finset.sum_congr rfl
            (fun e he => hunit e (by simpa using he))
          _=_ := by simp
  have hcLast : 0≤∑ i,last.credit i := Finset.sum_nonneg (fun i _ => last.credit_nonnegative i)
  have hhistory := mul_le_mul_of_nonneg_left hs hc
  nlinarith only [hpaid,hinjection,hinitial,hhistory,hcLast]

end MinorFreeSpanners
