import MinorFreeSpanners.NormalizedMinorLightness

/-! The bound applies to the literal ordered greedy output and its retained
MST of the original input, with the same corrected weighted-girth guarantee. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable
universe u

 theorem greedy_minor_lightness {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (eps : ℝ) (heps : 0<eps) (heps1 : eps≤1)
    (r h : ℕ) (hr : 1≤r) (hh : 3≤h)
    (hn : 2≤Fintype.card V) (hconn : G.Connected)
    (hfree : CliqueMinorFree G h) (hw : ∀ e,0<w e) :
    let stretch := (1+eps)*(2*(r:ℝ)-1)
    IsSpanner G (greedyOutput G w stretch) w stretch ∧
    CliqueMinorFree (greedyOutput G w stretch) h ∧
    ∃ T : SimpleGraph V, T≤greedyOutput G w stretch ∧ IsMinimumSpanningTree G T w ∧
      lightness (greedyOutput G w stretch) T w≤
        2*(42*(Nat.log 2 (canonicalScale eps)+1:ℕ)+1)*canonicalPhaseCredit (canonicalScale eps) r h := by
  intro stretch
  have ht : 1≤stretch := by
    dsimp [stretch]
    have hrR : (1:ℝ)≤r := by exact_mod_cast hr
    nlinarith
  obtain ⟨hspan,_,hg,T,hTH,hTG⟩ := greedyOutput_preliminaries G w stretch ht (fun e => (hw e).le) hconn
  have hminor := greedy_minorFree G w stretch h hfree
  have hH : greedyOutput G w stretch≤G := hspan.1
  have hTM : IsMinimumSpanningTree (greedyOutput G w stretch) T w := by
    refine ⟨hTH,hTG.2.1,?_⟩
    intro S hSH hS
    exact hTG.2.2 S (hSH.trans hH) hS
  exact ⟨hspan,hminor,T,hTH,hTG,
    normalized_minor_lightness eps heps heps1 r h hr hh hn hTM hminor hg (fun e _ => hw e)⟩

end MinorFreeSpanners
