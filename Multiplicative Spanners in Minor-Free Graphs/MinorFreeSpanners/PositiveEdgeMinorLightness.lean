import MinorFreeSpanners.EdgeWeightTransport

/-! The existential upper bound needs positivity only on actual input edges,
and accepts every positive stretch slack using its literal cap at one. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable
universe u

 theorem positive_edge_minor_lightness {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (eps : ℝ) (heps : 0<eps) (r h : ℕ) (hr : 1≤r) (hh : 3≤h)
    (hn : 2≤Fintype.card V) (hconn : G.Connected)
    (hfree : CliqueMinorFree G h) (hw : ∀ e∈G.edgeSet,0<w e) :
    ∃ H T : SimpleGraph V, IsSpanner G H w ((1+eps)*(2*(r:ℝ)-1)) ∧
      CliqueMinorFree H h ∧ T≤H ∧ IsMinimumSpanningTree G T w ∧
      lightness H T w≤minorLightnessConstant*(Real.logb 2 (8097/min eps 1)+1)*
        (Nat.log 2 h+2:ℕ)^9*(h:ℝ)^(2/(r+1:ℝ))/(min eps 1)^3 := by
  let z : Sym2 V → ℝ := fun e => if e∈G.edgeSet then w e else 1
  have hz : ∀ e,0<z e := by intro e; dsimp [z]; split_ifs with he; exact hw e he; norm_num
  have heq : ∀ e∈G.edgeSet,z e=w e := by intro e he; simp [z,he]
  have hd : 0<min eps 1 := lt_min heps (by norm_num)
  obtain ⟨hspan,hminor,T,hTH,hTG,hlight⟩ := greedy_minor_polylog_lightness G z
    (min eps 1) hd (min_le_right _ _) r h hr hh hn hconn hfree hz
  let H := greedyOutput G z ((1+min eps 1)*(2*(r:ℝ)-1))
  have hspanw : IsSpanner G H w ((1+min eps 1)*(2*(r:ℝ)-1)) := spanner_congr_edges heq hspan
  have hstretch : (1+min eps 1)*(2*(r:ℝ)-1)≤(1+eps)*(2*(r:ℝ)-1) := by
    apply mul_le_mul_of_nonneg_right (by linarith [min_le_left eps (1:ℝ)])
    have hrR : (1:ℝ)≤r := by exact_mod_cast hr
    linarith
  refine ⟨H,T,⟨hspanw.1,?_⟩,hminor,hTH,mst_congr_edges heq hTG,?_⟩
  · intro a b p
    obtain ⟨q,hq⟩ := hspanw.2 a b p
    have hp : 0≤walkWeight w p := by
      rw [←walkWeight_congr_edges le_rfl heq p]
      exact walkWeight_nonneg z (fun e => (hz e).le) p
    exact ⟨q,hq.trans (mul_le_mul_of_nonneg_right hstretch hp)⟩
  · change totalWeight H w/totalWeight T w≤_
    rw [←totalWeight_congr_edges hspan.1 heq,←totalWeight_congr_edges hTG.1 heq]
    exact hlight

end MinorFreeSpanners
