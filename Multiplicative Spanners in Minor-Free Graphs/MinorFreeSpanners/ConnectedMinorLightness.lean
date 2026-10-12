import MinorFreeSpanners.SmallCliqueLightnessDomain

/-! All positive clique orders and all connected finite graph sizes, including
the zero-tree-weight singleton boundary, are covered explicitly. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable
universe u

 theorem connected_minor_lightness {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (eps : ℝ) (heps : 0<eps) (r h : ℕ) (hr : 1≤r) (hh : 0<h)
    (hconn : G.Connected) (hfree : CliqueMinorFree G h) (hw : ∀ e∈G.edgeSet,0<w e) :
    ∃ H T : SimpleGraph V, IsSpanner G H w ((1+eps)*(2*(r:ℝ)-1)) ∧
      CliqueMinorFree H h ∧ T≤H ∧ IsMinimumSpanningTree G T w ∧
      lightness H T w≤minorLightnessConstant*(Real.logb 2 (8097/min eps 1)+1)*
        (Nat.log 2 h+2:ℕ)^9*(h:ℝ)^(2/(r+1:ℝ))/(min eps 1)^3 := by
  by_cases hn : 2≤Fintype.card V
  · exact positive_edge_minor_lightness G w eps heps r h hr
      (nontrivial_connected_clique_order G h hh hn hconn hfree) hn hconn hfree hw
  · have hcard : Fintype.card V≤1 := by omega
    let := Fintype.card_le_one_iff_subsingleton.mp hcard
    have hbot : G=⊥ := Subsingleton.elim _ _
    have htree : G.IsTree := ⟨hconn,by rw [hbot]; exact isAcyclic_bot⟩
    refine ⟨G,G,⟨le_rfl,?_⟩,hfree,le_rfl,⟨le_rfl,htree,?_⟩,?_⟩
    · intro a b p
      refine ⟨p,?_⟩
      have hz : walkWeight w p=0 := by
        induction p with
        | nil => simp
        | cons hadj _ _ => simp [hbot] at hadj
      simp [hz]
    · intro S hS _
      have heq : S=G := by apply le_antisymm hS; rw [hbot]; exact bot_le
      simp [heq]
    · have hd : 0<min eps 1 := lt_min heps (by norm_num)
      have harg : (1:ℝ)≤8097/min eps 1 := by
        apply (le_div_iff₀ hd).mpr
        linarith [min_le_right eps (1:ℝ)]
      have hlog : 0≤Real.logb 2 (8097/min eps 1) := Real.logb_nonneg (by norm_num) harg
      have hempty : G.edgeFinset=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        have hedge := G.mem_edgeFinset.mp he
        simp [hbot] at hedge
      simp only [lightness,totalWeight,hempty,Finset.sum_empty,zero_div]
      unfold minorLightnessConstant
      positivity

end MinorFreeSpanners
