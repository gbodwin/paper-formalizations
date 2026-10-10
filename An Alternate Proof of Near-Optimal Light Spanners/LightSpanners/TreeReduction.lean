import LightSpanners.Subdivision
import LightSpanners.SubdivisionTree
import LightSpanners.SubdivisionGirth
import LightSpanners.RoundingTree
import LightSpanners.Construction

/-! Actual unit-MST reduction: scaling, a well-founded sequence of explicit
heavy-edge subdivisions, a proved vertex budget, and global rounding. -/
namespace LightSpanners
open SimpleGraph Finset

/-- A heavy edge can be split into a unit-bounded first piece and a positive
remainder whose ceiling is strictly smaller than the original ceiling. -/
theorem subdivision_split_ceiling {w : ℝ} (hw : 1 < w) :
    let a := w / (subdivisionPieces w : ℝ)
    0 < a ∧ a ≤ 1 ∧ 0 < w - a ∧
      ⌈a⌉₊ - 1 + (⌈w - a⌉₊ - 1) < subdivisionPieces w - 1 := by
  dsimp only
  have hb := subdivision_piece_bounds hw
  have hapos : 0 < w / (subdivisionPieces w : ℝ) := by linarith [hb.1]
  have hbpos : 0 < w - w / (subdivisionPieces w : ℝ) := by linarith [hb.2]
  have hwk : w ≤ (subdivisionPieces w : ℝ) := Nat.le_ceil w
  have hk : 2 ≤ subdivisionPieces w := by
    by_contra! h
    have hh : (subdivisionPieces w : ℝ) ≤ 1 := by exact_mod_cast (show subdivisionPieces w ≤ 1 by omega)
    linarith
  have hkreal : (2 : ℝ) ≤ subdivisionPieces w := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < subdivisionPieces w := by linarith
  have hmul : w / (subdivisionPieces w : ℝ) * subdivisionPieces w = w :=
    div_mul_cancel₀ _ hkpos.ne'
  have hrem : w - w / (subdivisionPieces w : ℝ) ≤
      (subdivisionPieces w : ℝ) - 1 := by
    apply (mul_le_mul_iff_left₀ hkpos).mp
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hwk)
      (show 0 ≤ (subdivisionPieces w : ℝ) - 1 by linarith)
    nlinarith
  have hceil_a : ⌈w / (subdivisionPieces w : ℝ)⌉₊ = 1 := by
    apply (Nat.ceil_eq_iff (by decide : 1 ≠ 0)).mpr
    simpa using And.intro hapos hb.2
  have hceil_b : ⌈w - w / (subdivisionPieces w : ℝ)⌉₊ ≤ subdivisionPieces w - 1 := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_sub (by omega : 1 ≤ subdivisionPieces w)]
    norm_num
    linarith [hrem]
  have hceil_pos : 0 < ⌈w - w / (subdivisionPieces w : ℝ)⌉₊ := Nat.ceil_pos.mpr hbpos
  exact ⟨hapos, hb.2, hbpos, by omega⟩

variable {V : Type*} [DecidableEq V] [Fintype V]
attribute [local instance] Classical.propDecidable

/-- Number of excess ceiling-pieces in the tree. This integer vanishes when
every tree edge has weight at most one. -/
noncomputable def subdivisionExcess (T : SimpleGraph V) (w : Sym2 V → ℝ) : ℕ :=
  ∑ e ∈ T.edgeFinset, (⌈w e⌉₊ - 1)

theorem sum_subdivision_edges {A : Type*} [AddCommMonoid A]
    {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (f : Sym2 (Option V) → A) :
    ∑ e ∈ (subdivideEdge G u v).edgeFinset, f e =
      f s(some u, none) + f s(some v, none) +
        ∑ e ∈ G.edgeFinset.erase s(u,v), f (Sym2.map some e) := by
  classical
  have hnew (x : V) : s(some x, none) ∉
      (G.edgeFinset.erase s(u,v)).image (Sym2.map some) := by
    simp [Finset.mem_image, Sym2.exists]
  have hneq : s(some u, none) ≠ s(some v, none) := by
    simpa [Sym2.eq_iff] using huv.ne
  rw [subdivision_edgeFinset,
    Finset.sum_insert (by simp only [Finset.mem_insert]; exact not_or.mpr ⟨hneq, hnew u⟩),
    Finset.sum_insert (hnew v), Finset.sum_image]
  · exact (add_assoc _ _ _).symm
  · intro a _ b _ hab
    exact Sym2.map.injective (Option.some_injective V) hab

/-- Splitting one heavy tree edge decreases the integer potential. -/
theorem subdivisionExcess_decreases {T : SimpleGraph V} {u v : V}
    (huv : T.Adj u v) (w : Sym2 V → ℝ) (hw : 1 < w s(u,v)) :
    let a := w s(u,v) / (subdivisionPieces (w s(u,v)) : ℝ)
    subdivisionExcess (subdivideEdge T u v) (subdivideWeight w u a (w s(u,v) - a)) <
      subdivisionExcess T w := by
  classical
  dsimp only
  have hsplit := (subdivision_split_ceiling hw).2.2.2
  have hmap (e : Sym2 V) :
      subdivideWeight w u (w s(u,v) / (subdivisionPieces (w s(u,v)) : ℝ))
        (w s(u,v) - w s(u,v) / (subdivisionPieces (w s(u,v)) : ℝ)) (Sym2.map some e) =
      w e := by
    induction e using Sym2.inductionOn with | hf x y => rfl
  unfold subdivisionExcess
  rw [sum_subdivision_edges huv]
  simp only [hmap, subdivideWeight_new', ite_true,
    ite_eq_right (by simpa using huv.ne.symm)]
  have hsum := Finset.add_sum_erase T.edgeFinset (fun e => ⌈w e⌉₊ - 1) (a := s(u,v))
    (by simpa using (mem_edgeSet T).mpr huv)
  rw [← hsum]
  exact Nat.add_lt_add_right hsplit _

omit [DecidableEq V] in
/-- The integer potential is bounded by the actual tree weight, including
arbitrarily light original edges. -/
theorem subdivisionExcess_le_weight (T : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ T.edgeSet, 0 ≤ w e) :
    (subdivisionExcess T w : ℝ) ≤ totalWeight T w := by
  classical
  simp only [subdivisionExcess, totalWeight, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro e he
  by_cases hh : 1 < w e
  · exact (subdivision_new_vertices_lt hh).le
  · have hc : ⌈w e⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using le_of_not_gt hh)
    have hz : ⌈w e⌉₊ - 1 = 0 := by omega
    rw [hz]
    simpa only [Nat.cast_zero] using hw e (by simpa using he)

omit [DecidableEq V] in
/-- A proper edge-subgraph has strictly smaller total weight when all graph
edges have positive weights. -/
theorem totalWeight_lt_of_subgraph_ne {G T : SimpleGraph V}
    (hTG : T ≤ G) (hne : T ≠ G) (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ G.edgeSet, 0 < w e) : totalWeight T w < totalWeight G w := by
  classical
  have hss : T.edgeFinset ⊂ G.edgeFinset :=
    Finset.ssubset_iff_subset_ne.mpr ⟨edgeFinset_mono hTG, fun h => hne (edgeFinset_inj.mp h)⟩
  obtain ⟨e, heG, heT⟩ := Finset.exists_of_ssubset hss
  exact Finset.sum_lt_sum_of_subset (edgeFinset_mono hTG) heG heT
    (hw e (by simpa using heG)) (fun d hd _ => (hw d (by simpa using hd)).le)

omit [DecidableEq V] [Fintype V] in
/-- Nonnegative rescaling preserves a bottleneck-path certificate. -/
theorem HasBottleneckPaths.scale {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (h : HasBottleneckPaths G T w) {c : ℝ} (hc : 0 ≤ c) :
    HasBottleneckPaths G T (fun e => c * w e) := by
  intro x y hxy
  obtain ⟨p, hp⟩ := h x y hxy
  exact ⟨p, fun e he => mul_le_mul_of_nonneg_left (hp e he) hc⟩

omit [DecidableEq V] in
/-- A positive-weight tree on at least two vertices has positive total weight. -/
theorem tree_totalWeight_pos {T : SimpleGraph V} (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card V) (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ T.edgeSet, 0 < w e) : 0 < totalWeight T w := by
  have hc : T.edgeFinset.card + 1 = Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using hT.card_edgeFinset
  exact Finset.sum_pos (fun e he => hw e (by simpa using he))
    (Finset.card_pos.mp (by omega))

universe u

/-- Output data for the repeated subdivision construction. Both total weights
and the weighted-girth lower bound are preserved; the tree becomes unit-bounded. -/
def BoundedSubdivisionResult (W : Type u) (inst : Fintype W)
    (graphWeight treeWeight : ℝ) (vertexBound : ℕ) (g : ℝ) : Prop :=
  letI := inst
  ∃ (G T : SimpleGraph W) (w : Sym2 W → ℝ),
    T ≤ G ∧ T.IsTree ∧ HasBottleneckPaths G T w ∧
    (∀ e ∈ G.edgeSet, 0 < w e) ∧ WeightedGirthAbove G w g ∧
    totalWeight G w = graphWeight ∧ totalWeight T w = treeWeight ∧
    Fintype.card W ≤ vertexBound ∧ (∀ e ∈ T.edgeSet, w e ≤ 1)

/-- Repeated explicit heavy-edge subdivision terminates and adds at most the
initial integer potential many vertices. The result is an actual finite graph. -/
theorem exists_bounded_tree_subdivision_aux (k : ℕ) :
    ∀ (W : Type u) [Fintype W] (G T : SimpleGraph W) (w : Sym2 W → ℝ)
      (g : ℝ), 0 ≤ g → T.IsTree → T ≤ G → HasBottleneckPaths G T w →
      (∀ e ∈ G.edgeSet, 0 < w e) → WeightedGirthAbove G w g →
      subdivisionExcess T w ≤ k →
      ∃ (X : Type u) (instX : Fintype X),
        BoundedSubdivisionResult X instX (totalWeight G w) (totalWeight T w)
          (Fintype.card W + subdivisionExcess T w) g := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W inst G T w g hg hT hTG hopt hw hG hk
    classical
    by_cases hupper : ∀ e ∈ T.edgeSet, w e ≤ 1
    · exact ⟨W, inst, G, T, w, hTG, hT, hopt, hw, hG, rfl, rfl, by omega, hupper⟩
    · push Not at hupper
      obtain ⟨e, he, hheavy⟩ := hupper
      induction e using Sym2.inductionOn with
      | hf u v =>
        have huv : T.Adj u v := (mem_edgeSet T).mp he
        let a := w s(u,v) / (subdivisionPieces (w s(u,v)) : ℝ)
        let G1 := subdivideEdge G u v
        let T1 := subdivideEdge T u v
        let w1 := subdivideWeight w u a (w s(u,v) - a)
        obtain ⟨ha, _, hb, _⟩ := subdivision_split_ceiling hheavy
        have hsum : a + (w s(u,v) - a) = w s(u,v) := by ring
        have hsmall : subdivisionExcess T1 w1 < subdivisionExcess T w :=
          subdivisionExcess_decreases huv w hheavy
        obtain ⟨X, instX, GX, TX, wX, hTXG, hTX, hoptX, hwX, hgX,
          hweightG, hweightT, hcard, hupperX⟩ :=
          ih (subdivisionExcess T1 w1) (hsmall.trans_le hk) (Option W)
            G1 T1 w1 g hg (subdivideEdge_isTree huv hT) (subdivideEdge_mono hTG u v)
            (hopt.subdivideEdge huv hsum ha.le hb.le)
            (subdivideWeight_positive_edges w hw ha hb)
            (WeightedGirthAbove.subdivideEdge (hTG huv) w hsum ha.le hb.le hg hG) le_rfl
        let := instX
        refine ⟨X, instX, GX, TX, wX, hTXG, hTX, hoptX, hwX, hgX, ?_, ?_, ?_, hupperX⟩
        · exact hweightG.trans (totalWeight_subdivideEdge (hTG huv) w hsum)
        · exact hweightT.trans (totalWeight_subdivideEdge huv w hsum)
        · simp only [Fintype.card_option] at hcard
          omega

/-- Output of the first half of Lemma 3.5: an actual finite graph with a
unit-weight MST and a preserved weighted-girth lower bound. -/
def UnitTreeReductionResult (W : Type u) (inst : Fintype W)
    (vertexBound : ℕ) (g lowerLightness : ℝ) : Prop :=
  letI := inst
  ∃ (G T : SimpleGraph W) (w : Sym2 W → ℝ),
    IsMinimumSpanningTree G T w ∧ ¬ G.IsAcyclic ∧
    (∀ e ∈ G.edgeSet, 1 ≤ w e) ∧ (∀ e ∈ T.edgeSet, w e = 1) ∧
    WeightedGirthAbove G w g ∧ Fintype.card W ≤ vertexBound ∧
    lowerLightness ≤ lightness G T w

/-- A normalized graph with a bottleneck-certified spanning tree admits an
actual unit-MST reduction on at most `2n-1` vertices. Weighted girth does not
decrease, and lightness falls by at most a factor of two. This constructs the
repeated subdivision and its vertex budget; it does not assume that graph. -/
theorem normalized_unit_tree_reduction {U : Type u} [Fintype U]
    {G T : SimpleGraph U} (w : Sym2 U → ℝ) (g : ℝ)
    (hn : 2 ≤ Fintype.card U) (hg : 0 ≤ g) (hT : T.IsTree) (hTG : T ≤ G)
    (hopt : HasBottleneckPaths G T w) (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hG : WeightedGirthAbove G w g) (hnonforest : ¬ G.IsAcyclic)
    (hnormal : totalWeight T w = (Fintype.card U : ℝ) - 1) :
    ∃ (X : Type u) (instX : Fintype X),
      UnitTreeReductionResult X instX (2 * Fintype.card U - 1) g (lightness G T w / 2) := by
  classical
  obtain ⟨X, instX, GX, TX, wX, hTXG, hTX, hoptX, hwX, hgX,
    hweightG, hweightT, hcard, hupperX⟩ :=
    exists_bounded_tree_subdivision_aux (subdivisionExcess T w) U G T w g hg hT hTG hopt
      hw hG le_rfl
  let := instX
  have hproper : T ≠ G := by
    intro heq
    exact hnonforest (heq ▸ hT.isAcyclic)
  have hstrict := totalWeight_lt_of_subgraph_ne hTG hproper w hw
  have hneX : TX ≠ GX := by
    intro heq
    have heqWeight := congrArg (fun H => totalWeight H wX) heq
    rw [hweightT, hweightG] at heqWeight
    exact (ne_of_lt hstrict) heqWeight
  have hnonforestX : ¬ GX.IsAcyclic := by
    intro hGX
    have htree : GX.IsTree := ⟨hTX.connected.mono hTXG, hGX⟩
    have hle : GX ≤ TX := (isTree_iff_minimal_connected.mp htree).2 hTX.connected hTXG
    exact hneX (le_antisymm hTXG hle)
  have hp := subdivisionExcess_le_weight T w (fun e he => (hw e (edgeSet_mono hTG he)).le)
  rw [hnormal] at hp
  have hcast : ((Fintype.card U - 1 : ℕ) : ℝ) = (Fintype.card U : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card U)]
    norm_num
  rw [← hcast] at hp
  have hpNat : subdivisionExcess T w ≤ Fintype.card U - 1 := by exact_mod_cast hp
  have hcard' : Fintype.card X ≤ 2 * Fintype.card U - 1 := by omega
  have hlight : lightness GX TX wX = lightness G T w := by
    simp only [lightness, hweightG, hweightT]
  have hround := normalized_round_up_lightness hTX wX (Fintype.card U) hn hupperX
    (fun e he => (hwX e he).le) (hweightT.trans hnormal) hcard'
  rw [hlight] at hround
  exact ⟨X, instX, GX, TX, (fun e => max 1 (wX e)),
    round_up_isMinimumSpanningTree hTX hTXG wX hupperX, hnonforestX,
    (fun _ _ => le_max_left _ _), (fun e he => max_eq_left (hupperX e he)),
    hgX.round_up hg hwX, hcard', hround⟩

/-- Scale, repeatedly subdivide, and round an actual positive weighted graph.
This completes the unit-MST stage of the reduction from a bottleneck-certified
tree: at most `2n-1` vertices, no decrease in weighted girth, non-forest output,
and a loss of at most two in lightness. -/
theorem unit_tree_reduction {U : Type u} [Fintype U]
    {G T : SimpleGraph U} (w : Sym2 U → ℝ) (g : ℝ)
    (hn : 2 ≤ Fintype.card U) (hg : 0 ≤ g) (hT : T.IsTree) (hTG : T ≤ G)
    (hopt : HasBottleneckPaths G T w) (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hG : WeightedGirthAbove G w g) (hnonforest : ¬ G.IsAcyclic) :
    ∃ (X : Type u) (instX : Fintype X),
      UnitTreeReductionResult X instX (2 * Fintype.card U - 1) g (lightness G T w / 2) := by
  classical
  have htpos := tree_totalWeight_pos hT hn w (fun e he => hw e (edgeSet_mono hTG he))
  have hnreal : (1 : ℝ) < Fintype.card U := by
    exact_mod_cast (show 1 < Fintype.card U by omega)
  let c := ((Fintype.card U : ℝ) - 1) / totalWeight T w
  have hc : 0 < c := div_pos (by linarith) htpos
  have hnormal : totalWeight T (fun e => c * w e) = (Fintype.card U : ℝ) - 1 := by
    rw [totalWeight_scale]
    dsimp only [c]
    exact div_mul_cancel₀ _ htpos.ne'
  have h := normalized_unit_tree_reduction (fun e => c * w e) g hn hg hT hTG
    (hopt.scale hc.le) (fun e he => mul_pos hc (hw e he))
    ((weightedGirthAbove_scale_iff hc).mpr hG) hnonforest hnormal
  simpa only [lightness_scale G T w hc] using h

/-- Kruskal supplies a bottleneck-certified tree for an actual finite connected
graph; no external edge order or path certificate is required. -/
theorem exists_bottleneck_spanning_tree {U : Type u} [Fintype U]
    (G : SimpleGraph U) (w : Sym2 U → ℝ) (hconn : G.Connected) :
    ∃ T : SimpleGraph U, T ≤ G ∧ T.IsTree ∧ HasBottleneckPaths G T w := by
  classical
  refine ⟨edgeGraph (kruskalEdges (greedyInput G w)), ?_, ?_, ?_⟩
  · simpa only [greedyInput_graph] using
      edgeGraph_mono (kruskalEdges_subset (greedyInput G w))
  · apply kruskal_isTree _ (greedyInput_nondiag G w)
    simpa only [greedyInput_graph] using hconn
  · intro x y hxy
    have he : s(x,y) ∈ greedyInput G w := by simpa using hxy
    obtain ⟨p, _, hp⟩ := kruskal_bottleneck w (greedyInput G w)
      (greedyInput_nondiag G w) (greedyInput_sorted G w) s(x,y) he x y rfl
    exact ⟨p, hp⟩

/-- The unit-MST stage for any explicit reference MST. Kruskal, positive
rescaling, repeated heavy-edge subdivision, and rounding are all constructed
inside this proof. The Euler-tour spanning-cycle stage remains separate. -/
theorem unit_tree_reduction_of_mst {U : Type u} [Fintype U]
    {G T : SimpleGraph U} (w : Sym2 U → ℝ) (g : ℝ)
    (hn : 2 ≤ Fintype.card U) (hg : 0 ≤ g) (hT : IsMinimumSpanningTree G T w)
    (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hG : WeightedGirthAbove G w g) (hnonforest : ¬ G.IsAcyclic) :
    ∃ (X : Type u) (instX : Fintype X),
      UnitTreeReductionResult X instX (2 * Fintype.card U - 1) g (lightness G T w / 2) := by
  classical
  obtain ⟨K, hKG, hK, hopt⟩ := exists_bottleneck_spanning_tree G w
    (hT.2.1.connected.mono hT.1)
  have hKmin := minimumSpanningTree_of_bottleneck hK hKG hopt
  have h := unit_tree_reduction w g hn hg hK hKG hopt hw hG hnonforest
  simpa only [lightness_mst_independent hKmin hT] using h

end LightSpanners
