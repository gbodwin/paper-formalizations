import LightEFTSpanners.GraphPruning
import LightEFTSpanners.WeightedSampling
import LightEFTSpanners.StretchParameters

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners BlockerSampling
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A real sampled/pruned host graph has high weighted girth, retains an actual
MST no heavier than the host tree, and keeps the required candidate weight.
This is the graph assembly in Lemmas26–27; no expected-weight, girth, minimum-
tree existence or final weight bound is assumed. The host tree itself is input,
so this is not a forest-packing existence theorem. -/
theorem exists_heavy_girth_host {G T : SimpleGraph V} {seed U : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {t : ℝ} {f : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w t f B) (hT : T.IsTree) (hTG : T ≤ G)
    (hTseed : ∀ e∈T.edgeSet,e∈seed) (hUG : ∀ e∈U,e∈G.edgeSet)
    (hUseed : ∀ e∈U,e∉seed)
    (hhost : ∀ e∈U, Disjoint (B e) T.edgeFinset)
    (hw : ∀ e∈G.edgeSet,0≤w e) (hf : 0<f) (ht : 0≤t+1) :
    ∃ R K : SimpleGraph V, R ≤ G ∧ IsMinimumSpanningTree R K w ∧
      totalWeight K w ≤ totalWeight T w ∧ WeightedGirthAbove R w (t+1) ∧
      (∑ e∈U,w e)/(4*(f:ℝ)) ≤ totalWeight R w := by
  classical
  obtain ⟨S,hSU,hweight⟩ := exists_heavy_surviving_sample U B w
    (fun e he => hw e (hUG e he)) f hf (fun e _ => hB.capped e) (fun e _ => hB.no_self e)
  let X := T ⊔ edgeGraph S
  have hXG : X ≤ G := by
    apply sup_le hTG
    intro u v huv
    have he := (mem_edgeGraph S _).mp ((mem_edgeSet _).mpr huv)
    exact (mem_edgeSet G).mp (hUG _ (hSU he.1))
  have hseed : ∀ e∈X.edgeSet,e∈seed → e∈T.edgeSet := by
    intro e he hs
    rw [show X=T⊔edgeGraph S from rfl,edgeSet_sup] at he
    rcases he with he | he
    · exact he
    · exact (hUseed e (hSU ((mem_edgeGraph S e).mp he).1) hs).elim
  obtain ⟨K,hmin,hKT,hg⟩ := exists_finalPrune hB hXG hT (show T≤X from le_sup_left)
    hTseed hseed ht
  let R := (cleanGraph X B).deleteEdges (T.edgeSet \ K.edgeSet)
  have hRG : R ≤ G := (SimpleGraph.deleteEdges_le (G := cleanGraph X B) _).trans
    ((cleanGraph_le X B).trans hXG)
  have hsurvive : surviving U B S ⊆ R.edgeFinset := by
    intro e he
    obtain ⟨heU,heS,hdis⟩ := mem_filter.mp he
    have hediag : ¬e.IsDiag := G.not_isDiag_of_mem_edgeSet (hUG e heU)
    apply mem_edgeFinset.mpr
    rw [show R=(cleanGraph X B).deleteEdges (T.edgeSet \ K.edgeSet) from rfl,
      edgeSet_deleteEdges]
    constructor
    · apply (mem_cleanGraph X B e).mpr
      constructor
      · rw [show X=T⊔edgeGraph S from rfl,edgeSet_sup]
        exact Or.inr ((mem_edgeGraph S e).mpr ⟨heS,hediag⟩)
      · apply Finset.disjoint_left.mpr
        intro d hdB hdX
        have hd : d ∈ X.edgeSet := by simpa only [mem_edgeFinset] using hdX
        rw [show X=T⊔edgeGraph S from rfl,edgeSet_sup] at hd
        rcases hd with hdT | hdS
        · exact Finset.disjoint_left.mp (hhost e heU) hdB (mem_edgeFinset.mpr hdT)
        · have hdS' := ((mem_edgeGraph S d).mp hdS).1
          exact Finset.disjoint_left.mp hdis (mem_inter.mpr ⟨hdB,hSU hdS'⟩) hdS'
    · intro hd
      exact hUseed e heU (hTseed e hd.1)
  refine ⟨R,K,hRG,hmin,hKT,hg,hweight.trans ?_⟩
  unfold totalWeight
  apply sum_le_sum_of_subset_of_nonneg
  · intro e he
    have heR : e∈R.edgeSet := by simpa only [mem_edgeFinset] using hsurvive he
    simpa only [mem_edgeFinset] using heR
  · intro e he _
    have heR : e∈R.edgeSet := by simpa only [mem_edgeFinset] using he
    exact hw e (SimpleGraph.edgeSet_mono hRG heR)
/-- An explicit polynomial bound for the actual candidates of one supplied
host. The high-girth graph and its minimum tree are constructed above; the
coarse lightness theorem is applied at the corrected threshold. This does not
assert that a global host packing exists. -/
theorem host_candidate_weight_bound {G T : SimpleGraph V} {seed U : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {eps : ℝ} {f k : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w ((1+eps)*(2*k-1)) f B)
    (hT : T.IsTree) (hTG : T ≤ G)
    (hTseed : ∀ e∈T.edgeSet,e∈seed) (hUG : ∀ e∈U,e∈G.edgeSet)
    (hUseed : ∀ e∈U,e∉seed)
    (hhost : ∀ e∈U, Disjoint (B e) T.edgeFinset)
    (hw : ∀ e∈G.edgeSet,0<w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps)
    (hn : 2 ≤ Fintype.card V) :
    (∑ e∈U,w e) ≤ 4*(f:ℝ) *
      (8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹)) * totalWeight T w := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hkterm : 0≤2*(k:ℝ)-1 := by linarith
  have ht : 0≤(1+eps)*(2*(k:ℝ)-1)+1 := by positivity
  obtain ⟨R,K,hRG,hK,hKT,hg,hweight⟩ := exists_heavy_girth_host
    hB hT hTG hTseed hUG hUseed hhost (fun e he => (hw e he).le) hf ht
  have hwR : ∀ e∈R.edgeSet,0<w e := fun e he => hw e (edgeSet_mono hRG he)
  have hKpos := tree_totalWeight_pos hK.2.1 hn w
    (fun e he => hwR e (edgeSet_mono hK.1 he))
  have hb := corrected_threshold_lightness hK hwR heps hk hg
  have hmul := (div_le_iff₀ hKpos).mp hb
  have hcoeff : 0≤8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by positivity
  have hupper := hmul.trans (mul_le_mul_of_nonneg_left hKT hcoeff)
  have hfR : (0:ℝ)<4*(f:ℝ) := by positivity
  have hsum := (div_le_iff₀ hfR).mp (hweight.trans hupper)
  nlinarith
end LightEFTSpanners
