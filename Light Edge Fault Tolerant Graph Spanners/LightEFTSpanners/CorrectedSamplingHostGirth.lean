import LightEFTSpanners.GraphPruning
import LightEFTSpanners.CorrectedSamplingExpectedWeight
import LightEFTSpanners.StretchParameters

namespace LightEFTSpanners.CorrectedDeterministicSampling
open SimpleGraph Finset LightSpanners LightSpanners.FiniteSampling
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Every actual sample is cleaned and pruned, retaining each sampled
candidate that has no sampled blocker. The MST and girth conclusions are
constructed simultaneously; no random accuracy premise occurs. -/
theorem exists_girth_host_of_sample {G T : SimpleGraph V} {seed U : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {t : ℝ} {f : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w t f B) (hT : T.IsTree) (hTG : T ≤ G)
    (hTseed : ∀ e∈T.edgeSet,e∈seed) (hUG : ∀ e∈U,e∈G.edgeSet)
    (hUseed : ∀ e∈U,e∉seed)
    (hhost : ∀ e∈U, Disjoint (B e) T.edgeFinset)
    (S : Finset (Sym2 V)) (hSU : S⊆U)
    (hw : ∀ e∈G.edgeSet,0≤w e) (ht : 0≤t+1) :
    ∃ R K : SimpleGraph V, R ≤ G ∧ IsMinimumSpanningTree R K w ∧
      totalWeight K w ≤ totalWeight T w ∧ WeightedGirthAbove R w (t+1) ∧
      (∑ e∈surviving U B S,w e) ≤ totalWeight R w := by
  classical
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
  refine ⟨R,K,hRG,hmin,hKT,hg,?_⟩
  unfold totalWeight
  apply sum_le_sum_of_subset_of_nonneg
  · intro e he
    have heR : e∈R.edgeSet := by simpa only [mem_edgeFinset] using hsurvive he
    simpa only [mem_edgeFinset] using heR
  · intro e he _
    have heR : e∈R.edgeSet := by simpa only [mem_edgeFinset] using he
    exact hw e (SimpleGraph.edgeSet_mono hRG heR)
/-- An actual 1/f Bernoulli sample attains the expected candidate bound,
then the same sample is cleaned and pruned to a real high-girth host. -/
theorem exists_heavy_girth_host {G T : SimpleGraph V} {seed U : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {t : ℝ} {f : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w t f B) (hT : T.IsTree) (hTG : T ≤ G)
    (hTseed : ∀ e∈T.edgeSet,e∈seed) (hUG : ∀ e∈U,e∈G.edgeSet)
    (hUseed : ∀ e∈U,e∉seed)
    (hhost : ∀ e∈U, Disjoint (B e) T.edgeFinset)
    (hw : ∀ e∈G.edgeSet,0≤w e) (hf : 2≤f) (ht : 0≤t+1) :
    ∃ R K : SimpleGraph V, R ≤ G ∧ IsMinimumSpanningTree R K w ∧
      totalWeight K w ≤ totalWeight T w ∧ WeightedGirthAbove R w (t+1) ∧
      (∑ e∈U,w e)/(4*(f:ℝ)) ≤ totalWeight R w := by
  obtain ⟨S,hSU,hweight⟩ := exists_heavy_surviving_sample U B w
    (fun e he => hw e (hUG e he)) f hf (fun e _ => hB.capped e) (fun e _ => hB.no_self e)
  obtain ⟨R,K,hRG,hK,hKT,hg,hwR⟩ := exists_girth_host_of_sample hB hT hTG
    hTseed hUG hUseed hhost S hSU hw ht
  exact ⟨R,K,hRG,hK,hKT,hg,hweight.trans hwR⟩

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
    (hw : ∀ e∈G.edgeSet,0<w e) (hf : 2≤f) (hk : 0<k) (heps : 0<eps)
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
omit [DecidableEq V] in
private theorem weight_eq_edge_sum (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (a : Fintype G.edgeSet) : totalWeight G w=∑ e∈@SimpleGraph.edgeFinset V G a,w e := by
  unfold totalWeight
  have hh (a b : Fintype G.edgeSet) :
      (∑ e∈@SimpleGraph.edgeFinset V G a,w e)=∑ e∈@SimpleGraph.edgeFinset V G b,w e := by
    cases Subsingleton.elim a b
    rfl
  exact hh _ _

/-- The full host weight is its deterministic tree plus its disjoint original
non-seed candidate identities. -/
theorem host_weight_eq_tree_add_candidates {G T : SimpleGraph V}
    {seed U : Finset (Sym2 V)} (w : Sym2 V → ℝ)
    (hTseed : ∀ e∈T.edgeSet,e∈seed) (hUG : ∀ e∈U,e∈G.edgeSet)
    (hUseed : ∀ e∈U,e∉seed) :
    totalWeight (T⊔edgeGraph U) w=totalWeight T w+∑ e∈U,w e := by
  have hE : (T⊔edgeGraph U).edgeFinset=T.edgeFinset∪U := by
    ext e
    simp only [mem_edgeFinset,edgeSet_sup,Set.mem_union,mem_edgeGraph,mem_union]
    constructor
    · rintro (he | ⟨he,_⟩)
      · exact Or.inl he
      · exact Or.inr he
    · rintro (he | he)
      · exact Or.inl he
      · exact Or.inr ⟨he,G.not_isDiag_of_mem_edgeSet (hUG e he)⟩
  have hd : Disjoint T.edgeFinset U := disjoint_left.mpr
    (fun e heT heU => hUseed e heU (hTseed e (mem_edgeFinset.mp heT)))
  calc
    _ = ∑ e∈(T⊔edgeGraph U).edgeFinset,w e := weight_eq_edge_sum _ w _
    _ = ∑ e∈T.edgeFinset∪U,w e := by rw [hE]
    _ = (∑ e∈T.edgeFinset,w e)+∑ e∈U,w e := sum_union hd
    _ = _ := by rw [weight_eq_edge_sum T w _]

/-- Literal corrected Lemma 27: a real pruned graph and minimum tree are
constructed for each Bernoulli outcome. Their actual finite expected weight
is at least the full host weight divided by 4f, minus the seed-tree weight.
The stronger surviving-candidate inequality also holds for each outcome. -/
theorem exists_sampled_girth_family {G T : SimpleGraph V} {seed U : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {t : ℝ} {f : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w t f B) (hT : T.IsTree) (hTG : T ≤ G)
    (hTseed : ∀ e∈T.edgeSet,e∈seed) (hUG : ∀ e∈U,e∈G.edgeSet)
    (hUseed : ∀ e∈U,e∉seed)
    (hhost : ∀ e∈U, Disjoint (B e) T.edgeFinset)
    (hw : ∀ e∈G.edgeSet,0≤w e) (hf : 2≤f) (ht : 0≤t+1) :
    ∃ R K : Finset (Sym2 V) → SimpleGraph V,
      (∀ S,S⊆U → R S ≤ G ∧ IsMinimumSpanningTree (R S) (K S) w ∧
        totalWeight (K S) w≤totalWeight T w ∧ WeightedGirthAbove (R S) w (t+1) ∧
        (∑ e∈surviving U B S,w e)≤totalWeight (R S) w) ∧
      totalWeight (T⊔edgeGraph U) w/(4*(f:ℝ))-totalWeight T w ≤
        ∑ S∈U.powerset,mass U (1/(f:ℝ)) S*totalWeight (R S) w := by
  classical
  have hex (S : Finset (Sym2 V)) :
      ∃ R K : SimpleGraph V,S⊆U → R ≤ G ∧ IsMinimumSpanningTree R K w ∧
        totalWeight K w≤totalWeight T w ∧ WeightedGirthAbove R w (t+1) ∧
        (∑ e∈surviving U B S,w e)≤totalWeight R w := by
    by_cases hSU : S⊆U
    · obtain ⟨R,K,hprop⟩ := exists_girth_host_of_sample hB hT hTG hTseed hUG hUseed
        hhost S hSU hw ht
      exact ⟨R,K,fun _ => hprop⟩
    · exact ⟨T,T,fun hh => (hSU hh).elim⟩
  choose R K hRK using hex
  refine ⟨R,K,hRK,?_⟩
  have hfR : (2:ℝ)≤f := by exact_mod_cast hf
  have hp1 : 1/(f:ℝ)≤1 := (div_le_one (by linarith)).mpr (by linarith)
  have hExpected := corrected_expected_weight U B w (fun e he => hw e (hUG e he))
    f hf (fun e _ => hB.capped e) (fun e _ => hB.no_self e)
  have hExpectedR : (∑ e∈U,w e)/(4*(f:ℝ))≤
      ∑ S∈U.powerset,mass U (1/(f:ℝ)) S*totalWeight (R S) w := by
    apply hExpected.trans
    apply sum_le_sum
    intro S hS
    exact mul_le_mul_of_nonneg_left (hRK S (mem_powerset.mp hS)).2.2.2.2
      (mass_nonneg _ _ (by positivity) hp1)
  have hT0 : 0≤totalWeight T w := by
    rw [weight_eq_edge_sum T w _]
    exact sum_nonneg (fun e he => hw e (edgeSet_mono hTG (mem_edgeFinset.mp he)))
  have hbaseline : totalWeight T w/(4*(f:ℝ))≤totalWeight T w :=
    div_le_self hT0 (by linarith)
  rw [host_weight_eq_tree_add_candidates w hTseed hUG hUseed,add_div]
  linarith

end LightEFTSpanners.CorrectedDeterministicSampling
