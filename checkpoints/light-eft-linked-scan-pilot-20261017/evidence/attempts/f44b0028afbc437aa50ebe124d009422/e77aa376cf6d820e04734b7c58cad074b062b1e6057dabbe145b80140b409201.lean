import LightEFTSpanners.ExactOrderSubdivision
import LightEFTSpanners.StretchParameters

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

/-- Actual n-vertex positive-weight simple graphs of weighted girth greater
than g, normalized by an actual MST. Zero supplies the explicit n<2 boundary. -/
def lightnessSpectrum (n : ℕ) (g : ℝ) : Set ℝ :=
  {x | x=0 ∨ ∃ G T : SimpleGraph (Fin n), ∃ w : Sym2 (Fin n) → ℝ,
    2≤n ∧ IsMinimumSpanningTree G T w ∧ (∀ e∈G.edgeSet,0<w e) ∧
    WeightedGirthAbove G w g ∧ x=lightness G T w}

/-- The extremal lightness is a genuine supremum over actual graphs. Bounds
below use g>2, where this real-valued supremum is proved finite. -/
noncomputable def extremalLightness (n : ℕ) (g : ℝ) : ℝ := sSup (lightnessSpectrum n g)

 theorem lightnessSpectrum_bddAbove (n : ℕ) {g : ℝ} (hg : 2<g) :
    BddAbove (lightnessSpectrum n g) := by
  refine ⟨8+2048/(g-2)*(n:ℝ),?_⟩
  intro x hx
  rcases hx with rfl | ⟨G,T,w,_,hT,hw,hG,rfl⟩
  · positivity
  · have heps : 0<g-2 := by linarith
    have ht : (1+(g-2))*(2*(1:ℝ)-1)+1=g := by ring
    have hG' : WeightedGirthAbove G w ((1+(g-2))*(2*(1:ℝ)-1)+1) := by rwa [ht]
    have hh := corrected_threshold_lightness hT hw heps (show 0<1 by omega) (by simpa using hG')
    simpa using hh

 theorem extremalLightness_nonneg (n : ℕ) {g : ℝ} (hg : 2<g) :
    0≤extremalLightness n g :=
  le_csSup (lightnessSpectrum_bddAbove n hg) (Or.inl rfl)

/-- Canonical finite reindexing does not assume monotonicity in graph order. -/
theorem lightness_mem_spectrum {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ} {g : ℝ} {n : ℕ}
    (hT : IsMinimumSpanningTree G T w) (hw : ∀ e∈G.edgeSet,0<w e)
    (hG : WeightedGirthAbove G w g) (hn : 2≤n) (hcard : Fintype.card V=n) :
    lightness G T w ∈ lightnessSpectrum n g := by
  classical
  let e : Fin n ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  refine Or.inr ⟨G.comap e,T.comap e,fun d => w (Sym2.map e d),hn,
    minimumTree_comap_equiv e hT,?_,girth_comap_equiv e hG,?_⟩
  · intro d hd
    exact hw _ ((mem_comap_edgeSet e.toEmbedding G d).mp hd)
  · exact (lightness_comap_equiv e G T w).symm

/-- Exact-order monotonicity is witnessed by real positive edge subdivision,
not by adding isolated vertices or replacing n with a monotone envelope. -/
theorem lightnessSpectrum_mono_succ {n : ℕ} {g : ℝ} (hg : 0≤g) :
    lightnessSpectrum n g ⊆ lightnessSpectrum (n+1) g := by
  intro x hx
  rcases hx with rfl | ⟨G,T,w,hn,hT,hw,hG,rfl⟩
  · exact Or.inl rfl
  · obtain ⟨G',T',w',hT',hw',hg',heq⟩ := exists_order_succ_same_lightness hT hw hG hg
      (by simpa using hn)
    rw [← heq]
    exact lightness_mem_spectrum hT' hw' hg' (by omega) (by simp)

 theorem lightnessSpectrum_mono {m n : ℕ} {g : ℝ} (hmn : m≤n) (hg : 0≤g) :
    lightnessSpectrum m g ⊆ lightnessSpectrum n g := by
  induction n,hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih => exact ih.trans (lightnessSpectrum_mono_succ hg)

 theorem extremalLightness_mono {m n : ℕ} {g : ℝ} (hmn : m≤n) (hg : 2<g) :
    extremalLightness m g≤extremalLightness n g := by
  apply csSup_le (show (lightnessSpectrum m g).Nonempty from ⟨0,Or.inl rfl⟩)
  intro x hx
  exact le_csSup (lightnessSpectrum_bddAbove n hg)
    (lightnessSpectrum_mono hmn (by linarith) hx)

/-- The actual graph bound, with its original vertex count and exact threshold. -/
theorem lightness_le_extremal {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ} {g : ℝ} {n : ℕ}
    (hT : IsMinimumSpanningTree G T w) (hw : ∀ e∈G.edgeSet,0<w e)
    (hG : WeightedGirthAbove G w g) (hg : 2<g)
    (hn : 2≤Fintype.card V) (hcard : Fintype.card V≤n) :
    lightness G T w ≤ extremalLightness n g :=
  le_csSup (lightnessSpectrum_bddAbove n hg)
    (lightnessSpectrum_mono hcard (by linarith) (lightness_mem_spectrum hT hw hG hn rfl))
end LightEFTSpanners
