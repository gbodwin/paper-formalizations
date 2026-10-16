import LightEFTSpanners.NativeGirthSimplicity
import LightEFTSpanners.NonnegativeExtremal

namespace LightEFTSpanners.NativeWeighted
open Finset SimpleGraph
open scoped NNReal
variable {V E W : Type*}
attribute [local instance] Classical.propDecidable

/-- Exact original-ID model on an embedded host vertex domain. -/
structure NativeSimpleModel (G : Graph V E) (R : Finset E) (j : W ↪ G.vertexSet) where
  pair : E → Sym2 W
  link : ∀ e ∈ R, ∀ u v, pair e = s(u,v) ↔ G.IsLink e (j u).val (j v).val
  nonDiag : ∀ e ∈ R, ¬ (pair e).IsDiag
  injective : Set.InjOn pair (R : Set E)

/-- Construct the model only after actual native simplicity is established.
Every retained ID has endpoints in the host; no extra IDs are invented. -/
noncomputable def nativeSimpleModel [Nonempty W] (G : Graph V E) (R : Finset E)
    (j : W ↪ G.vertexSet) (hs : (G.restrict (R : Set E)).Simple)
    (hends : ∀ e ∈ R, ∃ u v, G.IsLink e (j u).val (j v).val) : NativeSimpleModel G R j := by
  classical
  let pair : E → Sym2 W := fun e => if he : e ∈ R then
    s((hends e he).choose,((hends e he).choose_spec).choose)
    else s(Classical.choice inferInstance,Classical.choice inferInstance)
  have hlink : ∀ e ∈ R, ∀ u v, pair e = s(u,v) ↔ G.IsLink e (j u).val (j v).val := by
    intro e he u v
    let a := (hends e he).choose
    let b := ((hends e he).choose_spec).choose
    have hab : G.IsLink e (j a).val (j b).val := ((hends e he).choose_spec).choose_spec
    have hp : pair e = s(a,b) := by simp only [pair,he,dite_true]; rfl
    rw [hp]
    constructor
    · intro h
      rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hab
      · exact hab.symm
    · intro huv
      rcases hab.eq_and_eq_or_eq_and_eq huv with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact Sym2.eq_iff.mpr (Or.inl ⟨j.injective (Subtype.ext ha),j.injective (Subtype.ext hb)⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨j.injective (Subtype.ext ha),j.injective (Subtype.ext hb)⟩)
  let : (G.restrict (R : Set E)).Simple := hs
  refine ⟨pair,hlink,?_,?_⟩
  · intro e he
    obtain ⟨u,v,hl⟩ := hends e he
    have hp := (hlink e he u v).mpr hl
    rw [hp]
    have hne : u ≠ v := by
      intro h
      subst v
      exact hs.not_isLoopAt e (j u).val ⟨he,hl⟩
    simpa using hne
  · intro e he d hd hpair
    obtain ⟨u,v,hl⟩ := hends e he
    have hdl := (hlink d hd u v).mp (hpair.symm.trans ((hlink e he u v).mpr hl))
    exact (show (G.restrict (R : Set E)).IsLink e (j u).val (j v).val from ⟨he,hl⟩).eq ⟨hd,hdl⟩

namespace NativeSimpleModel
variable {G : Graph V E} {R : Finset E} {j : W ↪ G.vertexSet}
noncomputable def project (M : NativeSimpleModel G R j) (K : Finset E) : SimpleGraph W :=
  LightSpanners.edgeGraph (K.image M.pair)

noncomputable def weights (M : NativeSimpleModel G R j) (w : E → ℝ≥0) (s : Sym2 W) : ℝ :=
  if h : ∃ e ∈ R, M.pair e = s then (w h.choose : ℝ) else 0

theorem weights_pair (M : NativeSimpleModel G R j) (w : E → ℝ≥0) (e : E) (he : e ∈ R) :
    M.weights w (M.pair e) = w e := by
  have hex : ∃ d ∈ R, M.pair d = M.pair e := ⟨e,he,rfl⟩
  simp only [weights,hex,dite_true]
  have hd := M.injective hex.choose_spec.1 he hex.choose_spec.2
  rw [hd]

theorem weights_nonneg (M : NativeSimpleModel G R j) (w : E → ℝ≥0) (s : Sym2 W) :
    0 ≤ M.weights w s := by
  unfold weights
  split
  · exact NNReal.coe_nonneg _
  · exact le_refl _

theorem project_adj (M : NativeSimpleModel G R j) {K : Finset E} (hK : K ⊆ R) (u v : W) :
    (M.project K).Adj u v ↔ u ≠ v ∧ ∃ e ∈ K, G.IsLink e (j u).val (j v).val := by
  constructor
  · intro h
    have hm := (LightSpanners.mem_edgeGraph _ _).mp ((mem_edgeSet _).mpr h)
    obtain ⟨e,he,hp⟩ := mem_image.mp hm.1
    exact ⟨h.ne,e,he,(M.link e (hK he) u v).mp hp⟩
  · rintro ⟨_,e,he,hl⟩
    have hp := (M.link e (hK he) u v).mpr hl
    apply (mem_edgeSet _).mp
    exact (LightSpanners.mem_edgeGraph _ _).mpr ⟨mem_image.mpr ⟨e,he,hp⟩,hp ▸ M.nonDiag e (hK he)⟩

theorem project_mono (M : NativeSimpleModel G R j) {K L : Finset E} (h : K ⊆ L) :
    M.project K ≤ M.project L := LightSpanners.edgeGraph_mono (image_subset_image h)

theorem project_edgeFinset [Fintype W] (M : NativeSimpleModel G R j)
    {K : Finset E} (hK : K ⊆ R) : (M.project K).edgeFinset = K.image M.pair := by
  ext s
  rw [mem_edgeFinset,project,LightSpanners.mem_edgeGraph]
  constructor
  · exact And.left
  · intro h
    obtain ⟨e,he,rfl⟩ := mem_image.mp h
    exact ⟨mem_image.mpr ⟨e,he,rfl⟩,M.nonDiag e (hK he)⟩

/-- Literal equality of the actual-ID sum with the projected edge-weight sum. -/
theorem totalWeight_project [Fintype W] (M : NativeSimpleModel G R j) (w : E → ℝ≥0)
    {K : Finset E} (hK : K ⊆ R) :
    LightSpanners.totalWeight (M.project K) (M.weights w) = (totalWeight w K : ℝ) := by
  unfold LightSpanners.totalWeight
  rw [M.project_edgeFinset hK,Finset.sum_image]
  · simp only [totalWeight,NNReal.coe_sum]
    exact sum_congr rfl (fun e he => M.weights_pair w e (hK he))
  · intro e he d hd h
    exact M.injective (hK he) (hK hd) h

/-- Lift every simple walk using its actual original IDs, preserving the full
edge list after applying the injective pair map, and the exact weight. -/
theorem lift_walk (M : NativeSimpleModel G R j) (w : E → ℝ≥0) {u v : W}
    (p : (M.project R).Walk u v) :
    ∃ r : Walk G R ∅ (j u) (j v), r.edgeList.map M.pair = p.edges ∧
      (r.weight w : ℝ) = LightSpanners.walkWeight (M.weights w) p := by
  induction p with
  | nil => exact ⟨.nil _,rfl,by simp [Walk.weight]⟩
  | @cons u v z huv p ih =>
    obtain ⟨_,e,he,hl⟩ := (M.project_adj Subset.rfl u v).mp huv
    obtain ⟨r,hr,hw⟩ := ih
    refine ⟨.cons e hl he (by simp) r,?_,?_⟩
    · simp [Walk.edgeList,hr,(M.link e he u v).mpr hl]
    · simp only [Walk.weight,NNReal.coe_add,LightSpanners.walkWeight_cons,hw]
      rw [← (M.link e he u v).mpr hl,M.weights_pair w e he]

/-- Native full girth transports only after the original-ID model is proved. -/
theorem girth_project (M : NativeSimpleModel G R j) {w : E → ℝ≥0} {b : ℝ≥0}
    (hg : NativeWeightedGirthAbove G R w b) :
    LightSpanners.WeightedGirthAbove (M.project R) (M.weights w) (b : ℝ) := by
  intro u p hp s hs
  obtain ⟨r,hr,hw⟩ := M.lift_walk w p
  have hn : r.edgeList.Nodup := List.Nodup.of_map (hr.symm ▸ hp.isTrail.edges_nodup)
  have hm : s ∈ r.edgeList.map M.pair := hr.symm ▸ hs
  obtain ⟨e,he,hes⟩ := List.mem_map.mp hm
  have h := hg (j u) r hn e he
  have hreal : (b:ℝ)*(w e:ℝ) < (r.weight w:ℝ) := by exact_mod_cast h
  rw [hw] at hreal
  rw [← hes,M.weights_pair w e (r.edgeList_selected e he)]
  exact hreal

/-- Nonnegative native extremal estimate with exact original-ID weights. -/
theorem extremal_bound [Fintype W] (M : NativeSimpleModel G R j) (w : E → ℝ≥0)
    (K : Finset E) (hK : K ⊆ R) (hT : (M.project K).IsTree) (b : ℝ≥0)
    (hb : 2 < b) (hg : NativeWeightedGirthAbove G R w b) (n : ℕ)
    (hcard : Fintype.card W ≤ n) :
    (totalWeight w R : ℝ) ≤ extremalLightness n (b:ℝ) * (totalWeight w K : ℝ) := by
  have h := nonnegative_extremal_tree_bound (M.project_mono hK) hT
    (fun e _ => M.weights_nonneg w e) (M.girth_project hg) (by exact_mod_cast hb) hcard
  rwa [M.totalWeight_project w Subset.rfl,M.totalWeight_project w hK] at h

end NativeSimpleModel
end LightEFTSpanners.NativeWeighted
