import LightEFTSpanners.CorrectedCloudConstruction
import LightSpanners.Weight
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Tactic

/-! Explicit weight accounting for the corrected clique-cloud construction.
The upper bound uses a finite encoding of every certificate edge. Internal
edges are charged at most `m*p^2` times and each tree edge exactly `2*p` times. -/
namespace LightEFTSpanners.CorrectedCloud
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

/-- Internal cloud edges have weight δ; cross edges retain their core weight. -/
noncomputable def edgeWeight {m p : ℕ} (w : Sym2 (Fin m) → ℝ) (δ : ℝ)
    (e : Sym2 (Fin m × Fin p)) : ℝ :=
  if (Sym2.map Prod.fst e).IsDiag then δ else w (Sym2.map Prod.fst e)

@[simp] theorem edgeWeight_pair {m p : ℕ} (w : Sym2 (Fin m) → ℝ) (δ : ℝ)
    (a b : Fin m × Fin p) :
    edgeWeight w δ s(a,b) = if a.1=b.1 then δ else w s(a.1,b.1) := by
  simp only [edgeWeight,Sym2.map_mk,Sym2.mk_isDiag_iff]

@[simp] theorem edgeWeight_internal {m p : ℕ} (w : Sym2 (Fin m) → ℝ) (δ : ℝ)
    (u : Fin m) (i j : Fin p) : edgeWeight w δ s((u,i),(u,j))=δ := by simp

@[simp] theorem edgeWeight_cross {m p : ℕ} (w : Sym2 (Fin m) → ℝ) (δ : ℝ)
    {u v : Fin m} (h : u≠v) (i j : Fin p) :
    edgeWeight w δ s((u,i),(v,j))=w s(u,v) := by simp [h]

theorem edgeWeight_pos {m p : ℕ} {G : SimpleGraph (Fin m)}
    {w : Sym2 (Fin m) → ℝ} {δ : ℝ} (hw : ∀ e∈G.edgeSet,0<w e)
    (hδ : 0<δ) {e : Sym2 (Fin m × Fin p)} (he : e∈(graph G p).edgeSet) :
    0<edgeWeight w δ e := by
  rcases e with ⟨a,b⟩
  have hab := (mem_edgeSet _).mp he
  rw [edgeWeight_pair]
  split_ifs with h
  · exact hδ
  · exact hw _ ((mem_edgeSet G).mpr (hab.resolve_left (fun hh => h hh.1)))

theorem edgeWeight_nonneg {m p : ℕ} {G : SimpleGraph (Fin m)}
    {w : Sym2 (Fin m) → ℝ} {δ : ℝ} (hw : ∀ e∈G.edgeSet,0≤w e)
    (hδ : 0≤δ) {e : Sym2 (Fin m × Fin p)} (he : e∈(graph G p).edgeSet) :
    0≤edgeWeight w δ e := by
  rcases e with ⟨a,b⟩
  have hab := (mem_edgeSet _).mp he
  rw [edgeWeight_pair]
  split_ifs with h
  · exact hδ
  · exact hw _ ((mem_edgeSet G).mpr (hab.resolve_left (fun hh => h hh.1)))

theorem pair_inf_sup {m : ℕ} (e : Sym2 (Fin m)) : s(e.inf,e.sup)=e := by
  cases e using Sym2.ind with
  | _ u v =>
    rcases le_total u v with h | h <;> simp [h,Sym2.eq_swap]

theorem coreEdge_inf_lt_sup {m : ℕ} {T : SimpleGraph (Fin m)} (e : T.edgeSet) :
    (e:Sym2 (Fin m)).inf < (e:Sym2 (Fin m)).sup := by
  have h := T.not_isDiag_of_mem_edgeSet e.property
  have hne : (e:Sym2 (Fin m)).inf ≠ (e:Sym2 (Fin m)).sup := by
    intro he
    apply h
    rw [← pair_inf_sup (e:Sym2 (Fin m)),Sym2.mk_isDiag_iff]
    exact he
  exact lt_of_le_of_ne (Sym2.inf_le_sup _) hne

/-- A finite indexing family for all internal edges and both tree matchings. -/
abbrev BudgetIndex {m : ℕ} (T : SimpleGraph (Fin m)) (p : ℕ) :=
  (Fin m × (Fin p × Fin p)) ⊕ (T.edgeSet × (Fin p × Bool))

noncomputable def budgetEdge {m p : ℕ} (T : SimpleGraph (Fin m)) :
    BudgetIndex T p → Sym2 (Fin m × Fin p)
  | Sum.inl (u,i,j) => s((u,i),(u,j))
  | Sum.inr (e,i,b) =>
    if b then s(((e:Sym2 (Fin m)).inf,i),((e:Sym2 (Fin m)).sup,finRotate p i))
    else s(((e:Sym2 (Fin m)).inf,i),((e:Sym2 (Fin m)).sup,i))

theorem budgetEdge_weight_internal {m p : ℕ} (T : SimpleGraph (Fin m))
    (w : Sym2 (Fin m) → ℝ) (δ : ℝ) (u : Fin m) (i j : Fin p) :
    edgeWeight w δ (budgetEdge T (Sum.inl (u,i,j)))=δ := by simp [budgetEdge]

theorem budgetEdge_weight_cross {m p : ℕ} (T : SimpleGraph (Fin m))
    (w : Sym2 (Fin m) → ℝ) (δ : ℝ) (e : T.edgeSet) (i : Fin p) (b : Bool) :
    edgeWeight w δ (budgetEdge T (Sum.inr (e,i,b)))=w e := by
  have hne := (coreEdge_inf_lt_sup e).ne
  cases b <;> simp [budgetEdge,hne,pair_inf_sup]

/-- Every sparse certificate edge is represented by the finite budget family. -/
theorem budgetEdge_cover {m p : ℕ} (T : SimpleGraph (Fin m))
    {e : Sym2 (Fin m × Fin p)} (he : e∈(certificate T p).edgeSet) :
    ∃ x : BudgetIndex T p, budgetEdge T x=e := by
  have identity (u v : Fin m) (huv : T.Adj u v) (i : Fin p) :
      ∃ x : BudgetIndex T p, budgetEdge T x=s((u,i),(v,i)) := by
    let d : T.edgeSet := ⟨s(u,v),(mem_edgeSet T).mpr huv⟩
    refine ⟨Sum.inr (d,i,false),?_⟩
    rcases le_total u v with h | h
    · simp [budgetEdge,d,h]
    · simp [budgetEdge,d,h,Sym2.eq_swap]
  have shift (u v : Fin m) (huv : T.Adj u v) (horder : u<v) (i : Fin p) :
      ∃ x : BudgetIndex T p, budgetEdge T x=s((u,i),(v,finRotate p i)) := by
    let d : T.edgeSet := ⟨s(u,v),(mem_edgeSet T).mpr huv⟩
    exact ⟨Sum.inr (d,i,true),by simp [budgetEdge,d,horder.le]⟩
  rcases e with ⟨⟨u,i⟩,⟨v,j⟩⟩
  rcases (mem_edgeSet _).mp he with h | ⟨huv,hmatch⟩
  · rcases h with ⟨rfl,_⟩
    exact ⟨Sum.inl (u,i,j),rfl⟩
  · rcases hmatch with hij | ⟨horder,hij⟩ | ⟨horder,hij⟩
    · cases hij
      exact identity u v huv i
    · cases hij
      exact shift u v huv horder i
    · cases hij
      obtain ⟨x,hx⟩ := shift v u huv.symm horder j
      exact ⟨x,hx.trans (Sym2.eq_swap ..)⟩

/-- The finite representation has exactly the advertised weighted budget. -/
theorem sum_budgetEdge_weight {m p : ℕ} (T : SimpleGraph (Fin m))
    (w : Sym2 (Fin m) → ℝ) (δ : ℝ) :
    (∑ x : BudgetIndex T p, edgeWeight w δ (budgetEdge T x)) =
      (m:ℝ)*(p:ℝ)^2*δ + 2*(p:ℝ)*totalWeight T w := by
  classical
  simp only [BudgetIndex,Fintype.sum_sum_type,Fintype.sum_prod_type,
    budgetEdge_weight_internal,budgetEdge_weight_cross]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Fintype.card_bool]
  have hs : (∑ e : T.edgeSet, w e)=totalWeight T w := by
    unfold totalWeight
    apply Finset.sum_bij (fun (e:T.edgeSet) _ => (e:Sym2 (Fin m)))
    · intro e _
      exact mem_edgeFinset.mpr e.property
    · intro a _ b _ h
      exact Subtype.ext h
    · intro e he
      exact ⟨⟨e,mem_edgeFinset.mp he⟩,mem_univ _,rfl⟩
    · intro e _
      rfl
  simp_rw [← Finset.mul_sum]
  rw [hs]
  ring

/-- Certificate weight is bounded without assuming any MST optimality. -/
theorem certificate_weight_le {m p : ℕ} (T : SimpleGraph (Fin m))
    (w : Sym2 (Fin m) → ℝ) (δ : ℝ) (hw : ∀ e∈T.edgeSet,0≤w e)
    (hδ : 0≤δ) :
    totalWeight (certificate T p) (edgeWeight w δ) ≤
      (m:ℝ)*(p:ℝ)^2*δ + 2*(p:ℝ)*totalWeight T w := by
  classical
  let s := (Finset.univ : Finset (BudgetIndex T p)).image (budgetEdge T)
  have hsub : (certificate T p).edgeFinset ⊆ s := by
    intro e he
    obtain ⟨x,hx⟩ := budgetEdge_cover T (mem_edgeFinset.mp he)
    exact mem_image.mpr ⟨x,mem_univ _,hx⟩
  have hnonneg : ∀ e∈s, 0≤edgeWeight w δ e := by
    intro e he
    obtain ⟨x,_,rfl⟩ := mem_image.mp he
    cases x with
    | inl x => rcases x with ⟨u,i,j⟩; simpa only [budgetEdge_weight_internal] using hδ
    | inr x => rcases x with ⟨e,i,b⟩; simpa only [budgetEdge_weight_cross] using hw e e.property
  calc
    _ ≤ ∑ e∈s, edgeWeight w δ e :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e he _ => hnonneg e he)
    _ ≤ ∑ x : BudgetIndex T p, edgeWeight w δ (budgetEdge T x) :=
      Finset.sum_image_le_of_nonneg hnonneg
    _ = _ := sum_budgetEdge_weight T w δ

/-- The common positive weight assigned to internal clique edges. -/
noncomputable def cloudDelta {m : ℕ} (T : SimpleGraph (Fin m))
    (w : Sym2 (Fin m) → ℝ) (p : ℕ) : ℝ :=
  totalWeight T w / ((m:ℝ)*(p:ℝ)^2)

/-- The corrected paper's actual weight function. -/
noncomputable def cloudWeight {m : ℕ} (T : SimpleGraph (Fin m))
    (w : Sym2 (Fin m) → ℝ) (p : ℕ) : Sym2 (Fin m × Fin p) → ℝ :=
  edgeWeight w (cloudDelta T w p)

theorem cloudDelta_pos {m p : ℕ} {T : SimpleGraph (Fin m)}
    {w : Sym2 (Fin m) → ℝ} (hm : 0<m) (hp : 0<p)
    (hT : 0<totalWeight T w) : 0<cloudDelta T w p := by
  unfold cloudDelta
  positivity

theorem cloud_certificate_weight_le {m p : ℕ} (T : SimpleGraph (Fin m))
    (w : Sym2 (Fin m) → ℝ) (hm : 0<m) (hp : 0<p)
    (hw : ∀ e∈T.edgeSet,0≤w e) :
    totalWeight (certificate T p) (cloudWeight T w p) ≤
      (2*(p:ℝ)+1)*totalWeight T w := by
  have hTnn : 0≤totalWeight T w := by
    exact sum_nonneg (fun e he => hw e (mem_edgeFinset.mp he))
  have hδ : 0≤cloudDelta T w p := by unfold cloudDelta; positivity
  have hden : (m:ℝ)*(p:ℝ)^2 ≠ 0 := by positivity
  have hc := certificate_weight_le (p:=p) T w (cloudDelta T w p) hw hδ
  have heq : (m:ℝ)*(p:ℝ)^2*cloudDelta T w p=totalWeight T w := by
    unfold cloudDelta
    exact mul_div_cancel₀ _ hden
  dsimp only [cloudWeight]
  rw [heq] at hc
  nlinarith

/-- Retained copies of one unordered core edge, with actual input edge IDs. -/
noncomputable def crossFiber {m p : ℕ} (H : SimpleGraph (Fin m × Fin p))
    (e : Sym2 (Fin m)) : Finset (Sym2 (Fin m × Fin p)) :=
  H.edgeFinset.filter (fun d => Sym2.map Prod.fst d=e)

@[simp] theorem mem_crossFiber {m p : ℕ} (H : SimpleGraph (Fin m × Fin p))
    (e : Sym2 (Fin m)) (d : Sym2 (Fin m × Fin p)) :
    d∈crossFiber H e ↔ d∈H.edgeSet ∧ Sym2.map Prod.fst d=e := by
  simp [crossFiber]

/-- Sum of the retained copies in one cross bundle. -/
theorem crossFiber_weight {m p : ℕ} {G : SimpleGraph (Fin m)}
    (H : SimpleGraph (Fin m × Fin p)) (w : Sym2 (Fin m) → ℝ) (δ : ℝ)
    {e : Sym2 (Fin m)} (he : e∈G.edgeSet) :
    (∑ d∈crossFiber H e, edgeWeight w δ d) = (crossFiber H e).card * w e := by
  have hdiag := G.not_isDiag_of_mem_edgeSet he
  calc
    _ = ∑ _d∈crossFiber H e, w e := by
      apply sum_congr rfl
      intro d hd
      have hd' := (mem_crossFiber H e d).mp hd
      simp only [edgeWeight,hd'.2,hdiag,ite_false]
    _ = _ := by simp

/-- All retained core bundles occupy disjoint parts of the output edge set. -/
theorem core_bundle_weight_le {m p : ℕ} {G : SimpleGraph (Fin m)}
    {H : SimpleGraph (Fin m × Fin p)} (hHG : H≤graph G p)
    (w : Sym2 (Fin m) → ℝ) (δ : ℝ) (hw : ∀ e∈G.edgeSet,0≤w e)
    (hδ : 0≤δ) :
    (∑ e∈G.edgeFinset, (crossFiber H e).card * w e) ≤
      totalWeight H (edgeWeight w δ) := by
  classical
  have hs : (∑ e∈G.edgeFinset, ∑ d∈crossFiber H e,edgeWeight w δ d) =
      ∑ d∈H.edgeFinset.filter (fun d => Sym2.map Prod.fst d∈G.edgeFinset),
        edgeWeight w δ d := by
    exact sum_fiberwise_eq_sum_filter H.edgeFinset G.edgeFinset
      (Sym2.map Prod.fst) (edgeWeight w δ)
  have heq : (∑ e∈G.edgeFinset, (crossFiber H e).card*w e) =
      ∑ e∈G.edgeFinset, ∑ d∈crossFiber H e,edgeWeight w δ d := by
    apply sum_congr rfl
    intro e he
    exact (crossFiber_weight H w δ (mem_edgeFinset.mp he)).symm
  rw [heq,hs]
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro d hd _
  exact edgeWeight_nonneg hw hδ (edgeSet_mono hHG (mem_edgeFinset.mp hd))

/-- A uniform copy-retention count gives the actual output's weight lower bound. -/
theorem retained_weight_lower {m p r : ℕ} {G : SimpleGraph (Fin m)}
    {H : SimpleGraph (Fin m × Fin p)} (hHG : H≤graph G p)
    (w : Sym2 (Fin m) → ℝ) (δ : ℝ) (hw : ∀ e∈G.edgeSet,0≤w e)
    (hδ : 0≤δ) (hret : ∀ e∈G.edgeSet,r≤(crossFiber H e).card) :
    (r:ℝ)*totalWeight G w ≤ totalWeight H (edgeWeight w δ) := by
  calc
    _ = ∑ e∈G.edgeFinset, (r:ℝ)*w e := by rw [totalWeight,mul_sum]
    _ ≤ ∑ e∈G.edgeFinset, (crossFiber H e).card*w e := by
      apply sum_le_sum
      intro e he
      apply mul_le_mul_of_nonneg_right _ (hw e (mem_edgeFinset.mp he))
      exact_mod_cast hret e (mem_edgeFinset.mp he)
    _ ≤ _ := core_bundle_weight_le hHG w δ hw hδ

end LightEFTSpanners.CorrectedCloud
