import VFTSpanners.ShortestPaths

namespace VFTSpanners
open SimpleGraph Finset
open scoped ENNReal
variable {V : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- An edge-fault-avoiding walk uses no failed edge, including at its endpoints. -/
def EdgeAvoids (F : Finset (Sym2 V)) {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : Prop := ∀ e ∈ p.edges, e ∉ F

/-- Greedy coverage for edge faults. Only a surviving queried edge needs replacement. -/
def EdgeCovered (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (k f : ℕ) (e : Sym2 V) : Prop :=
  ∀ u v, s(u,v) = e → ∀ F : Finset (Sym2 V), F.card ≤ f → e ∉ F →
    ∃ p : H.Walk u v, EdgeAvoids F p ∧ walkWeight w p ≤ (k : ℝ)*w e

/-- Weighted EFT stretch, quantified over arbitrary sets of at most `f` edges. -/
def IsEFTSpanner (G H : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ) : Prop :=
  H ≤ G ∧ ∀ F : Finset (Sym2 V), F.card ≤ f → ∀ u v (p : G.Walk u v),
    EdgeAvoids F p → ∃ q : H.Walk u v,
      EdgeAvoids F q ∧ walkWeight w q ≤ (k : ℝ)*walkWeight w p

omit [DecidableEq V] in
theorem edgeCovered_mono {H K : SimpleGraph V} (hHK : H ≤ K)
    {w : Sym2 V → ℝ} {k f : ℕ} {e : Sym2 V} (h : EdgeCovered H w k f e) :
    EdgeCovered K w k f e := by
  intro u v he F hF heF
  obtain ⟨p,hp,hw⟩ := h u v he F hF heF
  exact ⟨p.mapLe hHK, by simpa [EdgeAvoids] using hp, by simpa using hw⟩

omit [DecidableEq V] in
theorem edgeCovered_of_mem {H : SimpleGraph V} {w : Sym2 V → ℝ}
    {k f : ℕ} (hk : 1 ≤ k) (hw : ∀ e, 0 ≤ w e)
    {e : Sym2 V} (he : e ∈ H.edgeSet) : EdgeCovered H w k f e := by
  intro u v huv F hF heF
  have hadj : H.Adj u v := (mem_edgeSet H).mp (huv ▸ he)
  refine ⟨hadj.toWalk, ?_, ?_⟩
  · simpa [EdgeAvoids, SimpleGraph.Adj.toWalk, huv] using heF
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    simp only [SimpleGraph.Adj.toWalk, walkWeight_cons, walkWeight_nil, add_zero, huv]
    nlinarith [hw e]

omit [DecidableEq V] in
theorem edgeCovered_edges_spanner {G H : SimpleGraph V}
    {w : Sym2 V → ℝ} {k f : ℕ} (hHG : H ≤ G)
    (h : ∀ e ∈ G.edgeSet, EdgeCovered H w k f e) : IsEFTSpanner G H w k f := by
  refine ⟨hHG, ?_⟩
  intro F hF u v p hp
  induction p with
  | nil => exact ⟨.nil, hp, by simp⟩
  | @cons u v z huv p ih =>
    have heF : s(u,v) ∉ F := hp _ (by simp)
    obtain ⟨q,hq,hqw⟩ := h s(u,v) ((mem_edgeSet G).mpr huv) u v rfl F hF heF
    obtain ⟨t,ht,htw⟩ := ih (fun e he => hp e (by simp [he]))
    refine ⟨q.append t, ?_, ?_⟩
    · intro e he
      simp only [Walk.edges_append, List.mem_append] at he
      exact he.elim (hq e) (ht e)
    · simp only [walkWeight_append, walkWeight_cons]
      nlinarith

omit [DecidableEq V] in
/-- A different non-loop edge has an endpoint outside a queried edge. -/
theorem exists_endpoint_outside {d e : Sym2 V} (hd : ¬ d.IsDiag) (hne : d ≠ e) :
    ∃ x, x ∈ d ∧ x ∉ e := by
  induction d using Sym2.inductionOn with
  | _ a b =>
    have hab : a ≠ b := by simpa using hd
    by_contra hn
    push Not at hn
    have ha : a ∈ e := hn a (by simp)
    have hb : b ∈ e := hn b (by simp)
    exact hne ((Sym2.mem_and_mem_iff hab).mp ⟨ha,hb⟩).symm

/-- Replace each failed edge by one endpoint outside the queried edge.
This is the precise reduction allowing the VFT blocking-set proof to cover EFT. -/
theorem covered_implies_edgeCovered {H : SimpleGraph V} {w : Sym2 V → ℝ}
    {k f : ℕ} {e : Sym2 V} (hc : Covered H w k f e) : EdgeCovered H w k f e := by
  classical
  intro u v huv F hF heF
  let D := F.filter (fun d => ¬ d.IsDiag)
  have hx (d : {d // d ∈ D}) : ∃ x, x ∈ d.val ∧ x ∉ e :=
    exists_endpoint_outside (mem_filter.mp d.property).2
      (fun h => heF (h ▸ (mem_filter.mp d.property).1))
  let x (d : {d // d ∈ D}) : V := Classical.choose (hx d)
  let S : Finset V := D.attach.image x
  have hS : S.card ≤ f := calc
    S.card ≤ D.attach.card := card_image_le
    _ = D.card := card_attach
    _ ≤ F.card := card_filter_le _ _
    _ ≤ f := hF
  have hout : ∀ z ∈ S, z ∉ e := by
    intro z hz
    obtain ⟨d,_,rfl⟩ := mem_image.mp hz
    exact (Classical.choose_spec (hx d)).2
  have hu : u ∉ S := fun h => hout u h (by rw [← huv]; simp)
  have hv : v ∉ S := fun h => hout v h (by rw [← huv]; simp)
  obtain ⟨p,hp,hw⟩ := hc u v huv S hS hu hv
  refine ⟨p,?_,hw⟩
  intro d hd hdF
  have hdD : d ∈ D := mem_filter.mpr ⟨hdF,H.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet hd)⟩
  let d' : {d // d ∈ D} := ⟨d,hdD⟩
  have hxS : x d' ∈ S := mem_image.mpr ⟨d',mem_attach _ _,rfl⟩
  have hxP : x d' ∈ p.support := Walk.mem_support_iff_exists_mem_edges.mpr
    (Or.inr ⟨d,hd,(Classical.choose_spec (hx d')).1⟩)
  exact hp _ hxP hxS

/-- Extended nonnegative weighted distance after deleting failed edges. -/
noncomputable def edgeFaultDistance (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (u v : V) : ℝ≥0∞ :=
  ⨅ p : {p : G.Walk u v // EdgeAvoids F p}, ENNReal.ofReal (walkWeight w p.val)

omit [DecidableEq V] in
theorem IsEFTSpanner.distance_le {G H : SimpleGraph V} {w : Sym2 V → ℝ}
    {k f : ℕ} (h : IsEFTSpanner G H w k f) (hk : 1 ≤ k)
    (F : Finset (Sym2 V)) (hF : F.card ≤ f) (u v : V) :
    edgeFaultDistance H w F u v ≤ (k : ℝ≥0∞) * edgeFaultDistance G w F u v := by
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by simpa using (by omega : k ≠ 0)
  unfold edgeFaultDistance
  rw [ENNReal.mul_iInf_of_ne hk0 (by simp)]
  apply le_iInf
  intro p
  obtain ⟨q,hq,hweight⟩ := h.2 F hF u v p.val p.property
  calc
    _ ≤ ENNReal.ofReal (walkWeight w q) := iInf_le (fun p : {p : H.Walk u v // EdgeAvoids F p} =>
      ENNReal.ofReal (walkWeight w p.val)) ⟨q,hq⟩
    _ ≤ ENNReal.ofReal ((k : ℝ)*walkWeight w p.val) := ENNReal.ofReal_le_ofReal hweight
    _ = (k : ℝ≥0∞)*ENNReal.ofReal (walkWeight w p.val) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simp

end VFTSpanners
