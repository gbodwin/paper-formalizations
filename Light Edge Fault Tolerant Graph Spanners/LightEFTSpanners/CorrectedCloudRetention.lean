import LightEFTSpanners.CorrectedCloudProjection

/-! Every original core edge forces at least f+1 distinct retained cross
edges. The fault set consists of the actual retained edges in that bundle. -/
namespace LightEFTSpanners.CorrectedCloud
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

noncomputable def retainedBundle {m p : ℕ}
    (H : SimpleGraph (Fin m × Fin p)) (u v : Fin m) :
    Finset (Sym2 (Fin m × Fin p)) :=
  H.edgeFinset.filter (fun e => Sym2.map Prod.fst e = s(u,v))

@[simp] theorem mem_retainedBundle {m p : ℕ}
    (H : SimpleGraph (Fin m × Fin p)) (u v : Fin m)
    (e : Sym2 (Fin m × Fin p)) :
    e ∈ retainedBundle H u v ↔ e ∈ H.edgeSet ∧ Sym2.map Prod.fst e = s(u,v) := by
  simp [retainedBundle]

theorem exists_unfailed_cross_edge {m p : ℕ} {u v : Fin m} (hne : u≠v)
    (F : Finset (Sym2 (Fin m × Fin p))) (hF : F.card < p) :
    ∃ i j : Fin p, s((u,i),(v,j)) ∉ F := by
  classical
  have hp : 0<p := lt_of_le_of_lt (Nat.zero_le _) hF
  let i : Fin p := ⟨0,hp⟩
  by_contra! h
  have hinj : Function.Injective
      (fun j : Fin p => (s((u,i),(v,j)) : Sym2 (Fin m × Fin p))) := by
    intro a b he
    rcases Sym2.eq_iff.mp he with he | he
    · exact congrArg Prod.snd he.2
    · exact (hne (congrArg Prod.fst he.1)).elim
  have hsub : univ.image
      (fun j : Fin p => (s((u,i),(v,j)) : Sym2 (Fin m × Fin p))) ⊆ F := by
    intro e he
    obtain ⟨j,_,rfl⟩ := mem_image.mp he
    exact h i j
  have hc := card_le_card hsub
  rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin] at hc
  omega

/-- Literal all-fault spanner semantics force f+1 copies of every core edge.
This holds for arbitrary real stretch and arbitrary nonnegative internal
weights, so it applies directly to the corrected positive clique weights. -/
theorem retainedBundle_card_gt {m p f : ℕ} {G : SimpleGraph (Fin m)}
    {H : SimpleGraph (Fin m × Fin p)}
    (w : Sym2 (Fin m) → ℝ) (W : Sym2 (Fin m × Fin p) → ℝ) (t : ℝ)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (hW : ∀ e ∈ (graph G p).edgeSet, 0 ≤ W e)
    (hcross : ∀ a b : Fin m × Fin p, G.Adj a.1 b.1 →
      W s(a,b) = w s(a.1,b.1))
    (hg : WeightedGirthAbove G w (t+1))
    (hsp : IsEFTSpanner (graph G p) H W t f) (hfp : f < p)
    {u v : Fin m} (huv : G.Adj u v) :
    f < (retainedBundle H u v).card := by
  classical
  by_contra! hcard
  let F := retainedBundle H u v
  have hF : F.card ≤ f := hcard
  obtain ⟨i,j,hij⟩ := exists_unfailed_cross_edge huv.ne F (hF.trans_lt hfp)
  have hinput : (afterFaults (graph G p) F).Adj (u,i) (v,j) :=
    deleteEdges_adj.mpr ⟨Or.inr huv,hij⟩
  obtain ⟨r,hr⟩ := (hsp.2 F hF).2 (u,i) (v,j) hinput.toWalk
  have hcrossij := hcross (u,i) (v,j) huv
  have hr' : walkWeight W r ≤ t * w s(u,v) := by
    simpa only [SimpleGraph.Adj.toWalk, walkWeight_cons, walkWeight_nil,
      add_zero, hcrossij] using hr
  have hsub : afterFaults H F ≤ graph G p := (deleteEdges_le _).trans hsp.1
  have havoid : ∀ e ∈ r.edges, Sym2.map Prod.fst e ≠ s(u,v) := by
    intro e he hproj
    have hed := (mem_afterFaults H F e).mp (r.edges_subset_edgeSet he)
    exact hed.2 ((mem_retainedBundle H u v e).mpr ⟨hed.1,hproj⟩)
  obtain ⟨q,hq⟩ := exists_projected_walk hsub w W
    (fun e he => hW e (edgeSet_mono hsub he)) hcross s(u,v) r havoid
  have hlong := deleted_edge_walk_too_heavy hw hg huv q
  linarith

end LightEFTSpanners.CorrectedCloud
