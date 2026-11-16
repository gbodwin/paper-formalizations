import LightEFTSpanners.CorrectedCloudCycle
import LightEFTSpanners.ConnectivityCuts

/-! Cut counting for the corrected cloud certificate. Every nontrivial cut
contains at least p+1 certificate edges, giving an actual p-fault preserver. -/
namespace LightEFTSpanners.CorrectedCloud
open SimpleGraph Finset
open ConnectivityCuts
attribute [local instance] Classical.propDecidable

noncomputable def cycleCutEdges {m p : ℕ} (u v : Fin m)
    (S : Set (Fin m × Fin p)) : Finset (Sym2 (Fin m × Fin p)) :=
  (edges (matchingCycle p) (cycleEmbedding u v ⁻¹' S)).image
    (Sym2.map (cycleEmbedding u v))

theorem cycleCutEdges_card {m p : ℕ} {u v : Fin m} (huv : u≠v)
    (S : Set (Fin m × Fin p)) :
    (cycleCutEdges u v S).card =
      (edges (matchingCycle p) (cycleEmbedding u v ⁻¹' S)).card := by
  apply card_image_of_injective
  exact Sym2.map.injective (cycleEmbedding_injective huv)

theorem cycleCutEdges_subset {m p : ℕ} {T : SimpleGraph (Fin m)}
    {u v : Fin m} (huv : T.Adj u v) (horder : u<v)
    (S : Set (Fin m × Fin p)) : cycleCutEdges u v S ⊆ edges (certificate T p) S := by
  intro e he
  obtain ⟨d,hd,rfl⟩ := mem_image.mp he
  obtain ⟨a,b⟩ := d
  obtain ⟨hab,hcross⟩ := (mem_edges_pair _ _ _ _).mp hd
  apply (mem_edges_pair _ _ _ _).mpr
  exact ⟨(cycleHom huv horder).map_rel hab,hcross⟩

theorem cycleCutEdges_noninternal {m p : ℕ} {u v : Fin m} (huv : u≠v)
    (S : Set (Fin m × Fin p)) {e : Sym2 (Fin m × Fin p)}
    (he : e∈cycleCutEdges u v S) : ¬(Sym2.map Prod.fst e).IsDiag := by
  obtain ⟨d,hd,rfl⟩ := mem_image.mp he
  obtain ⟨a,b⟩ := d
  have hab := ((mem_edges_pair _ _ _ _).mp hd).1
  cases a <;> cases b <;>
    simp_all [matchingCycle,cycleEmbedding,Sym2.mk_isDiag_iff,Ne.symm huv]

theorem cycleCutEdges_two_left {m p : ℕ} (hp : 2≤p) {u v : Fin m}
    (huv : u≠v) (S : Set (Fin m × Fin p)) {i j : Fin p}
    (hi : (u,i)∈S) (hj : (u,j)∉S) : 2≤(cycleCutEdges u v S).card := by
  rw [cycleCutEdges_card huv]
  exact edgeReachable_le_cut (matchingCycle p) _ (matchingCycle_two hp
    (Sum.inl i) (Sum.inl j)) hi hj

theorem cycleCutEdges_two_right {m p : ℕ} (hp : 2≤p) {u v : Fin m}
    (huv : u≠v) (S : Set (Fin m × Fin p)) {i j : Fin p}
    (hi : (v,i)∈S) (hj : (v,j)∉S) : 2≤(cycleCutEdges u v S).card := by
  rw [cycleCutEdges_card huv]
  exact edgeReachable_le_cut (matchingCycle p) _ (matchingCycle_two hp
    (Sum.inr i) (Sum.inr j)) hi hj

theorem cycleCutEdges_whole {m p : ℕ} (hp : 2≤p) {u v : Fin m}
    (huv : u≠v) (S : Set (Fin m × Fin p))
    (hwhole : ((∀i,(u,i)∈S) ∧ (∀i,(v,i)∉S)) ∨
      ((∀i,(v,i)∈S) ∧ (∀i,(u,i)∉S))) :
    (cycleCutEdges u v S).card=2*p := by
  rw [cycleCutEdges_card huv]
  have hfull : edges (matchingCycle p) (cycleEmbedding u v ⁻¹' S)=
      (matchingCycle p).edgeFinset := by
    ext e
    obtain ⟨a,b⟩ := e
    simp only [mem_edges_pair,mem_edgeFinset,mem_edgeSet]
    rcases hwhole with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;>
      cases a <;> cases b <;>
      simp [matchingCycle,cycleEmbedding,hu,hv]
  rw [hfull,matchingCycle_edge_card hp]

noncomputable def internalCrossEdge {m p : ℕ} (u : Fin m) (i j : Fin p)
    (S : Set (Fin m × Fin p)) (l : Fin p) : Sym2 (Fin m × Fin p) :=
  if (u,l)∈S then s((u,l),(u,j)) else s((u,i),(u,l))

noncomputable def internalCutWitness {m p : ℕ} (u : Fin m) (i j : Fin p)
    (S : Set (Fin m × Fin p)) : Finset (Sym2 (Fin m × Fin p)) :=
  (univ.erase i).image (internalCrossEdge u i j S)

theorem internalCutWitness_card {m p : ℕ} (u : Fin m) (i j : Fin p)
    (S : Set (Fin m × Fin p)) : (internalCutWitness u i j S).card=p-1 := by
  have hinj : Set.InjOn (internalCrossEdge u i j S) (univ.erase i) := by
    intro a ha b hb he
    have hai : a≠i := (mem_erase.mp ha).1
    have hbi : b≠i := (mem_erase.mp hb).1
    by_cases haS : (u,a)∈S <;> by_cases hbS : (u,b)∈S <;>
      simp only [internalCrossEdge,haS,hbS,ite_true,ite_false] at he <;>
      rcases Sym2.eq_iff.mp he with he | he <;>
      simp only [Prod.mk.injEq] at he <;> aesop
  rw [internalCutWitness,card_image_of_injOn hinj,card_erase_of_mem (mem_univ i),card_univ]
  simp

theorem internalCutWitness_subset {m p : ℕ} (T : SimpleGraph (Fin m))
    (u : Fin m) (i j : Fin p) (S : Set (Fin m × Fin p))
    (hi : (u,i)∈S) (hj : (u,j)∉S) :
    internalCutWitness u i j S ⊆ edges (certificate T p) S := by
  intro e he
  obtain ⟨l,hl,rfl⟩ := mem_image.mp he
  by_cases hlS : (u,l)∈S
  · have hlj : l≠j := by intro h; subst l; exact hj hlS
    simpa only [internalCrossEdge,ite_eq_left hlS] using
      (mem_edges_pair _ S (u,l) (u,j)).mpr ⟨internal_adj T u hlj,Or.inl ⟨hlS,hj⟩⟩
  · have hil : i≠l := by intro h; subst l; exact hlS hi
    simpa only [internalCrossEdge,ite_eq_right hlS] using
      (mem_edges_pair _ S (u,i) (u,l)).mpr ⟨internal_adj T u hil,Or.inl ⟨hi,hlS⟩⟩

theorem internalCutWitness_internal {m p : ℕ} (u : Fin m) (i j : Fin p)
    (S : Set (Fin m × Fin p)) {e : Sym2 (Fin m × Fin p)}
    (he : e∈internalCutWitness u i j S) : (Sym2.map Prod.fst e).IsDiag := by
  obtain ⟨l,_,rfl⟩ := mem_image.mp he
  by_cases hl : (u,l)∈S <;> simp [internalCrossEdge,hl,Sym2.mk_isDiag_iff]

theorem partial_cloud_cut_lower {m p : ℕ} {T : SimpleGraph (Fin m)}
    (hm : 2≤m) (hp : 2≤p) (hT : T.Connected)
    (S : Set (Fin m × Fin p)) (u : Fin m) (i j : Fin p)
    (hi : (u,i)∈S) (hj : (u,j)∉S) :
    p+1≤(edges (certificate T p) S).card := by
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨v,huv⟩ := hT.preconnected.exists_adj_of_nontrivial u
  have hne : u≠v := T.ne_of_adj huv
  let A := internalCutWitness u i j S
  have hA : A.card=p-1 := internalCutWitness_card u i j S
  have hAsub : A⊆edges (certificate T p) S := internalCutWitness_subset T u i j S hi hj
  rcases lt_or_gt_of_ne hne with horder | horder
  · let B := cycleCutEdges u v S
    have hB : 2≤B.card := cycleCutEdges_two_left hp hne S hi hj
    have hBsub : B⊆edges (certificate T p) S := cycleCutEdges_subset huv horder S
    have hd : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro e he hf
      exact cycleCutEdges_noninternal hne S hf (internalCutWitness_internal u i j S he)
    have hc := card_le_card (union_subset hAsub hBsub)
    rw [card_union_of_disjoint hd,hA] at hc
    omega
  · let B := cycleCutEdges v u S
    have hB : 2≤B.card := cycleCutEdges_two_right hp hne.symm S hi hj
    have hBsub : B⊆edges (certificate T p) S := cycleCutEdges_subset huv.symm horder S
    have hd : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro e he hf
      exact cycleCutEdges_noninternal hne.symm S hf (internalCutWitness_internal u i j S he)
    have hc := card_le_card (union_subset hAsub hBsub)
    rw [card_union_of_disjoint hd,hA] at hc
    omega

theorem certificate_cut_lower {m p : ℕ} {T : SimpleGraph (Fin m)}
    (hm : 2≤m) (hp : 2≤p) (hT : T.Connected)
    (S : Set (Fin m × Fin p)) {a b : Fin m × Fin p}
    (ha : a∈S) (hb : b∉S) : p+1≤(edges (certificate T p) S).card := by
  by_cases hpartial : ∃u : Fin m, ∃i j : Fin p, (u,i)∈S ∧ (u,j)∉S
  · obtain ⟨u,i,j,hi,hj⟩ := hpartial
    exact partial_cloud_cut_lower hm hp hT S u i j hi hj
  have hsame (u : Fin m) (i j : Fin p) : (u,i)∈S ↔ (u,j)∈S := by
    constructor
    · intro hi
      by_contra hj
      exact hpartial ⟨u,i,j,hi,hj⟩
    · intro hj
      by_contra hi
      exact hpartial ⟨u,j,i,hj,hi⟩
  let S₀ : Set (Fin m) := {u | (u,a.2)∈S}
  have ha₀ : a.1∈S₀ := ha
  have hb₀ : b.1∉S₀ := fun h => hb ((hsame b.1 a.2 b.2).mp h)
  have hpos : 0<(edges T S₀).card := by
    have h := edgeReachable_le_cut T S₀
      (isEdgeReachable_one.mpr (hT.preconnected a.1 b.1)) ha₀ hb₀
    omega
  obtain ⟨e,he⟩ := card_pos.mp hpos
  obtain ⟨u,v⟩ := e
  obtain ⟨huv,hcross⟩ := (mem_edges_pair T S₀ u v).mp he
  have hne := T.ne_of_adj huv
  have hwhole : ((∀i,(u,i)∈S) ∧ (∀i,(v,i)∉S)) ∨
      ((∀i,(v,i)∈S) ∧ (∀i,(u,i)∉S)) := by
    rcases hcross with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact Or.inl ⟨fun i => (hsame u a.2 i).mp hu,
        fun i hi => hv ((hsame v i a.2).mp hi)⟩
    · exact Or.inr ⟨fun i => (hsame v a.2 i).mp hv,
        fun i hi => hu ((hsame u i a.2).mp hi)⟩
  rcases lt_or_gt_of_ne hne with horder | horder
  · have hc := card_le_card (cycleCutEdges_subset huv horder S)
    rw [cycleCutEdges_whole hp hne S hwhole] at hc
    omega
  · have hc := card_le_card (cycleCutEdges_subset huv.symm horder S)
    rw [cycleCutEdges_whole hp hne.symm S hwhole.symm] at hc
    omega

/-- The corrected sparse certificate is a genuine p-edge-fault connectivity
preserver; all cuts and all failure sets use actual unordered graph edges. -/
theorem certificate_isFTPreserver {m p : ℕ} {G T : SimpleGraph (Fin m)}
    (hTG : T≤G) (hT : T.Connected) (hm : 2≤m) (hp : 2≤p) :
    IsFTConnectivityPreserver (graph G p) (certificate T p) p := by
  refine ⟨certificate_le hTG,fun F hF a b => ?_⟩
  constructor
  · intro _
    have hreach : (certificate T p).IsEdgeReachable (p+1) a b :=
      edgeReachable_of_cut_lower _ (fun S ha hb => certificate_cut_lower hm hp hT S ha hb)
    apply hreach
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast (show F.card<p+1 by omega)
  · intro h
    exact h.mono (afterFaults_mono (certificate_le hTG) F)

end LightEFTSpanners.CorrectedCloud
