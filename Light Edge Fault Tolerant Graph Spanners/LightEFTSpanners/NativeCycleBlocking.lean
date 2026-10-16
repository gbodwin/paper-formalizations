import LightEFTSpanners.NativeCycleRotation

namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- No two trace positions can buy the same ID in a duplicate-free input list. -/
theorem InsertionTrace.same_earlier [DecidableEq E] {G : Graph V E} {w : E → ℝ≥0}
    {t : ℝ≥0} {f : ℕ} {seed : Finset E} {es : List E} {e : E}
    (hn : es.Nodup) (a b : InsertionTrace G w t f seed es e) : a.earlier = b.earlier := by
  have ha : (a.preEdges ++ e :: a.postEdges).Nodup := a.decomposition ▸ hn
  have hpre : e ∉ a.preEdges := fun he =>
    (List.nodup_append.mp ha).2.2 e he e (by simp) rfl
  have hpost : e ∉ a.postEdges := (List.nodup_cons.mp ha.of_append_right).1
  have hab := (List.append_cons_inj_of_notMem hpre hpost).mp
    (a.decomposition.symm.trans b.decomposition)
  unfold InsertionTrace.earlier
  rw [hab.2.2]

/-- Rotate an arbitrary original-ID edge-simple cycle at its latest candidate.
All complementary IDs lie in the exact earlier selected state; the seed lies
there too. Every nonseed cycle edge weighs at most the chosen candidate. -/
theorem latest_cycle_complement [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (f : ℕ) (seed : Finset E) (es : List E)
    (hsort : es.Pairwise (fun e d => w d ≤ w e)) (u : G.vertexSet)
    (p : Walk G (nativeGreedy G w t f seed es) ∅ u u) (hp : p.edgeList.Nodup)
    (hne : ∃ d ∈ p.edgeList, d ∉ seed) :
    ∃ e ∈ p.edgeList, e ∉ seed ∧ ∃ tr : InsertionTrace G w t f seed es e,
      seed ⊆ tr.earlier ∧ ∃ x y : G.vertexSet, G.IsLink e x.val y.val ∧
      ∃ r : Walk G tr.earlier ∅ y x, r.edgeList.Nodup ∧
        (∀ d, d ∈ r.edgeList ↔ d ∈ p.edgeList ∧ d ≠ e) ∧
        r.weight w + w e = p.weight w ∧
        (∀ d ∈ p.edgeList, d ∉ seed → w d ≤ w e) := by
  classical
  have hC : p.edgeList.toFinset ⊆ nativeGreedy G w t f seed es :=
    fun e he => p.edgeList_selected e (List.mem_toFinset.mp he)
  have hN : (p.edgeList.toFinset \ seed).Nonempty := by
    obtain ⟨d,hd,hs⟩ := hne
    exact ⟨d,mem_sdiff.mpr ⟨List.mem_toFinset.mpr hd,hs⟩⟩
  obtain ⟨e,he,tr,hrest,hweight⟩ := exists_latest_trace G w t f seed es hsort _ hC hN
  have hep : e ∈ p.edgeList := List.mem_toFinset.mp (mem_sdiff.mp he).1
  obtain ⟨x,y,hl,r,hrn,hrmem,hrw⟩ := p.cycle_complement w hp e hep
  have hRA : ∀ d ∈ r.edgeList, d ∈ tr.earlier := by
    intro d hd
    obtain ⟨hdp,hdne⟩ := (hrmem d).mp hd
    exact hrest (mem_erase.mpr ⟨hdne,List.mem_toFinset.mpr hdp⟩)
  obtain ⟨s,hse,hsw⟩ := r.transfer_selected w tr.earlier hRA
  refine ⟨e,hep,(mem_sdiff.mp he).2,tr,tr.seed_subset,x,y,hl,s,?_,?_,?_,?_⟩
  · rwa [hse]
  · intro d; rw [hse]; exact hrmem d
  · rwa [hsw]
  · intro d hd hs
    exact hweight d (mem_sdiff.mpr ⟨List.mem_toFinset.mpr hd,hs⟩)

/-- A fixed blocker family, derived once from actual traces. -/
def TracedBlockers [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0) (t : ℝ≥0)
    (f : ℕ) (seed : Finset E) (es : List E) (block : E → Finset E) : Prop :=
  ∀ e ∈ nativeGreedy G w t f seed es \ seed,
    ∃ tr : InsertionTrace G w t f seed es e,
      InsertionWitness G w t f tr.earlier e (block e)

theorem exists_traced_blockers [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (f : ℕ) (seed : Finset E) (es : List E)
    (hsort : es.Pairwise (fun e d => w d ≤ w e)) :
    ∃ block : E → Finset E, TracedBlockers G w t f seed es block ∧
      ∀ e ∉ nativeGreedy G w t f seed es \ seed, block e = ∅ := by
  classical
  have hex : ∀ e, ∃ F : Finset E,
      (e ∈ nativeGreedy G w t f seed es \ seed →
        ∃ tr : InsertionTrace G w t f seed es e, InsertionWitness G w t f tr.earlier e F) ∧
      (e ∉ nativeGreedy G w t f seed es \ seed → F = ∅) := by
    intro e
    by_cases he : e ∈ nativeGreedy G w t f seed es \ seed
    · obtain ⟨d,hd,tr,_,_⟩ := exists_latest_trace G w t f seed es hsort {e}
        (singleton_subset_iff.mpr (mem_sdiff.mp he).1)
        ⟨e,mem_sdiff.mpr ⟨mem_singleton_self e,(mem_sdiff.mp he).2⟩⟩
      have hde : d = e := mem_singleton.mp (mem_sdiff.mp hd).1
      subst d
      obtain ⟨F,hF⟩ := tr.witness
      exact ⟨F,fun _ => ⟨tr,hF⟩,fun hn => False.elim (hn he)⟩
    · exact ⟨∅,fun hh => False.elim (he hh),fun _ => rfl⟩
  choose block hb using hex
  exact ⟨block,fun e he => (hb e).1 he,fun e he => (hb e).2 he⟩

/-- The fixed family blocks every sufficiently short native edge-simple cycle
relative to any of its nonseed edges. Distinct parallel IDs and loops are not
collapsed or excluded by a minimum cycle length hypothesis. -/
theorem TracedBlockers.blocks_cycle [DecidableEq E] {G : Graph V E} {w : E → ℝ≥0}
    {t : ℝ≥0} {f : ℕ} {seed : Finset E} {es : List E} {block : E → Finset E}
    (hb : TracedBlockers G w t f seed es block) (hn : es.Nodup)
    (hsort : es.Pairwise (fun e d => w d ≤ w e)) (u : G.vertexSet)
    (p : Walk G (nativeGreedy G w t f seed es) ∅ u u) (hp : p.edgeList.Nodup)
    (d : E) (hd : d ∈ p.edgeList) (hds : d ∉ seed)
    (hw : p.weight w ≤ (t+1) * w d) :
    ∃ e ∈ p.edgeList, e ∉ seed ∧ ∃ z ∈ p.edgeList, z ∈ block e := by
  obtain ⟨e,he,hes,tr,_,x,y,hl,r,_,hrmem,hrw,hweight⟩ :=
    latest_cycle_complement G w t f seed es hsort u p hp ⟨d,hd,hds⟩
  obtain ⟨tr',hF⟩ := hb e (mem_sdiff.mpr ⟨p.edgeList_selected e he,hes⟩)
  have hEq := tr'.same_earlier hn tr
  rw [hEq] at hF
  have hwd : w d ≤ w e := hweight d hd hds
  have hshort : r.weight w ≤ t * w e := by nlinarith
  obtain ⟨z,hzr,hzF⟩ := hF.blocks_detour hl.symm r hshort
  exact ⟨e,he,hes,z,((hrmem z).mp hzr).1,hzF⟩

/-- Caps, no self-blocking and actual selected-blocker membership, for the
same fixed family used in blocks_cycle. -/
theorem TracedBlockers.sampling [DecidableEq E] {G : Graph V E} {w : E → ℝ≥0}
    {t : ℝ≥0} {f : ℕ} {seed : Finset E} {es : List E} {block : E → Finset E}
    (hb : TracedBlockers G w t f seed es block)
    (e : E) (he : e ∈ nativeGreedy G w t f seed es \ seed) :
    (block e).card ≤ f ∧ e ∉ block e ∧ block e ⊆ nativeGreedy G w t f seed es := by
  obtain ⟨tr,hF⟩ := hb e he
  exact ⟨hF.2.2.1,fun h => hF.1 (hF.2.1 h),hF.2.1.trans tr.earlier_subset⟩

/-- Clean subhosts exclude every short cycle relative to any nonseed edge.
There is no earlier-detour premise. Seed-only and seed-dominated cycles are not
asserted to have full weighted girth here. -/
theorem TracedBlockers.clean_cycle [DecidableEq E] {G : Graph V E} {w : E → ℝ≥0}
    {t : ℝ≥0} {f : ℕ} {seed : Finset E} {es : List E} {block : E → Finset E}
    (hb : TracedBlockers G w t f seed es block) (hn : es.Nodup)
    (hsort : es.Pairwise (fun e d => w d ≤ w e)) (R : Finset E)
    (hR : R ⊆ nativeGreedy G w t f seed es)
    (hclean : ∀ e ∈ R, e ∉ seed → Disjoint (block e) R)
    (u : G.vertexSet) (p : Walk G R ∅ u u) (hp : p.edgeList.Nodup)
    (d : E) (hd : d ∈ p.edgeList) (hds : d ∉ seed) :
    (t+1)*w d < p.weight w := by
  by_contra hh
  have hw : p.weight w ≤ (t+1)*w d := le_of_not_gt hh
  obtain ⟨s,hse,hsw⟩ := p.transfer_selected w _ (fun e he => hR (p.edgeList_selected e he))
  have hsn : s.edgeList.Nodup := hse.symm ▸ hp
  obtain ⟨e,he,hes,z,hz,hblock⟩ := hb.blocks_cycle hn hsort u s hsn d
    (hse.symm ▸ hd) hds (hsw.trans_le hw)
  have heR : e ∈ R := p.edgeList_selected e (hse ▸ he)
  have hzR : z ∈ R := p.edgeList_selected z (hse ▸ hz)
  exact Finset.disjoint_left.mp (hclean e heR hes) hblock hzR

end LightEFTSpanners.NativeWeighted
