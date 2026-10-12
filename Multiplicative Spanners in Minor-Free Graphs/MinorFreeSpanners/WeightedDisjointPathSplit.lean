import MinorFreeSpanners.WeightedPathSplit

/-! A first-crossing prefix and its vertex-disjoint remaining suffix retain
the actual original joining edge. No boundary vertex is charged twice. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem exists_weighted_disjoint_path_split {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (D L : ℝ) (hD : 0≤D) (hL : 0<L) {x y : I} (p : H.Walk x y) (hp : p.IsPath)
    (hd : ∀ i∈p.support,d i≤D) (hm : 2*L+D≤pathMass d p) :
    ∃ u v,∃ q : H.Walk x u,∃ r : H.Walk v y,∃ h : H.Adj u v,
      p=q.append (.cons h r) ∧ q.IsPath ∧ r.IsPath ∧
      p.support=q.support++r.support ∧
      Disjoint q.support.toFinset r.support.toFinset ∧
      L≤pathMass d q ∧ pathMass d q<L+D ∧ L≤pathMass d r ∧ r.length<p.length := by
  classical
  obtain ⟨u,q,s,he,hq,hlo,hhi⟩ := exists_weighted_path_prefix d D L p hp hL hd (by linarith)
  have hsp : s.IsPath := (he ▸ hp).of_append_right
  cases s with
  | nil =>
    simp only [Walk.append_nil] at he
    have hh : pathMass d p=pathMass d q := congrArg (pathMass d) he
    linarith
  | cons h r =>
    have hwhole : (q.append (.cons h r)).IsPath := he ▸ hp
    have hsum := pathMass_append d q (.cons h r) hwhole
    have hmass := pathMass_cons d h r ((Walk.cons_isPath_iff h r).mp hsp).2
    rw [←he] at hsum
    have hs : p.support=q.support++r.support := by
      rw [he,Walk.support_append]
      rfl
    have hn : (q.support++r.support).Nodup := hs ▸ hp.support_nodup
    have hdis := (List.nodup_append.mp hn).2.2
    refine ⟨u,_,q,r,h,he,hq,hsp.of_cons,hs,?_,hlo,hhi,by linarith,?_⟩
    · apply Finset.disjoint_left.mpr
      intro i hi hj
      exact hdis i (List.mem_toFinset.mp hi) i (List.mem_toFinset.mp hj) rfl
    · rw [he,Walk.length_append,Walk.length_cons]
      omega

end MinorFreeSpanners
