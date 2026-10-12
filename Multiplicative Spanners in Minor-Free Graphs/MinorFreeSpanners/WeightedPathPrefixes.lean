import MinorFreeSpanners.ResidualForestPaths

/-! Actual first-crossing prefixes of weighted simple paths. The selected
prefix is part of the original walk; no segmentation oracle is supplied. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem pathMass_cons {V : Type*} {G : SimpleGraph V} (d : V → ℝ)
    {a b c : V} (h : G.Adj a b) (p : G.Walk b c) (ha : a∉p.support) :
    pathMass d (.cons h p)=d a+pathMass d p := by
  classical
  simp [pathMass,Walk.support_cons,ha]

 theorem exists_weighted_path_prefix {V : Type*} {G : SimpleGraph V}
    (d : V → ℝ) (D L : ℝ) {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hL : 0<L) (hd : ∀ v∈p.support,d v≤D)
    (hm : L≤pathMass d p) :
    ∃ z,∃ q : G.Walk a z,∃ r : G.Walk z b,
      p=q.append r ∧ q.IsPath ∧ L≤pathMass d q ∧ pathMass d q<L+D := by
  classical
  induction p generalizing L with
  | @nil a =>
    refine ⟨a,.nil,.nil,rfl,Walk.IsPath.nil,hm,?_⟩
    have ha := hd a (by simp)
    simpa [pathMass] using (show d a<L+D by linarith)
  | @cons a x b h p ih =>
    have ha : a∉p.support := ((Walk.cons_isPath_iff h p).mp hp).2
    have hmass := pathMass_cons d h p ha
    by_cases hstart : L≤d a
    · refine ⟨a,.nil,.cons h p,rfl,Walk.IsPath.nil,?_,?_⟩
      · simpa [pathMass] using hstart
      · have hda := hd a (by simp)
        simpa [pathMass] using (show d a<L+D by linarith)
    · have hLp : 0<L-d a := by linarith
      have hmp : L-d a≤pathMass d p := by linarith
      obtain ⟨z,q,r,hqr,hq,hlo,hhi⟩ := ih (L-d a) hp.of_cons hLp
        (fun v hv => hd v (by simp [hv])) hmp
      have haq : a∉q.support := by
        intro hx
        exact ha (by rw [hqr,Walk.mem_support_append_iff];exact Or.inl hx)
      refine ⟨z,.cons h q,r,by simp [hqr],hq.cons haq,?_,?_⟩
      · rw [pathMass_cons d h q haq];linarith
      · rw [pathMass_cons d h q haq];linarith

end MinorFreeSpanners
