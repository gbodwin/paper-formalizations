import MinorFreeSpanners.MaximumSupportedPath

/-! A simple path passes through a distinguished root at most once. Actual
root-avoiding path bounds therefore control the same finite maximum path
chosen for absorption's intrinsic certificate. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem rooted_path_mass_bound {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (S : Finset I) (root : I) (K : ℝ) (hK : 0≤K)
    (havoid : ∀ a b,∀ q : H.Walk a b,q.IsPath → (∀ i∈q.support,i∈S) →
      root∉q.support → pathMass d q≤K)
    {v : I} (p : H.Walk root v) (hp : p.IsPath) (hS : ∀ i∈p.support,i∈S) :
    pathMass d p≤d root+K := by
  classical
  cases p with
  | nil => simpa [pathMass] using hK
  | cons h q =>
    have hn := ((Walk.cons_isPath_iff h q).mp hp).2
    have hq := havoid _ _ q hp.of_cons (fun i hi => hS i (by simp [hi])) hn
    rw [pathMass_cons d h q hn]
    linarith

 theorem path_mass_bound_through_root {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (S : Finset I) (root : I) (K : ℝ)
    (hroot : 0≤d root) (hK : 0≤K)
    (havoid : ∀ a b,∀ q : H.Walk a b,q.IsPath → (∀ i∈q.support,i∈S) →
      root∉q.support → pathMass d q≤K)
    {u v : I} (p : H.Walk u v) (hp : p.IsPath) (hS : ∀ i∈p.support,i∈S) :
    pathMass d p≤d root+2*K := by
  classical
  by_cases hr : root∈p.support
  · let l := p.takeUntil root hr
    let r := p.dropUntil root hr
    have hlp : l.IsPath := hp.takeUntil hr
    have hrp : r.IsPath := hp.dropUntil hr
    have hl := rooted_path_mass_bound d S root K hK havoid l.reverse hlp.reverse
      (fun i hi => hS i (p.support_takeUntil_subset_support hr (by simpa using hi)))
    have hh := rooted_path_mass_bound d S root K hK havoid r hrp
      (fun i hi => hS i (p.support_dropUntil_subset_support hr hi))
    rw [pathMass_reverse] at hl
    have he : l.append r=p := Walk.take_spec p hr
    have hm := pathMass_append d l r (he.symm ▸ hp)
    rw [he] at hm
    linarith
  · have hh := havoid u v p hp hS hr
    linarith

 theorem exists_rooted_diameter_path {I : Type*} (H : SimpleGraph I)
    (d : I → ℝ) (S : Finset I) (root : I) (hrootS : root∈S) (K : ℝ)
    (hroot : 1≤d root) (hK : 0≤K)
    (havoid : ∀ a b,∀ q : H.Walk a b,q.IsPath → (∀ i∈q.support,i∈S) →
      root∉q.support → pathMass d q≤K) :
    ∃ x∈S,∃ y∈S,∃ p : H.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈S) ∧
      d root-1≤pathMass d p-1 ∧ pathMass d p-1≤d root-1+2*K ∧
      ∀ a b,∀ q : H.Walk a b,q.IsPath → (∀ i∈q.support,i∈S) →
        pathMass d q-1≤pathMass d p-1 := by
  classical
  obtain ⟨x,hx,y,hy,p,hp,hps,hmax⟩ := exists_max_supported_path H S ⟨root,hrootS⟩ d
  have hn := hmax root root .nil Walk.IsPath.nil (by simpa using hrootS)
  have hu := path_mass_bound_through_root d S root K (by linarith) hK havoid p hp hps
  have hn' : d root≤pathMass d p := by simpa [pathMass] using hn
  exact ⟨x,hx,y,hy,p,hp,hps,by linarith [hn'],by linarith,
    fun a b q hq hqs => sub_le_sub_right (hmax a b q hq hqs) 1⟩

end MinorFreeSpanners
