import MinorFreeSpanners.ForestPathMass

/-! Removing a genuine leaf preserves all connections between other vertices;
in a forest it also preserves their unique simple paths. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem ConnectedWithin.erase_leaf {V : Type*} {G : SimpleGraph V}
    {S : Finset V} (hS : ConnectedWithin G S) {a z : V} (ha : a∈S)
    (hleaf : ∀ v∈S,G.Adj a v → v=z) : ConnectedWithin G (S.erase a) := by
  classical
  let Q := G.induce (S:Set V)
  let R : Set (S:Set V) := {v | v.val≠a}
  have hQ : Q.Connected := hS.induce_connected ⟨a,ha⟩
  have hR : (Q.induce R).Preconnected := hQ.preconnected.induce_of_degree_eq_one (by
    intro v hv y hy q hq
    have hv' : v.val=a := by simpa [R] using hv
    have hy' : G.Adj a y.val := by simpa [Q,hv'] using hy
    have hq' : G.Adj a q.val := by simpa [Q,hv'] using hq
    exact Subtype.ext ((hleaf y.val y.property hy').trans (hleaf q.val q.property hq').symm))
  intro x hx y hy
  obtain ⟨hxa,hxS⟩ := Finset.mem_erase.mp hx
  obtain ⟨hya,hyS⟩ := Finset.mem_erase.mp hy
  let j : Q.induce R →g G := {toFun := fun v => v.val.val,map_rel' := fun h => h}
  obtain ⟨p⟩ := hR ⟨⟨x,hxS⟩,hxa⟩ ⟨⟨y,hyS⟩,hya⟩
  refine ⟨p.map j,?_⟩
  intro v hv
  rw [Walk.support_map,List.mem_map] at hv
  obtain ⟨v,_,rfl⟩ := hv
  exact Finset.mem_erase.mpr ⟨v.property,v.val.property⟩

 theorem forest_path_avoids_leaf {V : Type*} (G : SimpleGraph V) (hG : G.IsAcyclic)
    {S : Finset V} (hS : ConnectedWithin G S) {a z : V} (ha : a∈S)
    (hleaf : ∀ v∈S,G.Adj a v → v=z) {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hs : ∀ v∈p.support,v∈S)
    (hxa : x≠a) (hya : y≠a) : a∉p.support := by
  classical
  obtain ⟨q,hq⟩ := (hS.erase_leaf ha hleaf) x
    (Finset.mem_erase.mpr ⟨hxa,hs x p.start_mem_support⟩) y
    (Finset.mem_erase.mpr ⟨hya,hs y p.end_mem_support⟩)
  have he := hG.subsingleton_path x y |>.elim ⟨p,hp⟩ q.toPath
  have hv : p=q.toPath.val := congrArg Subtype.val he
  rw [hv]
  intro h
  exact (Finset.mem_erase.mp (hq a (q.support_toPath_subset_support h))).1 rfl

 theorem pathMass_reverse {V : Type*} {G : SimpleGraph V} (d : V → ℝ)
    {x y : V} (p : G.Walk x y) : pathMass d p.reverse=pathMass d p := by
  classical
  simp [pathMass]

 theorem forest_path_mass_erase_bound {V : Type*} (G : SimpleGraph V) (hG : G.IsAcyclic)
    {S : Finset V} (hS : ConnectedWithin G S) {a z : V} (ha : a∈S)
    (hleaf : ∀ v∈S,G.Adj a v → v=z) (d : V → ℝ) (L D : ℝ)
    (hL : 0≤L) (hD : 0≤D) (hda : d a≤D)
    (hsmall : ∀ x y, ∀ p : G.Walk x y,p.IsPath →
      (∀ v∈p.support,v∈S.erase a) → pathMass d p<L) :
    ∀ x y, ∀ p : G.Walk x y,p.IsPath →
      (∀ v∈p.support,v∈S) → pathMass d p≤L+D := by
  classical
  have start (y : V) (p : G.Walk a y) (hp : p.IsPath)
      (hs : ∀ v∈p.support,v∈S) : pathMass d p≤L+D := by
    cases p with
    | nil => simpa [pathMass] using (show d a≤L+D by linarith)
    | @cons a b y hab p =>
      have hpp := (Walk.cons_isPath_iff hab p).mp hp
      have hps : ∀ v∈p.support,v∈S.erase a := by
        intro v hv
        exact Finset.mem_erase.mpr ⟨fun he => hpp.2 (he ▸ hv),hs v (by simp [hv])⟩
      have hmass := hsmall b y p hpp.1 hps
      have he : pathMass d (.cons hab p)=d a+pathMass d p := by
        simp [pathMass,Walk.support_cons,hpp.2]
      rw [he]
      linarith
  intro x y p hp hs
  by_cases hxa : x=a
  · subst x
    exact start y p hp hs
  by_cases hya : y=a
  · subst y
    have hh := start x p.reverse hp.reverse (by simpa using hs)
    simpa only [pathMass_reverse] using hh
  have hav := forest_path_avoids_leaf G hG hS ha hleaf p hp hs hxa hya
  have hmass := hsmall x y p hp (fun v hv =>
    Finset.mem_erase.mpr ⟨fun he => hav (he ▸ hv),hs v hv⟩)
  linarith

end MinorFreeSpanners
