import MinorFreeSpanners.ForestStarLeaf

/-! Actual bounded-mass branching cores. The selected core contains a genuine
three-neighbor star and has a surplus neighbor outside every simple path. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem three_neighbors_off_path {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (x : V) (N : Finset V)
    (hN : ∀ y∈N,G.Adj x y) (hcard : 3≤N.card)
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) : ∃ y∈N,y∉p.support := by
  classical
  by_contra hn
  push Not at hn
  have hsub : N⊆(G.neighborFinset x).filter fun y => y∈p.support := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr (hN y hy),hn y hy⟩
  have hle := (Finset.card_le_card hsub).trans (acyclic_path_neighbors_le_two G hG p hp x)
  omega

 theorem exists_bounded_branching_core {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (W : Finset V)
    (hW : ConnectedWithin G W) (x : V) (N : Finset V)
    (hN : ∀ y∈N,G.Adj x y) (hcard : 3≤N.card) (hNW : insert x N⊆W)
    (d : V → ℝ) (L D : ℝ) (hD : 0≤D) (hLD : 3*D<L)
    (hdpos : ∀ v∈W,0<d v) (hd : ∀ v∈W,d v≤D)
    (hlarge : ∃ a b,∃ p : G.Walk a b,p.IsPath ∧
      (∀ v∈p.support,v∈W) ∧ L≤pathMass d p) :
    ∃ S : Finset V,S⊆W ∧ insert x N⊆S ∧ ConnectedWithin G S ∧
      (∃ a b,∃ p : G.Walk a b,p.IsPath ∧
        (∀ v∈p.support,v∈S) ∧ L≤pathMass d p) ∧
      (∀ a b,∀ p : G.Walk a b,p.IsPath →
        (∀ v∈p.support,v∈S) → pathMass d p≤L+D) ∧
      (∀ a b,∀ p : G.Walk a b,p.IsPath → ∃ y∈S,G.Adj x y ∧ y∉p.support) := by
  classical
  let large (S : Finset V) := ∃ a b,∃ p : G.Walk a b,p.IsPath ∧
    (∀ v∈p.support,v∈S) ∧ L≤pathMass d p
  let good (S : Finset V) := S⊆W ∧ insert x N⊆S ∧ ConnectedWithin G S ∧ large S
  let candidates := (Finset.univ : Finset (Finset V)).filter good
  have hWgood : W∈candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Subset.rfl,hNW,hW,hlarge⟩
  obtain ⟨S,hSc,hmin⟩ := Finset.exists_min_image candidates Finset.card ⟨W,hWgood⟩
  obtain ⟨hSW,hNS,hS,hLS⟩ := (Finset.mem_filter.mp hSc).2
  have hne : S.Nonempty := ⟨x,hNS (by simp)⟩
  obtain ⟨a,ha,hak,z,hleaf⟩ := exists_leaf_outside_star G hG S hne x N hN hNS d L D
    (fun v hv => hdpos v (hSW hv)) (fun v hv => hd v (hSW hv)) hD hLD hLS
  have heconn := hS.erase_leaf ha hleaf
  have heK : insert x N⊆S.erase a := by
    intro v hv
    exact Finset.mem_erase.mpr ⟨fun he => hak (he ▸ hv),hNS hv⟩
  have hesmall : ∀ u v,∀ p : G.Walk u v,p.IsPath →
      (∀ w∈p.support,w∈S.erase a) → pathMass d p<L := by
    intro u v p hp hs
    by_contra hn
    have hen : S.erase a∈candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.erase_subset a S).trans hSW,heK,heconn,
        u,v,p,hp,hs,le_of_not_gt hn⟩
    have hc := hmin (S.erase a) hen
    have hecard := Finset.card_erase_of_mem ha
    have hpos := Finset.card_pos.mpr hne
    omega
  refine ⟨S,hSW,hNS,hS,hLS,?_,?_⟩
  · exact forest_path_mass_erase_bound G hG hS ha hleaf d L D (by linarith) hD
      (hd a (hSW ha)) hesmall
  · intro u v p hp
    obtain ⟨y,hy,hyp⟩ := three_neighbors_off_path G hG x N hN hcard p hp
    exact ⟨y,hNS (Finset.mem_insert_of_mem hy),hN y hy,hyp⟩

end MinorFreeSpanners
