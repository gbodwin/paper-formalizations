import MinorFreeSpanners.StarPathAugmentation
import MinorFreeSpanners.SimpleRelationPath

/-! Reachability of centers in an actual induced-star packing. The relation
uses a genuine old leaf and a compatible new graph edge. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A real new edge that creates no triangle with the old leaves. -/
def StarCompatible (G : SimpleGraph V) (L : V → Finset V) (x b : V) : Prop :=
  G.Adj b x ∧ ∀ z ∈ L b, ¬ G.Adj x z

/-- The old leaf of one star can be moved to the next star. -/
def StarCenterStep (G : SimpleGraph V) (B : Finset V) (L : V → Finset V)
    (b c : V) : Prop :=
  b ∈ B ∧ c ∈ B ∧ ∃ y ∈ L b, StarCompatible G L y c

omit [Fintype V] [DecidableEq V] in
/-- Turn a vertex-simple directed center chain into the concrete static
alternating route; leaf simplicity follows from the actual packing. -/
theorem static_star_route_of_center_chain {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    {b : V} {bs : List V} (hb : ∀ c ∈ b::bs, c ∈ B)
    (hchain : (b::bs).IsChain (StarCenterStep G B L))
    (hnodup : (b::bs).Nodup)
    (hroom : (L ((b::bs).getLast (List.cons_ne_nil _ _))).card < ell)
    {x : V} (hx : StarCompatible G L x b)
    (hunused : ∀ c ∈ b::bs, x ∉ L c) :
    ∃ xs, StaticStarAlternatingRoute G A B ell L x (b::bs) xs ∧
      ∀ z ∈ xs, z=x ∨ ∃ c ∈ b::bs, z ∈ L c := by
  classical
  induction bs generalizing b x with
  | nil =>
    refine ⟨[x],StaticStarAlternatingRoute.finish (hb b (by simp)) hx.1 hx.2 ?_,?_⟩
    · simpa using hroom
    · intro z hz; exact Or.inl (by simpa using hz)
  | cons c cs ih =>
    have harc := (List.isChain_cons_cons.mp hchain).1
    obtain ⟨y,hy,hyc⟩ := harc.2.2
    have htail : (c::cs).Nodup := (List.nodup_cons.mp hnodup).2
    have hbc : b ∉ c::cs := (List.nodup_cons.mp hnodup).1
    have hyunused : ∀ d ∈ c::cs, y ∉ L d := by
      intro d hd hyd
      have hbd : b ≠ d := fun he => hbc (he.symm ▸ hd)
      exact Finset.disjoint_left.mp (h.2.2.2.2.1 b d hbd) hy hyd
    obtain ⟨ys,hr,hybound⟩ := ih (fun d hd => hb d (by simp [hd]))
      (List.isChain_cons_cons.mp hchain).2 htail
      (by simpa only [List.getLast_cons_cons] using hroom) hyc hyunused
    have hxys : x ∉ ys := by
      intro hxy
      rcases hybound x hxy with he|⟨d,hd,hxd⟩
      · exact hunused b (by simp) (he.symm ▸ hy)
      · exact hunused d (by simp [hd]) hxd
    refine ⟨x::ys,StaticStarAlternatingRoute.step (hb b (by simp)) hx.1 hx.2 hy
      hbc hxys hr,?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact Or.inl rfl
    · rcases hybound z hz with rfl|⟨d,hd,hzd⟩
      · exact Or.inr ⟨b,by simp,hy⟩
      · exact Or.inr ⟨d,by simp [hd],hzd⟩

omit [Fintype V] [DecidableEq V] in
/-- Every vertex of the directed center chain really is an allowed center. -/
theorem star_center_chain_mem {G : SimpleGraph V} {B : Finset V}
    {L : V → Finset V} {b : V} {bs : List V} (hb : b ∈ B)
    (hc : (b::bs).IsChain (StarCenterStep G B L)) :
    ∀ c ∈ b::bs, c ∈ B := by
  induction bs generalizing b with
  | nil => simpa
  | cons d ds ih =>
    intro c hm
    rcases List.mem_cons.mp hm with rfl|hm
    · exact hb
    · exact ih (List.isChain_cons_cons.mp hc).1.2.1
        (List.isChain_cons_cons.mp hc).2 c hm

omit [Fintype V] in
/-- Every center reachable by genuine compatible alternating steps from an
unused leaf is saturated in a maximum packing. -/
theorem maximum_star_reachable_full {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    (hm : ∀ M, IsStarPacking G A B ell M → starPackingSize B M ≤ starPackingSize B L)
    {x s b : V} (hx : x ∈ A) (hn : x ∉ B.biUnion L)
    (hs : s ∈ B) (hxs : StarCompatible G L x s)
    (hr : Relation.ReflTransGen (StarCenterStep G B L) s b) :
    (L b).card = ell := by
  classical
  apply Nat.le_antisymm (h.2.2.2.2.2 b)
  by_contra hlt
  have hroom : (L b).card < ell := by omega
  obtain ⟨bs,hchain,hnodup,hlast⟩ := exists_simple_relation_path hr
  obtain ⟨xs,hroute,_⟩ := static_star_route_of_center_chain h
    (star_center_chain_mem hs hchain) hchain hnodup
    (by simpa only [hlast] using hroom) hxs
    (fun c _ => h.unused_of_uncovered hn c)
  exact maximum_star_packing_no_static_route h hm hx hn hroute

/-- The actual finite closure of compatible seed centers under old-leaf
alternating steps. -/
noncomputable def reachableStarCenters (G : SimpleGraph V) (B : Finset V)
    (L : V → Finset V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun b => ∃ s ∈ B, StarCompatible G L x s ∧
    Relation.ReflTransGen (StarCenterStep G B L) s b

omit [DecidableEq V] in
/-- Reachability does not introduce a center outside B. -/
theorem reachableStarCenters_subset (G : SimpleGraph V) (B : Finset V)
    (L : V → Finset V) (x : V) : reachableStarCenters G B L x ⊆ B := by
  classical
  intro b hb
  obtain ⟨s,hs,hxs,hr⟩ := (Finset.mem_filter.mp hb).2
  obtain ⟨bs,hchain,_,hlast⟩ := exists_simple_relation_path hr
  have hm := star_center_chain_mem hs hchain b
  exact hm (hlast ▸ List.getLast_mem (List.cons_ne_nil _ _))

/-- Every reachable star has exactly ell actual leaves. -/
theorem reachableStarCenters_full {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    (hm : ∀ M, IsStarPacking G A B ell M → starPackingSize B M ≤ starPackingSize B L)
    {x : V} (hx : x ∈ A) (hn : x ∉ B.biUnion L) :
    ∀ b ∈ reachableStarCenters G B L x, (L b).card = ell := by
  classical
  intro b hb
  obtain ⟨s,hs,hxs,hr⟩ := (Finset.mem_filter.mp hb).2
  exact maximum_star_reachable_full h hm hx hn hs hxs hr

end MinorFreeSpanners
