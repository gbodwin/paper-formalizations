import GreedyShortcuts.SCCQuotient

/-! Actual two-way representative stars and bounded lifting of the SCC DAG.
The construction costs at most 2n edges and turns every contracted edge into
an original augmented walk of at most three hops. -/
namespace GreedyShortcuts.SCCQuotient

open Finset SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def stars (G : V → V → Prop) : Finset (V × V) := by
  classical
  exact ((Finset.univ.image fun v => (v,representative G (component G v))) ∪
    (Finset.univ.image fun v => (representative G (component G v),v))).filter (fun e => e.1 ≠ e.2)

theorem stars_legal (G : V → V → Prop) : stars G ⊆ candidates G := by
  classical
  intro e he
  obtain ⟨he,hne⟩ := Finset.mem_filter.mp he
  apply (mem_candidates G e).mpr
  refine ⟨hne,?_⟩
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
    exact (representative_mutual G v).2
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
    exact (representative_mutual G v).1

theorem stars_card (G : V → V → Prop) : (stars G).card ≤ 2*Fintype.card V := by
  classical
  calc
    (stars G).card ≤ ((Finset.univ.image fun v => (v,representative G (component G v))) ∪
      (Finset.univ.image fun v => (representative G (component G v),v))).card := Finset.card_filter_le _ _
    _ ≤ (Finset.univ.image fun v => (v,representative G (component G v))).card +
      (Finset.univ.image fun v => (representative G (component G v),v)).card := Finset.card_union_le _ _
    _ ≤ Fintype.card V + Fintype.card V := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2*Fintype.card V := by omega

theorem to_representative (G : V → V → Prop) (v : V) :
    ∃ p : DWalk v (representative G (component G v)),Allowed (augment G (stars G)) p ∧ p.length ≤ 1 := by
  classical
  by_cases he : v = representative G (component G v)
  · exact ⟨(Walk.nil : DWalk v v).copy rfl he,by simp [Allowed],by simp⟩
  · apply DirectedLift.edge_walk
    exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩),he⟩)

theorem from_representative (G : V → V → Prop) (v : V) :
    ∃ p : DWalk (representative G (component G v)) v,Allowed (augment G (stars G)) p ∧ p.length ≤ 1 := by
  classical
  by_cases he : representative G (component G v) = v
  · exact ⟨(Walk.nil : DWalk v v).copy he.symm rfl,by simp [Allowed],by simp⟩
  · apply DirectedLift.edge_walk
    exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩),he⟩)

theorem edge_three_hops (G : V → V → Prop) {a b : Component G} (hab : graph G a b) :
    ∃ p : DWalk (representative G a) (representative G b),
      Allowed (augment G (stars G)) p ∧ p.length ≤ 3 := by
  obtain ⟨u,v,huv,rfl,rfl⟩ := hab
  obtain ⟨p,hp,hp1⟩ := from_representative G u
  obtain ⟨q,hq,hq1⟩ := DirectedLift.edge_walk (G := augment G (stars G)) (s := u) (t := v) (Or.inl huv)
  obtain ⟨r,hr,hr1⟩ := to_representative G v
  refine ⟨p.append (q.append r),(allowed_append _ _ _).mpr ⟨hp,(allowed_append _ _ _).mpr ⟨hq,hr⟩⟩,?_⟩
  simp only [Walk.length_append]
  omega

noncomputable def lifted (G : V → V → Prop) (J : Finset (Component G × Component G)) : Finset (V × V) :=
  stars G ∪ DirectedMap.edges (representative G) J

theorem mapped_legal (G : V → V → Prop) {J : Finset (Component G × Component G)}
    (hJ : J ⊆ candidates (graph G)) : DirectedMap.edges (representative G) J ⊆ candidates G := by
  intro e he
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp he
  have hh := (mem_candidates (graph G) (a,b)).mp (hJ hab)
  exact (mem_candidates G _).mpr ⟨fun he => hh.1 (representative_injective G he),reachable_lift G hh.2⟩

theorem lifted_legal (G : V → V → Prop) {J : Finset (Component G × Component G)}
    (hJ : J ⊆ candidates (graph G)) : lifted G J ⊆ candidates G :=
  Finset.union_subset (stars_legal G) (mapped_legal G hJ)

theorem lifted_card (G : V → V → Prop) (J : Finset (Component G × Component G)) :
    (lifted G J).card ≤ 2*Fintype.card V + J.card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add (stars_card G) (DirectedMap.edges_card_le _ _))

theorem augment_star_mono (G : V → V → Prop) (J : Finset (Component G × Component G)) (u v : V) :
    augment G (stars G) u v → augment G (lifted G J) u v :=
  fun h => h.elim Or.inl (fun he => Or.inr (Finset.mem_union_left _ he))

theorem augmented_edge_three_hops (G : V → V → Prop) (J : Finset (Component G × Component G))
    {a b : Component G} (hab : augment (graph G) J a b) :
    ∃ p : DWalk (representative G a) (representative G b),
      Allowed (augment G (lifted G J)) p ∧ p.length ≤ 3 := by
  rcases hab with hab | hab
  · obtain ⟨p,hp,hp3⟩ := edge_three_hops G hab
    exact ⟨p,allowed_mono (augment_star_mono G J) hp,hp3⟩
  · obtain ⟨p,hp,hp1⟩ := DirectedLift.edge_walk (G := augment G (lifted G J))
      (s := representative G a) (t := representative G b)
      (Or.inr (Finset.mem_union_right _ (DirectedMap.mem_edges _ _ hab)) :
        augment G (lifted G J) (representative G a) (representative G b))
    exact ⟨p,hp,hp1.trans (by decide)⟩

/-- The quantitative SCC reduction used in Section 3.3, for actual lifted
shortcut sets rather than an assumed output guarantee. -/
theorem lifted_hop_bound (G : V → V → Prop) (J : Finset (Component G × Component G))
    (β : ℕ) (hβ : ∀ a b,Reachable (graph G) a b → hopDist (augment (graph G) J) a b ≤ β)
    {s t : V} (hr : Reachable G s t) : hopDist (augment G (lifted G J)) s t ≤ 3*β+2 := by
  have hc := reachable_project G hr
  have hc' := reachable_augment (graph G) J hc
  let p := canonical (augment (graph G) J) (component G s) (component G t) hc'
  have hp := canonical_optimal (augment (graph G) J) (component G s) (component G t) hc'
  have hpβ : p.length ≤ β := by simpa only [hopDist_eq _ hc'] using hβ _ _ hc
  obtain ⟨q,hq,hq3⟩ := DirectedLift.bounded (representative G) 3
    (fun _ _ => augmented_edge_three_hops G J) p hp.1
  obtain ⟨l,hl,hl1⟩ := to_representative G s
  obtain ⟨r,hr',hr1⟩ := from_representative G t
  have hw := hopDist_le_walk (augment G (lifted G J)) (l.append (q.append r))
    ((allowed_append _ _ _).mpr ⟨allowed_mono (augment_star_mono G J) hl,
      (allowed_append _ _ _).mpr ⟨hq,allowed_mono (augment_star_mono G J) hr'⟩⟩)
  simp only [Walk.length_append] at hw
  omega

end GreedyShortcuts.SCCQuotient
