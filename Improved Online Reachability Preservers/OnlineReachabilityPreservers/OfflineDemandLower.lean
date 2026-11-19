import OnlineReachabilityPreservers.AcyclicOverlay

/-! The linear demand term in the offline worst-case lower bound. -/

namespace OnlineReachabilityPreservers

open Finset Relation

private theorem bipartite_arc_required {V : Type*} [DecidableEq V] [Fintype V]
    {A : Finset V} {H : Arcs V} (sub : H ⊆ A ×ˢ Aᶜ) {s t : V}
    (left : s ∈ A) (right : t ∈ Aᶜ) (served : Reach H s t) : (s,t) ∈ H := by
  have predecessor {u : V} (r : Reach H s u) (onLeft : u ∈ A) : s = u := by
    cases r with
    | refl => rfl
    | tail _ e => exact ((mem_compl.mp (mem_product.mp (sub e)).2) onLeft).elim
  cases served with
  | refl => exact ((mem_compl.mp right) left).elim
  | tail reach edge =>
    have eq := predecessor reach (mem_product.mp (sub edge)).1
    exact eq.symm ▸ edge

private theorem extend_demand_set {V : Type*} [DecidableEq V] [Fintype V] (active : Arcs V)
    (p : ℕ) (lower : active.card ≤ p) (upper : p ≤ Fintype.card V^2) :
    ∃ D : Arcs V, active ⊆ D ∧ D.card = p := by
  let unused := (univ : Finset (V × V)) \ active
  have unusedSize : unused.card = Fintype.card V^2-active.card := by
    rw [show unused.card = Fintype.card (V × V) - active.card from
      card_sdiff_of_subset (subset_univ _)]
    simp [Fintype.card_prod, pow_two]
  obtain ⟨extra, extraSub, extraSize⟩ :=
    exists_subset_card_eq (s := unused) (show p-active.card ≤ unused.card by omega)
  have separate : Disjoint active extra := by
    apply disjoint_left.mpr
    intro e he hE
    exact (mem_sdiff.mp (extraSub hE)).2 he
  refine ⟨active ∪ extra, subset_union_left, ?_⟩
  rw [card_union_of_disjoint separate, extraSize]
  exact Nat.add_sub_of_le lower

/-- For exactly `p` distinct demands, the offline extremum is at least
`p/6` when `2 ≤ n` and `p ≤ n²`. The extra requests preserve the original
reachability convention even when they are unreachable. -/
theorem offline_linear_demand_lower {n p : ℕ} (hn : 2 ≤ n) (hp : p ≤ n^2) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → p ≤ 6*H.card := by
  let s := n/2
  let A : Finset (Fin n) := (univ : Finset (Fin s)).map (Fin.castLEEmb (Nat.div_le_self n 2))
  let G := A ×ˢ Aᶜ
  let q := min p G.card
  have aSize : A.card = s := by simp [A, s]
  have acyclic : IsDAG G := by
    intro u v edge backwards
    obtain ⟨left, right⟩ := mem_product.mp edge
    cases backwards with
    | refl => exact (mem_compl.mp right) left
    | tail _ final => exact (mem_compl.mp (mem_product.mp final).2) left
  have gSize : G.card = s*(n-s) := by simp [G, card_product, card_compl, aSize]
  have one : n ≤ 3*s := by dsimp only [s]; omega
  have two : n ≤ 2*(n-s) := by dsimp only [s]; omega
  have gCap : n^2 ≤ 6*G.card := by
    rw [gSize, pow_two]
    exact (Nat.mul_le_mul one two).trans_eq (by ring)
  obtain ⟨active, activeSub, activeSize⟩ := exists_subset_card_eq (s := G) (min_le_right p G.card)
  have activeSize' : active.card = q := activeSize
  obtain ⟨D, presentActive, DSize⟩ := extend_demand_set active p
    (activeSize'.trans_le (min_le_left _ _)) (by simpa using hp)
  refine ⟨G, D, acyclic, DSize, ?_⟩
  intro H sub preserves
  have contains : active ⊆ H := by
    intro e he
    have ends := mem_product.mp (activeSub he)
    have present : e ∈ D.toList := mem_toList.mpr (presentActive he)
    exact bipartite_arc_required sub ends.1 ends.2
      ((preserves e present).mpr (Relation.ReflTransGen.single (activeSub he)))
  have bound : p ≤ 6*q := by
    dsimp only [q]
    by_cases enough : p ≤ G.card
    · rw [min_eq_left enough]
      omega
    · rw [min_eq_right (le_of_not_ge enough)]
      exact hp.trans gCap
  have qH : q ≤ H.card := activeSize' ▸ card_le_card contains
  exact bound.trans (Nat.mul_le_mul_left _ qH)


/-- An acyclic bridge-free family yields an instance at the original vertex
and distinct demand counts. The linear lower bound covers the path-count
term in the exact consecutive overlay identity. -/
theorem theorem14_acyclic_extremal_lower {n p : ℕ} (hn : 2 ≤ n) (hp : p ≤ n^2)
    (paths : Fin p → Finset (Fin n)) (nonempty : ∀ i, (paths i).Nonempty)
    (free : ∀ k, IsEmpty (Bridge (PathBefore paths) k)) :
    ∃ (G : Arcs (Fin n)) (D : Finset (Fin n × Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (∑ i, (paths i).card) ≤ 12*H.card := by
  by_cases long : 2*p ≤ ∑ i, (paths i).card
  · obtain ⟨G, demands, acyclic, length, _, exactSize⟩ := theorem14_acyclic_overlay_lower nonempty free
    have nDemands : demands.length = p := by simpa using length
    obtain ⟨D, keeps, size⟩ := extend_demand_set demands.toFinset p
      ((List.toFinset_card_le _).trans_eq nDemands) (by simpa using hp)
    refine ⟨G, D, acyclic, size, ?_⟩
    intro H sub serves
    have retained : Preserves G H demands :=
      fun d hd => serves d (mem_toList.mpr (keeps (List.mem_toFinset.mpr hd)))
    have eq := exactSize H sub retained
    omega
  · obtain ⟨G, D, acyclic, size, lower⟩ := offline_linear_demand_lower hn hp
    refine ⟨G, D, acyclic, size, ?_⟩
    intro H sub serves
    have edge := lower H sub serves
    omega

end OnlineReachabilityPreservers
