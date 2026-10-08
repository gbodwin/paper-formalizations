import LinearDistancePreservers.InducedMatchings
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Max

/-! Finite optimization proof of lazy shortest-path tree existence (Lemma 5).
Parents point toward the root. We first minimize the number of non-root
vertices, then the number of vertices with exactly one child. This is the
well-founded potential in the paper, expressed without an iterative algorithm.
Unreachable demands are allowed and do not require a tree path. -/
namespace LinearDistancePreservers
namespace LazyTreeSelection
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def support (f : V → Option V) : Finset V :=
  univ.filter fun v => f v ≠ none

def Single (f : V → Option V) (u : V) : Prop := ∃! v, f v = some u

noncomputable def singles (f : V → Option V) : Finset V :=
  univ.filter (Single f)

def Valid (G : SimpleGraph V) (s : V) (D : Finset V) (f : V → Option V) : Prop :=
  f s = none ∧
  (∀ v u, f v = some u → G.Adj u v ∧ G.dist s v = G.dist s u + 1 ∧
    (u = s ∨ f u ≠ none)) ∧
  ∀ v ∈ D, G.Reachable s v → v = s ∨ f v ≠ none

theorem exists_predecessor (G : SimpleGraph V) {s v : V}
    (hr : G.Reachable s v) (hne : v ≠ s) :
    ∃ u, G.Adj u v ∧ G.dist s v = G.dist s u + 1 ∧ G.Reachable s u := by
  obtain ⟨p, hp⟩ := hr.symm.exists_walk_length_eq_dist
  cases p with
  | nil => exact (hne rfl).elim
  | @cons v u s h p =>
    have hle := G.dist_le p
    have hd := h.symm.reachable.dist_triangle_right s
    rw [dist_eq_one_iff_adj.mpr h.symm] at hd
    rw [G.dist_comm] at hp hle
    simp only [Walk.length_cons] at hp
    exact ⟨u, h.symm, by omega, p.reachable.symm⟩

theorem exists_valid (G : SimpleGraph V) (s : V) (D : Finset V) :
    ∃ f, Valid G s D f := by
  classical
  let f : V → Option V := fun v =>
    if h : G.Reachable s v ∧ v ≠ s then some (exists_predecessor G h.1 h.2).choose
    else none
  refine ⟨f, ?_, ?_, ?_⟩
  · simp [f]
  · intro v u hu
    dsimp [f] at hu
    split at hu
    next h =>
      have he := (exists_predecessor G h.1 h.2).choose_spec
      have heq := Option.some.inj hu
      rw [heq] at he
      refine ⟨he.1, he.2.1, ?_⟩
      by_cases hs : u = s
      · exact Or.inl hs
      · exact Or.inr (by simp [f, he.2.2, hs])
    next h => cases hu
  · intro v hv hr
    by_cases hs : v = s
    · exact Or.inl hs
    · exact Or.inr (by simp [f, hr, hs])

/-- Both minima are attained in the finite set of parent functions. -/
theorem exists_optimal (G : SimpleGraph V) (s : V) (D : Finset V) :
    ∃ f, Valid G s D f ∧
      (∀ g, Valid G s D g → (support f).card ≤ (support g).card) ∧
      (∀ g, Valid G s D g → (support g).card = (support f).card →
        (singles f).card ≤ (singles g).card) := by
  classical
  let A : Finset (V → Option V) := univ.filter (Valid G s D)
  have hA : A.Nonempty := by
    obtain ⟨f, hf⟩ := exists_valid G s D
    exact ⟨f, by simp [A, hf]⟩
  obtain ⟨f, hf, hmin⟩ := exists_min_image A (fun f => (support f).card) hA
  let B := A.filter fun g => (support g).card = (support f).card
  have hB : B.Nonempty := ⟨f, by simp [B, hf]⟩
  obtain ⟨g, hg, hmin'⟩ := exists_min_image B (fun g => (singles g).card) hB
  have hg' := mem_filter.mp hg
  refine ⟨g, (mem_filter.mp hg'.1).2, ?_, ?_⟩
  · intro h hh
    rw [hg'.2]
    exact hmin h (by simp [A, hh])
  · intro h hh hc
    apply hmin' h
    simp only [B, mem_filter]
    exact ⟨by simp [A, hh], hc.trans hg'.2⟩

theorem support_update_some (f : V → Option V) {v u a : V}
    (hv : f v = some a) : support (Function.update f v (some u)) = support f := by
  classical
  ext z
  by_cases hz : z = v <;> simp [support, Function.update, hz, hv]

/-- Moving the unique child of one single-child parent to another removes
both parents from `singles`, and creates no new single-child parent. -/
theorem singles_reroute (f : V → Option V) {x x' y y' : V}
    (hxy : f y = some x) (hx'y' : f y' = some x')
    (hx : Single f x) (hx' : Single f x') (hxx' : x ≠ x') :
    singles (Function.update f y' (some x)) ⊂ singles f := by
  classical
  let g := Function.update f y' (some x)
  have hyy' : y ≠ y' := by
    intro h
    exact hxx' (Option.some.inj (hxy.symm.trans (h ▸ hx'y')))
  have hxyg : g y = some x := by simp [g, hyy', hxy]
  have hx'y'g : g y' = some x := by simp [g]
  have nox : ¬ Single g x := by
    rintro ⟨z, hz, hu⟩
    exact hyy' ((hu y hxyg).trans (hu y' hx'y'g).symm)
  have nox' : ¬ Single g x' := by
    rintro ⟨z, hz, hu⟩
    by_cases hzy : z = y'
    · subst z
      exact hxx' (Option.some.inj (hx'y'g.symm.trans hz))
    · have hfz : f z = some x' := by simpa [g, Function.update, hzy] using hz
      obtain ⟨a, ha, hua⟩ := hx'
      exact hzy ((hua z hfz).trans (hua y' hx'y').symm)
  have hsub : singles g ⊆ singles f := by
    intro z hz
    have hsg : Single g z := (mem_filter.mp hz).2
    have hzx : z ≠ x := fun h => nox (h ▸ hsg)
    have hzx' : z ≠ x' := fun h => nox' (h ▸ hsg)
    have he (v : V) : g v = some z ↔ f v = some z := by
      by_cases hv : v = y'
      · subst v
        simp [g, hx'y', Ne.symm hzx, Ne.symm hzx']
      · simp [g, Function.update, hv]
    exact mem_filter.mpr ⟨mem_univ _, by simpa only [Single, he] using hsg⟩
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro heq
  have : x ∈ singles g := heq.symm ▸ mem_filter.mpr ⟨mem_univ _, hx⟩
  exact nox (mem_filter.mp this).2

/-- The optimizer has the lazy-tree cross-edge exclusion. -/
theorem optimal_lazy (G : SimpleGraph V) (s : V) (D : Finset V)
    (f : V → Option V) (hf : Valid G s D f)
    (hmin : ∀ g, Valid G s D g → (support g).card = (support f).card →
      (singles f).card ≤ (singles g).card)
    {x x' y y' : V} (hxy : f y = some x) (hx'y' : f y' = some x')
    (hx : Single f x) (hx' : Single f x') (hne : x ≠ x')
    (hd : G.dist s x = G.dist s x') : ¬ G.Adj x y' := by
  classical
  intro hadj
  let g := Function.update f y' (some x)
  have hy's : y' ≠ s := by intro h; rw [h, hf.1] at hx'y'; cases hx'y'
  have hxy' : x ≠ y' := hadj.ne
  have hsupp : ∀ z, g z ≠ none ↔ f z ≠ none := by
    intro z
    by_cases hz : z = y' <;> simp [g, Function.update, hz, hx'y']
  have hvalid : Valid G s D g := by
    refine ⟨by simp [g, Function.update, Ne.symm hy's, hf.1], ?_, ?_⟩
    · intro v u hv
      by_cases h : v = y'
      · subst v
        have hu : x = u := by simpa [g] using hv
        subst u
        have hpar := (hf.2.1 y x hxy).2.2
        exact ⟨hadj, (hf.2.1 y' x' hx'y').2.1.trans (by rw [hd]),
          hpar.imp_right (fun h => (hsupp x).mpr h)⟩
      · have hv' : f v = some u := by simpa [g, Function.update, h] using hv
        have ht := hf.2.1 v u hv'
        exact ⟨ht.1, ht.2.1, ht.2.2.imp_right (fun h => (hsupp u).mpr h)⟩
    · intro v hv hr
      exact (hf.2.2 v hv hr).imp_right ((hsupp v).mpr)
  have hle := hmin g hvalid (congrArg Finset.card (support_update_some f hx'y'))
  exact (Finset.card_lt_card (singles_reroute f hxy hx'y' hx hx' hne)).not_ge hle

/-- Minimal trees have no non-root leaf outside the demand endpoints. -/
theorem optimal_leaves (G : SimpleGraph V) (s : V) (D : Finset V)
    (f : V → Option V) (hf : Valid G s D f)
    (hmin : ∀ g, Valid G s D g → (support f).card ≤ (support g).card)
    {v : V} (hv : f v ≠ none) (hleaf : ∀ z, f z ≠ some v) : v ∈ D := by
  classical
  by_contra hD
  let g := Function.update f v none
  have hvs : v ≠ s := by intro h; exact hv (h ▸ hf.1)
  have hvalid : Valid G s D g := by
    refine ⟨by simp [g, Ne.symm hvs, hf.1], ?_, ?_⟩
    · intro z u hz
      have hzv : z ≠ v := by intro h; simp [g, h] at hz
      have hz' : f z = some u := by simpa [g, hzv] using hz
      have huv : u ≠ v := by intro h; exact hleaf z (h ▸ hz')
      have hp := hf.2.1 z u hz'
      exact ⟨hp.1, hp.2.1, hp.2.2.imp_right (by simpa [g, huv])⟩
    · intro z hz hr
      have hzv : z ≠ v := by intro h; exact hD (h ▸ hz)
      simpa [g, hzv] using hf.2.2 z hz hr
  have heq : support g = (support f).erase v := by
    ext z
    by_cases hz : z = v <;> simp [support, g, hz, eq_comm]
  have hlt : (support g).card < (support f).card := by
    rw [heq]
    exact card_erase_lt_of_mem (by simp [support, hv])
  exact hlt.not_ge (hmin g hvalid)

/-- The actual undirected graph determined by the parent pointers. -/
def treeGraph {G : SimpleGraph V} {s : V} {D : Finset V}
    {f : V → Option V} (hf : Valid G s D f) : SimpleGraph V where
  Adj u v := f v = some u ∨ f u = some v
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun v h => by
    have he : f v = some v := h.elim id id
    have hd := (hf.2.1 v v he).2.1
    omega⟩

theorem treeGraph_le {G : SimpleGraph V} {s : V} {D : Finset V}
    {f : V → Option V} (hf : Valid G s D f) : treeGraph hf ≤ G := by
  intro u v h
  exact h.elim (fun h => (hf.2.1 v u h).1) (fun h => (hf.2.1 u v h).1.symm)

/-- Every selected vertex is connected to the root by an actual shortest walk. -/
theorem tree_walk {G : SimpleGraph V} {s : V} {D : Finset V}
    {f : V → Option V} (hf : Valid G s D f) (v : V)
    (hv : v = s ∨ f v ≠ none) :
    ∃ p : (treeGraph hf).Walk s v, p.length = G.dist s v := by
  generalize hd : G.dist s v = d
  induction d using Nat.strong_induction_on generalizing v with
  | h d ih =>
    rcases hv with rfl | hv
    · exact ⟨.nil, by simpa using hd⟩
    · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hv
      have hp := hf.2.1 v u hu
      obtain ⟨p, hlen⟩ := ih (G.dist s u) (by omega) u hp.2.2 rfl
      have hedge : (treeGraph hf).Adj u v := Or.inl hu
      refine ⟨p.concat hedge, ?_⟩
      rw [Walk.length_concat, hlen]
      omega

theorem tree_preserves {G : SimpleGraph V} {s : V} {D : Finset V}
    {f : V → Option V} (hf : Valid G s D f) {v : V} (hv : v ∈ D) :
    (treeGraph hf).edist s v = G.edist s v := by
  apply le_antisymm _ (edist_anti (treeGraph_le hf))
  by_cases hr : G.Reachable s v
  · obtain ⟨p, hp⟩ := tree_walk hf v (hf.2.2 v hv hr)
    exact p.edist_le.trans_eq (by rw [hp, hr.coe_dist_eq_edist])
  · simp [edist_eq_top_of_not_reachable hr]

/-- Nonbranching edges of the optimizer instantiate the earlier induced-matching lemma. -/
def lazyEdges {G : SimpleGraph V} {s : V} {D : Finset V}
    {f : V → Option V} (hf : Valid G s D f)
    (hmin : ∀ g, Valid G s D g → (support g).card = (support f).card →
      (singles f).card ≤ (singles g).card) : LazyEdges V G.Adj (G.dist s) where
  symmetric _ _ h := h.symm
  edge u v := f v = some u ∧ Single f u
  adjacent _ _ h := (hf.2.1 _ _ h.1).1
  increases _ _ h := (hf.2.1 _ _ h.1).2.1
  child_unique u v w hv hw := by
    obtain ⟨z, hz, hu⟩ := hv.2
    exact (hu v hv.1).trans (hu w hw.1).symm
  parent_unique u v w hu hv := Option.some.inj (hu.1.symm.trans hv.1)
  lazy u v u' v' he he' hne hd :=
    optimal_lazy G s D f hf hmin he.1 he'.1 he.2 he'.2 hne hd
  lipschitz u v h := by
    have hd := h.diff_dist_adj (u := s)
    omega

/-- Lemma 5 with real shortest-distance semantics, plus the exact interface
used in Lemma 6. Leaves are a subset of demand endpoints, as needed by the
proof (not necessarily equal: an endpoint can be internal to another path). -/
theorem exists_lazy_tree (G : SimpleGraph V) (s : V) (D : Finset V) :
    ∃ f, ∃ hf : Valid G s D f,
      (∀ v, f v ≠ none → (∀ z, f z ≠ some v) → v ∈ D) ∧
      (∀ v ∈ D, (treeGraph hf).edist s v = G.edist s v) ∧
      ∃ T : LazyEdges V G.Adj (G.dist s),
        ∀ u v, T.edge u v ↔ f v = some u ∧ Single f u := by
  obtain ⟨f, hf, hmin, hmin'⟩ := exists_optimal G s D
  exact ⟨f, hf, fun _ => optimal_leaves G s D f hf hmin,
    fun _ hv => tree_preserves hf hv, lazyEdges hf hmin', fun _ _ => Iff.rfl⟩

end LazyTreeSelection
end LinearDistancePreservers
