import OnlineReachabilityPreservers.Bridges

/-! The ordered intersections in Appendix A for a system with a common vertex order. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [LinearOrder I]

/-- Each path lists its selected vertices in the common order. -/
def PathBefore (paths : I → Finset V) (i : I) (x y : V) : Prop :=
  x ∈ paths i ∧ y ∈ paths i ∧ x < y

/-- The vertices strictly preceding the indicated vertex in a path. -/
def predecessors (s : Finset V) (y : V) : Finset V :=
  s.filter (· < y)

theorem predecessor_count_mono (s : Finset V) : Monotone (fun y => (predecessors s y).card) := by
  intro x y hxy
  apply card_le_card
  intro v hv
  obtain ⟨hvs, hlt⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨hvs, hlt.trans_le hxy⟩

theorem predecessor_count_strict {s : Finset V} {x y : V} (hx : x ∈ s) (hxy : x < y) :
    (predecessors s x).card < (predecessors s y).card := by
  apply card_lt_card
  rw [ssubset_iff_subset_ne]
  constructor
  · intro v hv
    obtain ⟨hvs, hlt⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨hvs, hlt.trans hxy⟩
  · intro eq
    have h : x ∈ predecessors s y := mem_filter.mpr ⟨hx, hxy⟩
    rw [← eq] at h
    exact lt_irrefl _ (mem_filter.mp h).2

theorem predecessor_count_injective (s : Finset V) :
    Set.InjOn (fun x => (predecessors s x).card) s :=
  (show StrictMonoOn (fun x => (predecessors s x).card) s from
    fun _ hx _ _ h => predecessor_count_strict hx h).injOn

/-- Definition 2. In the bridge representation its size is `k + 2`. -/
def HalfBridgeFree (before : I → V → V → Prop) (size : ℕ) : Prop :=
  ∀ ⦃k⦄, k + 2 ≤ size → ∀ b : Bridge before k, ¬ b.arc (Fin.last k) < b.river

/-- Full bridge-freeness used in Appendix B. -/
def BridgeFree (before : I → V → V → Prop) (size : ℕ) : Prop :=
  ∀ ⦃k⦄, k + 2 ≤ size → IsEmpty (Bridge before k)

omit [LinearOrder V] in
theorem BridgeFree.halfFree {before : I → V → V → Prop} {size : ℕ}
    (free : BridgeFree before size) : HalfBridgeFree before size :=
  fun _ h b => (free h).false b |>.elim

theorem HalfBridgeFree.restrict_paths {paths : I → Finset V} {size : ℕ}
    (free : HalfBridgeFree (PathBefore paths) size) (J : Finset I) :
    HalfBridgeFree (PathBefore fun j : J => paths j.val) size := by
  intro k hk b earlier
  let c : Bridge (PathBefore paths) k :=
    b.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ h => h)
  exact free hk c earlier

private def orderedBridge {paths : I → Finset V} {k : ℕ}
    (v : Fin (k + 2) → V) (a : Fin (k + 1) → I) (r : I)
    (ha : Function.Injective a) (hr : ∀ i, r ≠ a i)
    (river : PathBefore paths r (v 0) (v (Fin.last (k + 1))))
    (step : ∀ i, PathBefore paths (a i) (v i.castSucc) (v i.succ)) :
    Bridge (PathBefore paths) k where
  vertex := v
  arc := a
  river := r
  distinctVertices := (Fin.strictMono_iff_lt_succ.mpr fun i => (step i).2.2).injective
  distinctArcs := ha
  river_ne_arc := hr
  riverStep := river
  arcStep := step

omit [LinearOrder I] in
theorem BridgeFree.no_three {paths : I → Finset V} {size : ℕ}
    (free : BridgeFree (PathBefore paths) size) (hsize : 3 ≤ size)
    {a b r : I} {x y z : V} (ab : a ≠ b) (ra : r ≠ a) (rb : r ≠ b)
    (arc₁ : PathBefore paths a x y) (arc₂ : PathBefore paths b y z)
    (river : PathBefore paths r x z) : False := by
  let bridge : Bridge (PathBefore paths) 1 :=
    orderedBridge ![x, y, z] ![a, b] r (by
      intro i j eq
      fin_cases i <;> fin_cases j
      · rfl
      · exact (ab eq).elim
      · exact (ab.symm eq).elim
      · rfl) (by intro i; fin_cases i; exacts [ra, rb]) river (by
        intro i; fin_cases i; exacts [arc₁, arc₂])
  exact (free hsize).false bridge

/-- In a common vertex order, the half-2-bridge exclusion makes intersections unique. -/
theorem path_intersection_unique {paths : I → Finset V} {size : ℕ}
    (hsize : 2 ≤ size) (free : HalfBridgeFree (PathBefore paths) size)
    {i j : I} (hne : i ≠ j) {x y : V}
    (hxi : x ∈ paths i) (hxj : x ∈ paths j) (hyi : y ∈ paths i) (hyj : y ∈ paths j) :
    x = y := by
  have conflict {a r : I} {u v : V} (hlt : a < r)
      (arc : PathBefore paths a u v) (river : PathBefore paths r u v) : False := by
    let b : Bridge (PathBefore paths) 0 :=
      orderedBridge ![u, v] ![a] r (by intro x y _; fin_cases x; fin_cases y; rfl)
        (fun i => by fin_cases i; exact hlt.ne') river (by intro i; fin_cases i; exact arc)
    exact free hsize b hlt
  rcases lt_trichotomy x y with hxy | eq | hyx
  · rcases lt_or_gt_of_ne hne with hij | hji
    · exact (conflict hij ⟨hxi, hyi, hxy⟩ ⟨hxj, hyj, hxy⟩).elim
    · exact (conflict hji ⟨hxj, hyj, hxy⟩ ⟨hxi, hyi, hxy⟩).elim
  · exact eq
  · rcases lt_or_gt_of_ne hne with hij | hji
    · exact (conflict hij ⟨hyi, hxi, hyx⟩ ⟨hyj, hxj, hyx⟩).elim
    · exact (conflict hji ⟨hyj, hxj, hyx⟩ ⟨hyi, hxi, hyx⟩).elim

/-- A witnessed element of `R(left, right)` in Definition 3.
The two outer paths are distinct, as required for an ordered pair of distinct intersections. -/
structure IntersectionChain (paths : I → Finset V) (left middle right : I) (x y : V) : Prop where
  left_ne_middle : left ≠ middle
  left_ne_right : left ≠ right
  right_earlier : right < middle
  on_left : x ∈ paths left
  on_right : y ∈ paths right
  middle_step : PathBefore paths middle x y

/-- In Lemma 24, distinct middle paths have distinct left intersections. -/
theorem lemma24_left_injective {paths : I → Finset V}
    (free : HalfBridgeFree (PathBefore paths) 4) {l a b r : I} {x ya yb : V}
    (ha : IntersectionChain paths l a r x ya) (hb : IntersectionChain paths l b r x yb) :
    a = b := by
  have conflict {a b : I} {ya yb : V}
      (ha : IntersectionChain paths l a r x ya) (hb : IntersectionChain paths l b r x yb)
      (hne : a ≠ b) (hy : ya < yb) : False := by
    obtain ⟨_, _, har, _, hay, arc⟩ := ha
    obtain ⟨_, _, hbr, _, hby, river⟩ := hb
    let bridge : Bridge (PathBefore paths) 1 :=
      orderedBridge ![x, ya, yb] ![a, r] b (by
        intro i j eq
        fin_cases i <;> fin_cases j
        · rfl
        · exact (har.ne' eq).elim
        · exact (har.ne eq).elim
        · rfl) (by intro i; fin_cases i; exacts [hne.symm, hbr.ne']) river (by
          intro i
          fin_cases i
          · exact arc
          · exact ⟨hay, hby, hy⟩)
    exact free (by decide) bridge hbr
  by_contra hne
  rcases lt_trichotomy ya yb with hab | rfl | hba
  · exact conflict ha hb hne hab
  · have eq := path_intersection_unique (by decide) free hne
      ha.middle_step.1 hb.middle_step.1 ha.middle_step.2.1 hb.middle_step.2.1
    exact ha.middle_step.2.2.ne eq
  · exact conflict hb ha (fun eq => hne eq.symm) hba

/-- The order of the left intersections is weakly monotone at the right intersections. -/
theorem lemma24_right_monotone {paths : I → Finset V}
    (free : HalfBridgeFree (PathBefore paths) 4) {l a b r : I} {xa xb ya yb : V}
    (ha : IntersectionChain paths l a r xa ya) (hb : IntersectionChain paths l b r xb yb)
    (hx : xa < xb) : ya ≤ yb := by
  by_contra! hy
  obtain ⟨hla, hlr, har, hxa, hya, river⟩ := ha
  obtain ⟨hlb, _, hbr, hxb, hyb, middle⟩ := hb
  have hab : a ≠ b := by
    intro eq
    subst b
    exact hx.ne (path_intersection_unique (by decide) free hla hxa river.1 hxb middle.1)
  let bridge : Bridge (PathBefore paths) 2 :=
    orderedBridge ![xa, xb, yb, ya] ![l, b, r] a (by
      intro i j eq
      fin_cases i <;> fin_cases j
      · rfl
      · exact (hlb eq).elim
      · exact (hlr eq).elim
      · exact (hlb.symm eq).elim
      · rfl
      · exact (hbr.ne' eq).elim
      · exact (hlr.symm eq).elim
      · exact (hbr.ne eq).elim
      · rfl) (by intro i; fin_cases i; exacts [hla.symm, hab, har.ne']) river (by
        intro i
        fin_cases i
        · exact ⟨hxa, hxb, hx⟩
        · exact middle
        · exact ⟨hyb, hya, hy⟩)
  exact free (by decide) bridge har

/-- Appendix B strengthens the right order to strict order when every bridge is forbidden. -/
theorem lemma24_right_strict {paths : I → Finset V}
    (free : BridgeFree (PathBefore paths) 4) {l a b r : I} {xa xb ya yb : V}
    (ha : IntersectionChain paths l a r xa ya) (hb : IntersectionChain paths l b r xb yb)
    (hx : xa < xb) : ya < yb := by
  apply (lemma24_right_monotone free.halfFree ha hb hx).lt_of_ne
  rintro rfl
  have hab : a ≠ b := fun eq => hx.ne (path_intersection_unique (by decide) free.halfFree
    ha.left_ne_middle ha.on_left ha.middle_step.1 hb.on_left (eq.symm ▸ hb.middle_step.1))
  exact free.no_three (by decide) hb.left_ne_middle ha.left_ne_middle.symm hab
    ⟨ha.on_left, hb.on_left, hx⟩ hb.middle_step ha.middle_step

section TopologicalOrder

variable [Fintype V]

/-- Break ties in decreasing reach rank using the vertex order. -/
def reverseTopologicalKey (G : Arcs V) (x : V) : (ℕ ×ₗ V)ᵒᵈ :=
  OrderDual.toDual (toLex ((reaches G x).card, x))

noncomputable def topologicalEquiv (G : Arcs V) : V ≃ Set.range (reverseTopologicalKey G) :=
  Equiv.ofInjective (reverseTopologicalKey G) fun _ _ eq =>
    congrArg (fun a => (ofLex (OrderDual.ofDual a)).2) eq

/-- Represent a family by finsets on the same vertices in reverse topological order. -/
noncomputable def topologicalPaths (G : Arcs V) (paths : I → Finset V)
    (i : I) : Finset (Set.range (reverseTopologicalKey G)) :=
  (paths i).map (topologicalEquiv G).toEmbedding

omit [LinearOrder I] in
theorem topologicalPaths_step {G : Arcs V} (dag : IsDAG G) {paths : I → Finset V}
    (total : ∀ i {u v}, u ∈ paths i → v ∈ paths i → u ≠ v →
      BeforeIn G (paths i) u v ∨ BeforeIn G (paths i) v u)
    {i : I} {x y : Set.range (reverseTopologicalKey G)}
    (h : PathBefore (topologicalPaths G paths) i x y) :
    BeforeIn G (paths i) ((topologicalEquiv G).symm y) ((topologicalEquiv G).symm x) := by
  obtain ⟨hx, hy, hlt⟩ := h
  obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
  change (topologicalEquiv G u) < (topologicalEquiv G v) at hlt
  have hne : v ≠ u := fun eq => hlt.ne (congrArg (topologicalEquiv G) eq.symm)
  simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
  rcases total i hv hu hne with h | h
  · exact h
  · have hf : (toLex ((reaches G u).card, u)) < toLex ((reaches G v).card, v) :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl (h.rank_lt dag))
    exact (lt_asymm hf hlt).elim

end TopologicalOrder

variable [Fintype V] [Fintype I]

/-- Keep the two intersection vertices to make the finite counts explicit. -/
noncomputable def rWitnesses (paths : I → Finset V) (l r : I) : Finset (I × V × V) := by
  classical
  exact univ.filter fun w => IntersectionChain paths l w.1 r w.2.1 w.2.2

theorem mem_rWitnesses {paths : I → Finset V} {l r : I} {w : I × V × V} :
    w ∈ rWitnesses paths l r ↔ IntersectionChain paths l w.1 r w.2.1 w.2.2 := by
  classical
  simp [rWitnesses]

theorem rWitnesses_left_injective {paths : I → Finset V}
    (free : HalfBridgeFree (PathBefore paths) 4) (l r : I) :
    Set.InjOn (fun (w : I × V × V) => w.2.1) (rWitnesses paths l r) := by
  rintro ⟨a, x, y⟩ ha ⟨b, x', y'⟩ hb eq
  change x = x' at eq
  subst x'
  obtain ha := mem_rWitnesses.mp ha
  obtain hb := mem_rWitnesses.mp hb
  obtain rfl := lemma24_left_injective free ha hb
  obtain rfl := path_intersection_unique (by decide) free ha.right_earlier.ne
    ha.on_right ha.middle_step.2.1 hb.on_right hb.middle_step.2.1
  rfl

theorem lemma24_fiber_card {paths : I → Finset V}
    (free : HalfBridgeFree (PathBefore paths) 4) (l r : I) :
    (rWitnesses paths l r).card ≤ (paths l).card :=
  card_le_card_of_injOn (fun w => w.2.1) (fun _ hw => (mem_rWitnesses.mp hw).on_left)
    (rWitnesses_left_injective free l r)

/-- Definition 3 with explicit witnesses, unique under the half-2-bridge exclusion. -/
noncomputable def rChains (paths : I → Finset V) : Finset ((I × I) × (I × V × V)) := by
  classical
  exact univ.biUnion fun lr : I × I => (rWitnesses paths lr.1 lr.2).image (Prod.mk lr)

theorem mem_rChains {paths : I → Finset V} {w : (I × I) × (I × V × V)} :
    w ∈ rChains paths ↔ IntersectionChain paths w.1.1 w.2.1 w.1.2 w.2.2.1 w.2.2.2 := by
  classical
  rcases w with ⟨lr, w⟩
  simp [rChains, mem_rWitnesses]

theorem rChains_card (paths : I → Finset V) :
    (rChains paths).card = ∑ lr : I × I, (rWitnesses paths lr.1 lr.2).card := by
  classical
  unfold rChains
  rw [card_biUnion]
  · apply sum_congr rfl
    intro lr _
    exact card_image_of_injective _ fun _ _ e => congrArg Prod.snd e
  · intro lr _ lr' _ hne
    apply disjoint_left.mpr
    intro w h1 h2
    obtain ⟨v, _, rfl⟩ := mem_image.mp h1
    obtain ⟨v', _, eq⟩ := mem_image.mp h2
    exact hne (congrArg Prod.fst eq).symm

theorem rChains_upper {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4) :
    (rChains paths).card ≤ Fintype.card I * ∑ l, (paths l).card := by
  rw [rChains_card]
  calc
    _ ≤ ∑ lr : I × I, (paths lr.1).card :=
      sum_le_sum fun lr _ => lemma24_fiber_card free lr.1 lr.2
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [mul_sum]

end OnlineReachabilityPreservers
