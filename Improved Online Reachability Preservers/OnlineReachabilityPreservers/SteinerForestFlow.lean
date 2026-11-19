import OnlineReachabilityPreservers.SteinerForestNetwork

/-! Unit flows on the paired forest supply terminal mass on both sides of
each root. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} {height : ℕ} [LinearOrder V] [Fintype V]

local instance : DecidableEq (ForestNetworkVertex V height) :=
  (inferInstance : LinearOrder (ForestNetworkVertex V height)).toDecidableEq

/-- The directed graph of one request with a prescribed set of metric links. -/
def forestRequestGraph (links : Arcs (HeightForestVertex V height)) (d : V × V) :
    Arcs (ForestNetworkVertex V height) :=
  links.map (forestNetworkCopy.prodMap forestNetworkCopy) ∪ forestNetworkEntries d.1 ∪ forestNetworkExits d.2

omit [LinearOrder V] [Fintype V] in
private theorem forestNetworkCopy_ne_source (a : HeightForestVertex V height) (s : V) :
    forestNetworkCopy a ≠ forestNetworkSource s := by
  intro h
  have eq := congrArg (fun b => (ofLex b).1.val) h
  change 0 = 1 at eq
  contradiction

omit [LinearOrder V] [Fintype V] in
private theorem forestNetworkCopy_ne_sink (a : HeightForestVertex V height) (t : V) :
    forestNetworkCopy a ≠ forestNetworkSink t := by
  intro h
  have eq := congrArg (fun b => (ofLex b).1.val) h
  change 0 = 2 at eq
  contradiction

private theorem forestRequestGraph_fromCopy {links : Arcs (HeightForestVertex V height)} {d : V × V}
    {a : HeightForestVertex V height} {b : ForestNetworkVertex V height}
    (edge : Edge (forestRequestGraph links d) (forestNetworkCopy a) b) :
    (∃ c, Edge links a c ∧ b = forestNetworkCopy c) ∨ (b = forestNetworkSink d.2 ∧ sinkLeaf d.2 a) := by
  rcases mem_union.mp edge with left | exit
  · rcases mem_union.mp left with internal | entry
    · obtain ⟨⟨u, v⟩, present, eq⟩ := mem_map.mp internal
      obtain ⟨first, second⟩ := Prod.mk.inj eq
      have same : u = a := forestNetworkCopy.injective first
      exact Or.inl ⟨v, same ▸ present, second.symm⟩
    · obtain ⟨u, _, eq⟩ := mem_image.mp entry
      exact (forestNetworkCopy_ne_source a d.1 (congrArg Prod.fst eq).symm).elim
  · obtain ⟨v, present, eq⟩ := mem_image.mp exit
    obtain ⟨first, second⟩ := Prod.mk.inj eq
    have same : v = a := forestNetworkCopy.injective first
    exact Or.inr ⟨second.symm, same ▸ (mem_filter.mp present).2⟩

private theorem forestRequestGraph_fromSource {links : Arcs (HeightForestVertex V height)} {d : V × V}
    {b : ForestNetworkVertex V height}
    (edge : Edge (forestRequestGraph links d) (forestNetworkSource d.1) b) :
    ∃ a : HeightForestVertex V height, sourceLeaf d.1 a ∧ b = forestNetworkCopy a := by
  rcases mem_union.mp edge with left | exit
  · rcases mem_union.mp left with internal | entry
    · obtain ⟨⟨u, v⟩, _, eq⟩ := mem_map.mp internal
      exact (forestNetworkCopy_ne_source u d.1 (congrArg Prod.fst eq)).elim
    · obtain ⟨u, present, eq⟩ := mem_image.mp entry
      exact ⟨u, (mem_filter.mp present).2, (congrArg Prod.snd eq).symm⟩
  · obtain ⟨a, _, eq⟩ := mem_image.mp exit
    exact (forestNetworkCopy_ne_source a d.1 (congrArg Prod.fst eq)).elim

private theorem forestRequestGraph_untilExit {links : Arcs (HeightForestVertex V height)} {d : V × V}
    {a : HeightForestVertex V height} {p : List (ForestNetworkVertex V height × ForestNetworkVertex V height)}
    (walk : Walk (forestRequestGraph links d) (forestNetworkCopy a) (forestNetworkSink d.2) p) :
    ∃ b middle, sinkLeaf d.2 b ∧ Walk links a b middle ∧
      ∀ e ∈ middle, forestNetworkCopy.prodMap forestNetworkCopy e ∈ p := by
  induction p generalizing a with
  | nil =>
    exact (forestNetworkCopy_ne_sink a d.2 (by simpa using walk.vertex_list)).elim
  | cons edge rest ih =>
    cases walk with
    | @cons _ next _ _ step later =>
      rcases forestRequestGraph_fromCopy step with ⟨v, transfer, rfl⟩ | ⟨_, finish⟩
      · obtain ⟨b, middle, last, tail, includes⟩ := ih later
        refine ⟨b, (a, v) :: middle, last, .cons transfer tail, ?_⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (includes e h)
      · exact ⟨a, [], finish, .nil _, by simp⟩

/-- A request path projects to a walk between its two leaf groups. All
projected links occurred on the original request path. -/
theorem forestRequestGraph_walk {links : Arcs (HeightForestVertex V height)} {d : V × V}
    {p : List (ForestNetworkVertex V height × ForestNetworkVertex V height)}
    (walk : Walk (forestRequestGraph links d) (forestNetworkSource d.1) (forestNetworkSink d.2) p) :
    ∃ a b middle, sourceLeaf d.1 a ∧ sinkLeaf d.2 b ∧ Walk links a b middle ∧
      ∀ e ∈ middle, forestNetworkCopy.prodMap forestNetworkCopy e ∈ p := by
  cases p with
  | nil => exact (forestNetworkSource_ne_sink d.1 d.2 (by simpa using walk.vertex_list)).elim
  | cons edge rest =>
    cases walk with
    | @cons _ next _ _ step later =>
      obtain ⟨a, start, rfl⟩ := forestRequestGraph_fromSource step
      obtain ⟨b, middle, finish, middleWalk, includes⟩ := forestRequestGraph_untilExit later
      exact ⟨a, b, middle, start, finish, middleWalk,
        fun e he => List.mem_cons_of_mem _ (includes e he)⟩

theorem forestNetworkCapacity_support (G : Arcs V) (d : V × V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ) :
    positiveFlowArcs (weightedNetworkCapacity (forestNetworkPriced G (heightForest G height))
      (forestNetworkDemand G height d) (forestNetworkWeight G) charges scale) ⊆
        forestRequestGraph (heightForest G height) d := by
  intro e he
  have pos := (mem_filter.mp he).2
  have fromForest {f : HeightForestVertex V height × HeightForestVertex V height}
      (present : f ∈ heightForest G height) :
      forestNetworkCopy.prodMap forestNetworkCopy f ∈ forestRequestGraph (heightForest G height) d :=
    mem_union_left _ (mem_union_left _ (mem_map_of_mem _ present))
  rw [weightedNetworkCapacity] at pos
  split at pos
  · rename_i free
    rcases mem_union.mp free with l | exit
    · rcases mem_union.mp l with hzero | entry
      · obtain ⟨a, ha, rfl⟩ := mem_map.mp hzero
        exact fromForest (mem_filter.mp ha).1
      · exact mem_union_left _ (mem_union_right _ entry)
    · exact mem_union_right _ exit
  · split at pos
    · rename_i priced
      obtain ⟨a, ha, rfl⟩ := mem_map.mp priced
      exact fromForest (mem_filter.mp ha).1
    · omega

omit [LinearOrder V] [Fintype V] in
private theorem heightCopy_eta (a : HeightForestVertex V height) :
    heightCopy (heightForestRoot a) (heightForestSide a) (heightForestHistory a) = a := by
  rfl

private theorem heightForest_left_step {G : Arcs V} {r : V}
    {a : HeightNode V height} {v : HeightForestVertex V height}
    (edge : Edge (heightForest G height) (heightCopy r false a) v) :
    (∃ b, Edge (inwardHeightTree G r height) a b ∧ v = heightCopy r false b) ∨
      (a = heightRoot ∧ v = heightCopy r true heightRoot) := by
  obtain ⟨root, _, here⟩ := mem_biUnion.mp edge
  rcases mem_union.mp here with side | center
  · rcases mem_union.mp side with first | second
    · obtain ⟨⟨x, y⟩, present, eq⟩ := mem_map.mp first
      obtain ⟨start, finish⟩ := Prod.mk.inj eq
      have same : root = r := congrArg heightForestRoot start
      have node : x = a := congrArg heightForestHistory start
      subst root x
      exact Or.inl ⟨y, present, finish.symm⟩
    · obtain ⟨⟨x, y⟩, _, eq⟩ := mem_map.mp second
      have wrong : true = false := congrArg heightForestSide (congrArg Prod.fst eq)
      contradiction
  · obtain ⟨start, finish⟩ := Prod.mk.inj (mem_singleton.mp center)
    have same : r = root := congrArg heightForestRoot start
    have atRoot : a = heightRoot := congrArg heightForestHistory start
    exact Or.inr ⟨atRoot, finish.trans (congrArg (fun q => heightCopy q true heightRoot) same.symm)⟩

private theorem heightForest_right_step {G : Arcs V} {r : V}
    {a : HeightNode V height} {v : HeightForestVertex V height}
    (edge : Edge (heightForest G height) (heightCopy r true a) v) :
    ∃ b, Edge (reverseArcs (inwardHeightTree (reverseArcs G) r height)) a b ∧ v = heightCopy r true b := by
  obtain ⟨root, _, here⟩ := mem_biUnion.mp edge
  rcases mem_union.mp here with side | center
  · rcases mem_union.mp side with first | second
    · obtain ⟨⟨x, y⟩, _, eq⟩ := mem_map.mp first
      have wrong : false = true := congrArg heightForestSide (congrArg Prod.fst eq)
      contradiction
    · obtain ⟨⟨x, y⟩, present, eq⟩ := mem_map.mp second
      obtain ⟨start, finish⟩ := Prod.mk.inj eq
      have same : root = r := congrArg heightForestRoot start
      have node : x = a := congrArg heightForestHistory start
      subst root x
      exact ⟨y, present, finish.symm⟩
  · have wrong : true = false := congrArg heightForestSide (congrArg Prod.fst (mem_singleton.mp center))
    contradiction

private theorem heightForestWalk_right {G : Arcs V} {r : V} {a : HeightNode V height}
    {v : HeightForestVertex V height} {p : List (HeightForestVertex V height × HeightForestVertex V height)}
    (walk : Walk (heightForest G height) (heightCopy r true a) v p) :
    ∃ b right, v = heightCopy r true b ∧
      Walk (reverseArcs (inwardHeightTree (reverseArcs G) r height)) a b right ∧
      ∀ e ∈ right, (heightCopy r true).prodMap (heightCopy r true) e ∈ p := by
  induction p generalizing a with
  | nil =>
    cases walk
    exact ⟨a, [], rfl, .nil _, by simp⟩
  | cons edge rest ih =>
    cases walk with
    | @cons _ next _ _ step later =>
      obtain ⟨b, transfer, rfl⟩ := heightForest_right_step step
      obtain ⟨c, right, finish, tail, includes⟩ := ih later
      refine ⟨c, (a, b) :: right, finish, .cons transfer tail, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | member
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (includes e member)

private theorem heightForestWalk_legs {G : Arcs V} {r : V} {a : HeightNode V height}
    {v : HeightForestVertex V height} {p : List (HeightForestVertex V height × HeightForestVertex V height)}
    (walk : Walk (heightForest G height) (heightCopy r false a) v p)
    (side : heightForestSide v = true) :
    ∃ b left right, v = heightCopy r true b ∧
      Walk (inwardHeightTree G r height) a heightRoot left ∧
      Walk (reverseArcs (inwardHeightTree (reverseArcs G) r height)) heightRoot b right ∧
      (∀ e ∈ left, (heightCopy r false).prodMap (heightCopy r false) e ∈ p) ∧
      (∀ e ∈ right, (heightCopy r true).prodMap (heightCopy r true) e ∈ p) := by
  induction p generalizing a with
  | nil =>
    cases walk
    simp at side
  | cons edge rest ih =>
    cases walk with
    | @cons _ next _ _ step later =>
      rcases heightForest_left_step step with ⟨b, transfer, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨c, left, right, finish, pre, post, preIn, postIn⟩ := ih later
        refine ⟨c, (a, b) :: left, right, finish, .cons transfer pre, post, ?_,
          fun e he => List.mem_cons_of_mem _ (postIn e he)⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | member
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (preIn e member)
      · obtain ⟨b, right, finish, tail, includes⟩ := heightForestWalk_right later
        exact ⟨b, [], right, finish, .nil _, tail, by simp,
          fun e he => List.mem_cons_of_mem _ (includes e he)⟩

private theorem inwardHeightWalk_has_ancestor {G : Arcs V} {r : V} {a u : HeightNode V height}
    {p : List (HeightNode V height × HeightNode V height)}
    (walk : Walk (inwardHeightTree G r height) a heightRoot p)
    (nonroot : u.val ≠ []) (ancestor : u.val <+: a.val) :
    (u, heightParent u) ∈ p := by
  induction p generalizing a with
  | nil =>
    cases walk
    exact (nonroot (List.prefix_nil.mp ancestor)).elim
  | cons e rest ih =>
    cases walk with
    | @cons _ b _ _ step later =>
      obtain ⟨_, _, rfl⟩ := inwardHeightTree_edge_iff.mp step
      by_cases same : u = a
      · subst u
        exact List.mem_cons_self
      · have shorter : u.val.length < a.val.length :=
          lt_of_le_of_ne ancestor.length_le (fun lengths => same (Subtype.ext (ancestor.eq_of_length_le lengths.ge)))
        have part : u.val <+: (heightParent a).val := by
          change _ <+: a.val.dropLast
          rw [List.dropLast_eq_take, List.prefix_take_iff]
          exact ⟨ancestor, Nat.le_sub_one_of_lt shorter⟩
        exact List.mem_cons_of_mem _ (ih later part)

def forestLegArc (r : V) (side : Bool) (u : HeightNode V height) :
    ForestNetworkVertex V height × ForestNetworkVertex V height :=
  if side then (forestNetworkCopy (heightCopy r true (heightParent u)), forestNetworkCopy (heightCopy r true u))
  else (forestNetworkCopy (heightCopy r false u), forestNetworkCopy (heightCopy r false (heightParent u)))

/-- A unit route assigns one source leaf and one sink leaf to the same
root, and uses the two metric ancestor chains. -/
structure ForestRouteWitness (d : V × V)
    (p : List (ForestNetworkVertex V height × ForestNetworkVertex V height)) where
  root : V
  left : HeightNode V height
  right : HeightNode V height
  left_leaf : sourceLeaf d.1 (heightCopy root false left)
  right_leaf : sinkLeaf d.2 (heightCopy root true right)
  left_chain : ∀ u : HeightNode V height, u.val ≠ [] → u.val <+: left.val → forestLegArc root false u ∈ p
  right_chain : ∀ u : HeightNode V height, u.val ≠ [] → u.val <+: right.val → forestLegArc root true u ∈ p

theorem forestRequestGraph_route {G : Arcs V} {d : V × V}
    {p : List (ForestNetworkVertex V height × ForestNetworkVertex V height)}
    (walk : Walk (forestRequestGraph (heightForest G height) d) (forestNetworkSource d.1) (forestNetworkSink d.2) p) :
    Nonempty (ForestRouteWitness d p) := by
  obtain ⟨a, b, middle, start, finish, route, includes⟩ := forestRequestGraph_walk walk
  let r := heightForestRoot a
  let u := heightForestHistory a
  have eq : heightCopy r false u = a := by
    change heightCopy (heightForestRoot a) false (heightForestHistory a) = a
    rw [← start.1, heightCopy_eta]
  have middleWalk := eq.symm ▸ route
  obtain ⟨v, left, right, rfl, lWalk, rWalk, lIn, rIn⟩ := heightForestWalk_legs middleWalk finish.1
  refine ⟨⟨r, u, v, eq.symm ▸ start, finish, ?_, ?_⟩⟩
  · intro node nonroot ancestor
    have member := inwardHeightWalk_has_ancestor lWalk nonroot ancestor
    exact includes _ (lIn _ member)
  · intro node nonroot ancestor
    have reverse : Walk (inwardHeightTree (reverseArcs G) r height) v heightRoot
        (right.reverse.map Prod.swap) := by simpa using rWalk.reverse
    have member := inwardHeightWalk_has_ancestor reverse nonroot ancestor
    obtain ⟨edge, fromRight, equal⟩ := List.mem_map.mp member
    have arc : edge = (heightParent node, node) := by
      apply Prod.swap_injective
      simpa using equal
    exact includes _ (rIn _ (arc ▸ (List.mem_reverse.mp fromRight)))

private theorem card_filter_list_indices {A : Type*} (l : List A) (P : A → Prop) [DecidablePred P] :
    ((univ : Finset (Fin l.length)).filter (fun i => P (l.get i))).card =
      (l.filter (fun a => decide (P a))).length := by
  have enumeration : (List.finRange l.length).toFinset = (univ : Finset (Fin l.length)) := by
    ext i
    simp
  rw [← enumeration, (List.nodup_finRange _).card_eq_countP, List.countP_eq_length_filter]
  have lengths := congrArg List.length (List.filter_map (l := List.finRange l.length)
    (f := l.get) (p := fun a => decide (P a)))
  rw [← List.ofFn_eq_map, List.ofFn_get, List.length_map] at lengths
  exact lengths.symm


/-- The total supplies in the two terminal groups agree root by root. An
ancestor's descendant supply is bounded by its directed metric arc. -/
structure ForestLeafLoads (d : V × V) (scale : ℕ) (capacity : ArcFlow (ForestNetworkVertex V height)) where
  rootUnits : V → ℕ
  leafUnits : V → Bool → HeightNode V height → ℕ
  root_total : ∑ r, rootUnits r = scale
  leaf_total : ∀ r side, ∑ a, leafUnits r side a = rootUnits r
  leaf_valid : ∀ r side a, 0 < leafUnits r side a →
    if side then sinkLeaf d.2 (heightCopy r true a) else sourceLeaf d.1 (heightCopy r false a)
  ancestor_bound : ∀ r side (u : HeightNode V height), u.val ≠ [] →
    (((∑ a ∈ univ.filter (fun a : HeightNode V height => u.val <+: a.val), leafUnits r side a) : ℕ) : ℤ) ≤
      capacity (forestLegArc r side u)

/-- A full request flow supplies equal terminal masses on both sides of
each root. Their total over all roots is the original integer supply. -/
theorem forestNetworkCovered_leafLoads (G : Arcs V) (d : V × V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ)
    (covered : weightedNetworkCovered (forestNetworkPriced G (heightForest G height))
      (forestNetworkDemand G height d) (forestNetworkWeight G) charges scale) :
    Nonempty (ForestLeafLoads d scale (weightedNetworkCapacity (forestNetworkPriced G (heightForest G height))
      (forestNetworkDemand G height d) (forestNetworkWeight G) charges scale)) := by
  classical
  let capacity := weightedNetworkCapacity (forestNetworkPriced G (heightForest G height))
    (forestNetworkDemand G height d) (forestNetworkWeight G) charges scale
  have nonneg := weightedNetworkCapacity_nonneg (forestNetworkPriced G (heightForest G height))
    (forestNetworkDemand G height d) (forestNetworkWeight G) charges scale
  obtain ⟨flow, valid⟩ := covered
  obtain ⟨paths, length, walks, uses⟩ := valid.decompose_capacity nonneg
  let I := Fin paths.length
  have supported : positiveFlowArcs flow ⊆ forestRequestGraph (heightForest G height) d := by
    intro e active
    have used := (mem_filter.mp active).2
    have allowed := used.trans_le (valid.upper e)
    exact forestNetworkCapacity_support G d charges scale (mem_filter.mpr ⟨mem_univ _, allowed⟩)
  have witness (i : I) : Nonempty (ForestRouteWitness d (paths.get i)) :=
    forestRequestGraph_route ((walks _ (List.get_mem _ _)).1.mono supported)
  let w := fun i => (witness i).some
  let atRoot := fun r => (univ : Finset I).filter (fun i => (w i).root = r)
  let terminal := fun (side : Bool) (i : I) => if side then (w i).right else (w i).left
  let rootCount := fun r => (atRoot r).card
  let leafCount := fun r side a => ((atRoot r).filter (fun i => terminal side i = a)).card
  have fiber (r) (side) (S : Finset (HeightNode V height)) :
      (∑ a ∈ S, leafCount r side a) = ((atRoot r).filter (fun i => terminal side i ∈ S)).card :=
    sum_card_fiberwise_eq_card_filter _ _ _
  refine ⟨⟨rootCount, leafCount, ?_, ?_, ?_, ?_⟩⟩
  · change (∑ r, ((univ : Finset I).filter (fun i => (w i).root = r)).card) = scale
    rw [← card_eq_sum_card_fiberwise (fun i _ => mem_univ (w i).root),
      card_univ, Fintype.card_fin, length]
  · intro r side
    rw [fiber]
    simp [rootCount]
  · intro r side a pos
    obtain ⟨i, present⟩ := card_pos.mp pos
    obtain ⟨hr, hTerminal⟩ := mem_filter.mp present
    have hr' : (w i).root = r := (mem_filter.mp hr).2
    cases side
    · change (w i).left = a at hTerminal
      change sourceLeaf d.1 (heightCopy r false a)
      simpa only [hr', hTerminal] using (w i).left_leaf
    · change (w i).right = a at hTerminal
      change sinkLeaf d.2 (heightCopy r true a)
      simpa only [hr', hTerminal] using (w i).right_leaf
  · intro r side u nonroot
    rw [fiber]
    let e := forestLegArc r side u
    have within : ((atRoot r).filter fun i => terminal side i ∈
        univ.filter (fun a : HeightNode V height => u.val <+: a.val)) ⊆
          (univ : Finset I).filter (fun i => e ∈ paths.get i) := by
      intro i present
      obtain ⟨hr, ht⟩ := mem_filter.mp present
      have hr' : (w i).root = r := (mem_filter.mp hr).2
      have part := (mem_filter.mp ht).2
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      cases side
      · change forestLegArc r false u ∈ paths.get i
        rw [← hr']
        exact (w i).left_chain u nonroot part
      · change forestLegArc r true u ∈ paths.get i
        rw [← hr']
        exact (w i).right_chain u nonroot part
    have count := card_le_card within
    have indexed := card_filter_list_indices paths (fun p => e ∈ p)
    have same : (paths.filter (fun p => @decide (e ∈ p) (Classical.propDecidable _))).length =
        arcUsage paths e := by
      unfold arcUsage
      apply congrArg List.length
      apply List.filter_congr
      intro p _
      by_cases present : e ∈ p <;> simp [present]
    have bound : _ ≤ arcUsage paths e := count.trans_eq (indexed.trans same)
    exact (show (_ : ℤ) ≤ (arcUsage paths e : ℤ) by exact_mod_cast bound).trans (uses e)

end OnlineReachabilityPreservers
