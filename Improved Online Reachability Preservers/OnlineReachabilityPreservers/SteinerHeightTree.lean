import Mathlib.Data.List.Chain
import Mathlib.Data.List.Lex
import OnlineReachabilityPreservers.SteinerHeightBlocks

/-! The finite inward metric tree used by the height reduction. -/

namespace OnlineReachabilityPreservers

open Finset

/-- A vertex of the height-reduced tree records its sequence of ancestor
labels after the root. -/
abbrev HeightNode (V : Type*) (height : ℕ) := {history : List V // history.length ≤ height}

private def heightNodeEquiv (V : Type*) (height : ℕ) :
    (Σ k : Fin (height + 1), Fin k.val → V) ≃ HeightNode V height where
  toFun s := ⟨List.ofFn s.2, by simpa using Nat.le_of_lt_succ s.1.isLt⟩
  invFun node := ⟨⟨node.val.length, Nat.lt_succ_of_le node.2⟩, node.val.get⟩
  left_inv := by
    intro s
    let forget (x : Σ k : Fin (height + 1), Fin k.val → V) : Σ n : ℕ, Fin n → V :=
      ⟨x.1.val, x.2⟩
    have injective : Function.Injective forget := by
      intro ⟨a, p⟩ ⟨b, q⟩ eq
      have same : a = b := Fin.ext (congrArg Sigma.fst eq)
      subst b
      have second : p = q := eq_of_heq ((Sigma.mk.inj_iff.mp eq).2)
      subst q
      rfl
    apply injective
    exact List.equivSigmaTuple.apply_symm_apply (forget s)
  right_inv := fun node => Subtype.ext (List.ofFn_get node.val)

instance {V : Type*} [Fintype V] (height : ℕ) : Fintype (HeightNode V height) :=
  Fintype.ofEquiv _ (heightNodeEquiv V height)

theorem heightNode_card (V : Type*) [Fintype V] (height : ℕ) :
    Fintype.card (HeightNode V height) = ∑ k : Fin (height + 1), Fintype.card V ^ k.val := by
  rw [← Fintype.card_congr (heightNodeEquiv V height), Fintype.card_sigma]
  simp

theorem heightNode_card_le (V : Type*) [Fintype V] [Nonempty V] (height : ℕ) :
    Fintype.card (HeightNode V height) ≤ (height + 1) * (Fintype.card V) ^ height := by
  rw [heightNode_card]
  calc
    _ ≤ ∑ _ : Fin (height + 1), (Fintype.card V) ^ height :=
      sum_le_sum fun i _ => Nat.pow_le_pow_right (Fintype.card_pos) (Nat.le_of_lt_succ i.isLt)
    _ = _ := by simp

variable {V : Type*} [LinearOrder V] [Fintype V] {height : ℕ}

def heightRoot : HeightNode V height := ⟨[], Nat.zero_le _⟩

def heightParent (node : HeightNode V height) : HeightNode V height :=
  ⟨node.val.dropLast, (List.dropLast_prefix node.val).length_le.trans node.2⟩

def heightLabel (root : V) (node : HeightNode V height) : V :=
  (root :: node.val).getLast (List.cons_ne_nil _ _)

omit [LinearOrder V] [Fintype V] in
@[simp]
theorem heightLabel_root (root : V) : heightLabel root (heightRoot : HeightNode V height) = root := rfl

omit [LinearOrder V] [Fintype V] in
theorem heightLabel_append (root : V) (history : List V) (vertex : V)
    (bound : (history ++ [vertex]).length ≤ height) :
    heightLabel root (⟨history ++ [vertex], bound⟩ : HeightNode V height) = vertex := by
  exact List.getLast_concat (l := root :: history)

/-- Each history must realize the transfers along its complete rootward chain. -/
def heightHistoryValid (G : Arcs V) (root : V) (node : HeightNode V height) : Prop :=
  (root :: node.val).IsChain fun a b => b ∈ reaches G a

instance (G : Arcs V) (root : V) (node : HeightNode V height) :
    Decidable (heightHistoryValid G root node) := by
  unfold heightHistoryValid
  infer_instance

def inwardHeightTree (G : Arcs V) (root : V) (height : ℕ) : Arcs (HeightNode V height) :=
  (univ.filter fun node => node.val ≠ [] ∧ heightHistoryValid G root node).image
    fun node => (node, heightParent node)

theorem inwardHeightTree_edge_iff {G : Arcs V} {root : V} {u v : HeightNode V height} :
    Edge (inwardHeightTree G root height) u v ↔
      u.val ≠ [] ∧ heightHistoryValid G root u ∧ v = heightParent u := by
  constructor
  · intro h
    obtain ⟨node, member, eq⟩ := mem_image.mp h
    obtain ⟨lhs, rhs⟩ := Prod.mk.inj eq
    subst node
    have valid := (mem_filter.mp member).2
    exact ⟨valid.1, valid.2, rhs.symm⟩
  · rintro ⟨ne, valid, rfl⟩
    exact mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, ne, valid⟩, rfl⟩

theorem heightHistoryValid_append {G : Arcs V} {root : V} {hist : HeightNode V height}
    {v : V} (bound : (hist.val ++ [v]).length ≤ height) :
    heightHistoryValid G root ⟨hist.val ++ [v], bound⟩ ↔
      heightHistoryValid G root hist ∧ Reach G v (heightLabel root hist) := by
  change ((root :: hist.val) ++ [v]).IsChain (fun a b => b ∈ reaches G a) ↔ _
  rw [List.isChain_append, List.getLast?_eq_some_getLast (List.cons_ne_nil root hist.val)]
  simp [heightHistoryValid, heightLabel]

theorem inwardHeightTree_append {G : Arcs V} {root : V} {hist : HeightNode V height}
    {v : V} (bound : (hist.val ++ [v]).length ≤ height)
    (valid : heightHistoryValid G root hist) (transfer : Reach G v (heightLabel root hist)) :
    Edge (inwardHeightTree G root height) ⟨hist.val ++ [v], bound⟩ hist := by
  refine inwardHeightTree_edge_iff.mpr ⟨by simp, (heightHistoryValid_append bound).mpr ⟨valid, transfer⟩, ?_⟩
  apply Subtype.ext
  simp [heightParent]

private theorem parent_valid {G : Arcs V} {root : V} {node : HeightNode V height}
    (h : heightHistoryValid G root node) : heightHistoryValid G root (heightParent node) :=
  h.prefix (List.cons_prefix_cons.mpr ⟨rfl, List.dropLast_prefix node.val⟩)

theorem inwardHeightTree_reaches_root {G : Arcs V} {root : V} {node : HeightNode V height}
    (valid : heightHistoryValid G root node) :
    Reach (inwardHeightTree G root height) node heightRoot := by
  have all (d : ℕ) (u : HeightNode V height) (depth : u.val.length = d)
      (ok : heightHistoryValid G root u) :
      Reach (inwardHeightTree G root height) u heightRoot := by
    induction d using Nat.strong_induction_on generalizing u with
    | _ d ih =>
      by_cases empty : u.val = []
      · obtain rfl : u = heightRoot := Subtype.ext empty
        exact .refl
      · have pdepth : (heightParent u).val.length < d := by
          have positive : 0 < u.val.length := List.length_pos_of_ne_nil empty
          change u.val.dropLast.length < d
          rw [List.length_dropLast, ← depth]
          omega
        have rest := ih _ pdepth (heightParent u) rfl (parent_valid ok)
        exact rest.head (inwardHeightTree_edge_iff.mpr ⟨empty, ok, rfl⟩)
  exact all _ node rfl valid

private theorem inwardHeightTree_edge_decreases {G : Arcs V} {root : V} {u v : HeightNode V height}
    (edge : Edge (inwardHeightTree G root height) u v) : v.val.length < u.val.length := by
  obtain ⟨ne, _, rfl⟩ := inwardHeightTree_edge_iff.mp edge
  have positive : 0 < u.val.length := List.length_pos_of_ne_nil ne
  change u.val.dropLast.length < u.val.length
  rw [List.length_dropLast]
  omega

/-- The metric template has one rootward edge at each nonroot valid history.
Other ambient histories have no incident arcs. -/
theorem inwardHeightTree_arborescence (G : Arcs V) (root : V) (height : ℕ) :
    InArborescence (inwardHeightTree G root height) heightRoot := by
  constructor
  · have mono {u v : HeightNode V height} (r : Reach (inwardHeightTree G root height) u v) :
        v.val.length ≤ u.val.length := by
      induction r with
      | refl => exact le_rfl
      | tail prior edge ih => exact (inwardHeightTree_edge_decreases edge).le.trans ih
    intro u v edge back
    exact (not_lt_of_ge (mono back)) (inwardHeightTree_edge_decreases edge)
  · intro u v w left right
    exact (inwardHeightTree_edge_iff.mp left).2.2.trans (inwardHeightTree_edge_iff.mp right).2.2.symm
  · intro e he
    obtain ⟨ne, valid, eq⟩ := inwardHeightTree_edge_iff.mp he
    exact ⟨inwardHeightTree_reaches_root valid, eq.symm ▸ inwardHeightTree_reaches_root (parent_valid valid)⟩

theorem inwardHeightTree_edge_reach {G : Arcs V} {root : V} {u v : HeightNode V height}
    (e : Edge (inwardHeightTree G root height) u v) : Reach G (heightLabel root u) (heightLabel root v) := by
  obtain ⟨ne, valid, rfl⟩ := inwardHeightTree_edge_iff.mp e
  have drop : (root :: u.val).dropLast = root :: u.val.dropLast := by
    cases h : u.val with
    | nil => exact (ne h).elim
    | cons a rest => simp
  have has : (root :: u.val).dropLast ≠ [] := by rw [drop]; exact List.cons_ne_nil _ _
  have last := valid.rel_getLast_dropLast has
  have transfer : heightLabel root u ∈ reaches G (heightLabel root (heightParent u)) := by
    simpa [heightLabel, heightParent, drop] using last
  exact mem_reaches.mp transfer

def heightLinkWeight (G : Arcs V) (root : V) (e : HeightNode V height × HeightNode V height) : ℕ :=
  hops G (heightLabel root e.1) (heightLabel root e.2)

theorem heightLinkWeight_le {G : Arcs V} {root : V} {u v : HeightNode V height}
    {path : List (V × V)} (w : Walk G (heightLabel root u) (heightLabel root v) path) :
    heightLinkWeight G root (u, v) ≤ path.length :=
  hops_le_walk w

/-- Expand any selected template links by the shortest original routes. -/
def expandHeightLinks (G : Arcs V) (root : V) (links : Arcs (HeightNode V height)) : Arcs V :=
  links.biUnion fun e => pathArcs (routePath G (heightLabel root e.1) (heightLabel root e.2))

theorem expandHeightLinks_mono (G : Arcs V) (root : V) :
    Monotone (expandHeightLinks (height := height) G root) := by
  intro left right sub e he
  obtain ⟨link, member, used⟩ := mem_biUnion.mp he
  exact mem_biUnion.mpr ⟨link, sub member, used⟩

theorem expandHeightLinks_sub (G : Arcs V) (root : V) (links : Arcs (HeightNode V height)) :
    expandHeightLinks G root links ⊆ G := by
  intro e he
  obtain ⟨link, _, used⟩ := mem_biUnion.mp he
  cases h : routePath G (heightLabel root link.1) (heightLabel root link.2) with
  | none => simp [pathArcs, h] at used
  | some path => exact (routePath_some h).1.mem (by simpa [pathArcs, h] using used)

theorem expandHeightLinks_cost (G : Arcs V) (root : V) (links : Arcs (HeightNode V height)) :
    (expandHeightLinks G root links).card ≤ ∑ link ∈ links, heightLinkWeight G root link := by
  refine card_biUnion_le.trans (sum_le_sum fun link _ => ?_)
  cases h : routePath G (heightLabel root link.1) (heightLabel root link.2) with
  | none => simp [pathArcs]
  | some path =>
    simp only [pathArcs, heightLinkWeight]
    calc
      path.toFinset.card ≤ path.length := List.toFinset_card_le path
      _ = _ := routePath_length_eq_hops h

theorem expandHeightLinks_reach {G : Arcs V} {root : V} {links : Arcs (HeightNode V height)}
    (sub : links ⊆ inwardHeightTree G root height) {u v : HeightNode V height}
    (path : Reach links u v) :
    Reach (expandHeightLinks G root links) (heightLabel root u) (heightLabel root v) := by
  induction path with
  | refl => exact .refl
  | @tail w z _ edge ih =>
    have transfer := inwardHeightTree_edge_reach (sub edge)
    obtain ⟨l, hl⟩ := routePath_succeeds.mpr transfer
    have used : l.toFinset ⊆ expandHeightLinks G root links := by
      intro e he
      exact mem_biUnion.mpr ⟨(w, z), edge, by simpa [pathArcs, hl] using he⟩
    exact ih.trans (reach_mono used (routePath_some hl).1.in_edges.reachable)

end OnlineReachabilityPreservers
