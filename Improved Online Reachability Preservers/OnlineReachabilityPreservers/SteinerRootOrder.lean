import Mathlib.Data.List.Lex
import OnlineReachabilityPreservers.SteinerJunction

/-! The terminal order in an inward arborescence and its edge intervals. -/

namespace OnlineReachabilityPreservers

open Finset

private theorem tail_le_of_cons_le {A : Type*} [LinearOrder A] {a : A} {left right : List A}
    (h : a :: left ≤ a :: right) : left ≤ right := by
  rcases lt_or_eq_of_le h with strict | eq
  · exact le_of_lt (show left < right from List.lex_cons_iff.mp strict)
  · exact (List.cons.inj eq).2.le

private theorem head_le_of_cons_le {A : Type*} [LinearOrder A] {a b : A} {left right : List A}
    (h : a :: left ≤ b :: right) : a ≤ b := by
  rcases lt_or_eq_of_le h with strict | eq
  · exact List.head_le_of_lt strict
  · exact (List.cons.inj eq).1.le

private theorem prefix_between {A : Type*} [LinearOrder A] {stem low mid high : List A}
    (first : stem <+: low) (last : stem <+: high) (low_mid : low ≤ mid) (mid_high : mid ≤ high) :
    stem <+: mid := by
  induction stem generalizing low mid high with
  | nil => exact List.nil_prefix
  | cons x stem ih =>
    obtain ⟨lowTail, rfl⟩ := first
    obtain ⟨highTail, rfl⟩ := last
    cases mid with
    | nil =>
      exact (not_le_of_gt (List.nil_lt_cons x _ ) low_mid).elim
    | cons y middle =>
      obtain rfl := le_antisymm (head_le_of_cons_le low_mid) (head_le_of_cons_le mid_high)
      apply List.cons_prefix_cons.mpr
      exact ⟨rfl, ih (List.prefix_append _ _) (List.prefix_append _ _)
        (tail_le_of_cons_le low_mid) (tail_le_of_cons_le mid_high)⟩

private theorem fin_convex_interval {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (between : ∀ {i j k : Fin n}, i ≤ j → j ≤ k → P i → P k → P j) :
    ∃ first past : ℕ, ∀ i : Fin n, P i ↔ first ≤ i.val ∧ i.val < past := by
  let S := (univ : Finset (Fin n)).filter P
  by_cases h : S.Nonempty
  · let lo := S.min' h
    let hi := S.max' h
    have mlo : lo ∈ S := min'_mem _ _
    have mhi : hi ∈ S := max'_mem _ _
    refine ⟨lo.val, hi.val + 1, fun i => ⟨?_, ?_⟩⟩
    · intro present
      have mem : i ∈ S := mem_filter.mpr ⟨mem_univ _, present⟩
      exact ⟨min'_le _ _ mem, Nat.lt_succ_of_le (le_max' _ _ mem)⟩
    · rintro ⟨afterFirst, beforePast⟩
      exact between afterFirst (Nat.le_of_lt_succ beforePast) (mem_filter.mp mlo).2 (mem_filter.mp mhi).2
  · refine ⟨0, 0, fun i => ⟨?_, ?_⟩⟩
    · intro present
      exact (h ⟨i, mem_filter.mpr ⟨mem_univ _, present⟩⟩).elim
    · rintro ⟨_, impossible⟩
      exact (Nat.not_lt_zero _ impossible).elim

variable {V : Type*} [LinearOrder V] [Fintype V]

private def terminalRouteKey (T : Arcs V) (root terminal : V) : List (V ×ₗ V) ×ₗ V :=
  toLex (((routePath T terminal root).getD []).reverse.map toLex, terminal)

/-- The terminals in lexicographic order on their root-to-terminal arc lists.
The arcs themselves retain their orientation toward the root. -/
def rootedTerminalOrder (T : Arcs V) (root : V) (terminals : Finset V) :
    List (List (V ×ₗ V) ×ₗ V) :=
  (terminals.image (terminalRouteKey T root)).sort (· ≤ ·)

theorem rootedTerminalOrder_length (T : Arcs V) (root : V) (terminals : Finset V) :
    (rootedTerminalOrder T root terminals).length = terminals.card := by
  rw [rootedTerminalOrder, Finset.length_sort]
  exact card_image_of_injective _ (fun a b eq => congrArg (fun key => (ofLex key).2) eq)

theorem rootedTerminalOrder_covers {T : Arcs V} {root : V} {terminals : Finset V} {v : V} :
    v ∈ terminals →
      ∃ i : Fin (rootedTerminalOrder T root terminals).length,
        (ofLex ((rootedTerminalOrder T root terminals).get i)).2 = v := by
  intro hv
  have mem : terminalRouteKey T root v ∈ rootedTerminalOrder T root terminals :=
    (Finset.mem_sort (· ≤ ·)).mpr (mem_image.mpr ⟨v, hv, rfl⟩)
  obtain ⟨i, eq⟩ := List.mem_iff_get.mp mem
  exact ⟨i, congrArg (fun key => (ofLex key).2) eq⟩

theorem rootedTerminalOrder_walk {T : Arcs V} {root : V} {terminals : Finset V}
    (allReach : ∀ v ∈ terminals, Reach T v root) (i : Fin (rootedTerminalOrder T root terminals).length) :
    let key := ofLex ((rootedTerminalOrder T root terminals).get i)
    Walk T key.2 root (key.1.map ofLex).reverse := by
  let xs := rootedTerminalOrder T root terminals
  have member : xs.get i ∈ xs := List.mem_iff_get.mpr ⟨i, rfl⟩
  have listed : xs.get i ∈ terminals.image (terminalRouteKey T root) :=
    (Finset.mem_sort (· ≤ ·)).mp member
  obtain ⟨v, hv, eq⟩ := mem_image.mp listed
  obtain ⟨l, h⟩ := routePath_succeeds.mpr (allReach v hv)
  change Walk T (ofLex (xs.get i)).2 root ((ofLex (xs.get i)).1.map ofLex).reverse
  rw [← eq]
  simpa [terminalRouteKey, h, List.map_map, Function.comp_def] using (routePath_some h).1

theorem rootedTerminalOrder_nodup {T : Arcs V} {root : V} (tree : InArborescence T root)
    {terminals : Finset V} (allReach : ∀ v ∈ terminals, Reach T v root)
    (i : Fin (rootedTerminalOrder T root terminals).length) :
    ((ofLex ((rootedTerminalOrder T root terminals).get i)).1).Nodup := by
  have simple := (rootedTerminalOrder_walk allReach i).simple_of_dag tree.dag
  have arcNodup := List.Nodup.of_map Prod.fst simple.2.of_append_left
  exact List.Nodup.of_map ofLex (List.nodup_reverse.mp arcNodup)

/-- The fixed rootward continuation of an arc is a prefix of exactly the
ordered routes that use the arc. -/
theorem rootedTerminalOrder_arc_prefix {T : Arcs V} {root : V} (tree : InArborescence T root)
    {terminals : Finset V} (allReach : ∀ v ∈ terminals, Reach T v root) {e : V × V} (arc : e ∈ T) :
    let xs := rootedTerminalOrder T root terminals
    ∃ stem : List (V ×ₗ V), toLex e ∈ stem ∧ ∀ i : Fin xs.length,
      toLex e ∈ (ofLex (xs.get i)).1 ↔ stem <+: (ofLex (xs.get i)).1 := by
  let xs := rootedTerminalOrder T root terminals
  obtain ⟨tail, _, continuation⟩ := tree.arc_reversed_prefix arc
  refine ⟨(e :: tail).reverse.map toLex, by simp, fun i => ?_⟩
  let arcs := (ofLex (xs.get i)).1
  have plain : e ∈ arcs.map ofLex ↔ (e :: tail).reverse <+: arcs.map ofLex := by
    have h := continuation (rootedTerminalOrder_walk allReach i)
    simpa [arcs] using h
  constructor
  · intro mem
    have member : e ∈ arcs.map ofLex := List.mem_map.mpr ⟨toLex e, mem, rfl⟩
    simpa [arcs, List.map_map, Function.comp_def] using ((plain.mp member).map toLex)
  · intro pref
    have member : e ∈ arcs.map ofLex := plain.mpr (by
      simpa [arcs, List.map_map, Function.comp_def] using pref.map ofLex)
    obtain ⟨key, hk, eq⟩ := List.mem_map.mp member
    exact ofLex.injective (show ofLex key = ofLex (toLex e) from eq) ▸ hk

/-- In the terminal traversal order, the routes using an arc form one
consecutive interval. Empty descendant sets use the empty interval. -/
theorem rootedTerminalOrder_arc_interval {T : Arcs V} {root : V} (tree : InArborescence T root)
    {terminals : Finset V} (allReach : ∀ v ∈ terminals, Reach T v root) {e : V × V} (arc : e ∈ T) :
    let xs := rootedTerminalOrder T root terminals
    ∃ first past : ℕ, ∀ i : Fin xs.length,
      toLex e ∈ (ofLex (xs.get i)).1 ↔ first ≤ i.val ∧ i.val < past := by
  let xs := rootedTerminalOrder T root terminals
  obtain ⟨_, _, atIndex⟩ := rootedTerminalOrder_arc_prefix tree allReach arc
  have ordered : xs.Pairwise (fun a b => a ≤ b) := Finset.pairwise_sort _ _
  refine fin_convex_interval (fun i : Fin xs.length => toLex e ∈ (ofLex (xs.get i)).1)
    (fun {i j k} left right hi hk => ?_)
  apply (atIndex j).mpr
  exact prefix_between ((atIndex i).mp hi) ((atIndex k).mp hk)
    (Prod.Lex.monotone_fst_ofLex (ordered.rel_get_of_le left))
    (Prod.Lex.monotone_fst_ofLex (ordered.rel_get_of_le right))

theorem rootedTerminalOrder_arc_mem {T : Arcs V} {root : V} {terminals : Finset V}
    (allReach : ∀ v ∈ terminals, Reach T v root) (i : Fin (rootedTerminalOrder T root terminals).length)
    {e : V ×ₗ V} (member : e ∈ (ofLex ((rootedTerminalOrder T root terminals).get i)).1) :
    ofLex e ∈ T :=
  (rootedTerminalOrder_walk allReach i).mem (List.mem_reverse.mpr (List.mem_map.mpr ⟨e, member, rfl⟩))

end OnlineReachabilityPreservers
