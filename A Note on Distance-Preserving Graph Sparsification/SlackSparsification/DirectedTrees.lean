import SlackSparsification.DirectedBasics
import Mathlib.Tactic

/-! Actual directed weighted shortest-path trees. Consistent lexicographic
shortest paths give one incoming arc per vertex in an out-tree; reversing the
input gives an in-tree. No tree-existence or size premise is supplied. -/
namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
open scoped ENNReal NNReal
variable {V : Type*} [Fintype V] [DecidableEq V] {K : SimpleGraph V}
attribute [local instance] Classical.propDecidable

theorem arc_decomposition {s t u v : V} (p : K.Walk s t) (he : (u,v) ∈ arcs p) :
    ∃ (l : K.Walk s u) (h : K.Adj u v) (r : K.Walk v t), p = (l.concat h).append r := by
  induction p with
  | nil => simp [arcs, arcList] at he
  | @cons s z t ha p ih =>
    have hm : (u,v) = (s,z) ∨ (u,v) ∈ arcs p := by simpa [arcs, arcList] using he
    rcases hm with h | h
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
      exact ⟨Walk.nil, ha, p, by simp⟩
    · obtain ⟨l, h, r, heq⟩ := ih h
      exact ⟨Walk.cons ha l, h, r, by simp [heq, Walk.concat_cons]⟩

/-- Every optimal path from one root uses the same predecessor at v. -/
theorem optimal_incoming_unique {A : V → V → Prop} {w : V → V → ℝ≥0}
    {s t t' u u' v : V} (p : K.Walk s t) (q : K.Walk s t')
    (hp : Optimal A w p) (hq : Optimal A w q)
    (he : (u,v) ∈ arcs p) (hf : (u',v) ∈ arcs q) : u = u' := by
  obtain ⟨l, h, r, heq⟩ := arc_decomposition p he
  obtain ⟨l', h', r', heq'⟩ := arc_decomposition q hf
  have hl : (l.concat h).IsSubwalk p := ⟨Walk.nil, r, by simpa using heq⟩
  have hl' : (l'.concat h').IsSubwalk q := ⟨Walk.nil, r', by simpa using heq'⟩
  have he := (hp.subwalk hl).unique (hq.subwalk hl')
  have hlast := congrArg Walk.penultimate he
  simpa using hlast

/-- A ≤n-arc directed out-tree preserves all actual weighted distances
from the chosen root, even when some vertices are unreachable. -/
theorem exists_out_tree (K : SimpleGraph V) (A : V → V → Prop)
    (w : V → V → ℝ≥0) (s : V) :
    ∃ F : Finset (V × V), F.card ≤ Fintype.card V ∧
      (∀ e ∈ F, A e.1 e.2) ∧ ∀ v, distance K (edgeRel F) w s v = distance K A w s v := by
  classical
  let R := {v : V // ∃ p : K.Walk s v, Allowed A p}
  choose p hp using fun v : R => exists_optimal A w s v.val v.property
  let F := (univ : Finset R).biUnion fun v => arcs (p v)
  have hFA : ∀ e ∈ F, A e.1 e.2 := by
    intro e he
    obtain ⟨v, _, hv⟩ := mem_biUnion.mp he
    exact arcs_allowed (p v) (hp v).1 hv
  have hsize : F.card ≤ Fintype.card V := by
    calc
      _ ≤ (univ : Finset V).card := by
        apply card_le_card_of_injOn (fun e : V × V => e.2)
        · intro e _; exact mem_univ _
        · intro e he f hf heq
          rcases e with ⟨u,v⟩
          rcases f with ⟨u',v'⟩
          change v = v' at heq
          subst v'
          obtain ⟨t, _, ht⟩ := mem_biUnion.mp he
          obtain ⟨t', _, ht'⟩ := mem_biUnion.mp hf
          exact Prod.ext (optimal_incoming_unique (p t) (p t') (hp t) (hp t') ht ht') rfl
      _ = _ := card_univ
  refine ⟨F, hsize, hFA, ?_⟩
  intro v
  apply le_antisymm _ (distance_mono w (fun u v h => hFA (u,v) h) s v)
  by_cases hv : ∃ q : K.Walk s v, Allowed A q
  · let i : R := ⟨v,hv⟩
    rw [distance_eq_cost (hp i)]
    apply distance_le_cost w (p i)
    apply allowed_of_arcs
    intro e he
    exact mem_biUnion.mpr ⟨i, mem_univ _, he⟩
  · simp [distance_of_no_walk w hv]

/-- Reverse the output arcs to obtain the corresponding ≤n-arc in-tree. -/
theorem exists_in_tree (K : SimpleGraph V) (A : V → V → Prop)
    (w : V → V → ℝ≥0) (s : V) :
    ∃ F : Finset (V × V), F.card ≤ Fintype.card V ∧
      (∀ e ∈ F, A e.1 e.2) ∧ ∀ v, distance K (edgeRel F) w v s = distance K A w v s := by
  classical
  obtain ⟨B, hBsize, hBA, hBdist⟩ := exists_out_tree K (fun u v => A v u) (fun u v => w v u) s
  let F := B.image Prod.swap
  have hrel (u v : V) : edgeRel F v u ↔ edgeRel B u v := by
    constructor
    · intro h
      obtain ⟨⟨a,b⟩, hab, he⟩ := mem_image.mp h
      have he' : b = v ∧ a = u := Prod.mk.inj he
      rcases he' with ⟨rfl,rfl⟩
      exact hab
    · intro h
      exact mem_image.mpr ⟨(u,v),h,rfl⟩
  refine ⟨F, card_image_le.trans hBsize, ?_, ?_⟩
  · intro e he
    obtain ⟨⟨u,v⟩, h, rfl⟩ := mem_image.mp he
    exact hBA (u,v) h
  · intro v
    calc
      distance K (edgeRel F) w v s = distance K (edgeRel B) (fun u v => w v u) s v := by
        rw [← distance_reverse (edgeRel F) w v s]
        congr 1
        funext u v
        exact propext (hrel u v)
      _ = distance K (fun u v => A v u) (fun u v => w v u) s v := hBdist v
      _ = _ := distance_reverse A w v s

/-- In- and out-trees together cost at most 2n directed arcs. -/
theorem exists_root_preserver (K : SimpleGraph V) (A : V → V → Prop)
    (w : V → V → ℝ≥0) (r : V) :
    ∃ F : Finset (V × V), F.card ≤ 2 * Fintype.card V ∧ (∀ e ∈ F, A e.1 e.2) ∧
      ∀ v, distance K (edgeRel F) w r v = distance K A w r v ∧
        distance K (edgeRel F) w v r = distance K A w v r := by
  obtain ⟨O, hOc, hOA, hOd⟩ := exists_out_tree K A w r
  obtain ⟨I, hIc, hIA, hId⟩ := exists_in_tree K A w r
  have hFA : ∀ e ∈ O ∪ I, A e.1 e.2 := by
    intro e he
    exact (mem_union.mp he).elim (hOA e) (hIA e)
  refine ⟨O ∪ I, (card_union_le O I).trans (by omega), hFA, ?_⟩
  intro v
  constructor
  · apply le_antisymm _ (distance_mono w (fun u v h => hFA (u,v) h) r v)
    exact (distance_mono w (fun _ _ h => mem_union_left I h) r v).trans_eq (hOd v)
  · apply le_antisymm _ (distance_mono w (fun u v h => hFA (u,v) h) v r)
    exact (distance_mono w (fun _ _ h => mem_union_right O h) v r).trans_eq (hId v)

end SlackSparsification.Directed
