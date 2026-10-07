import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The branching argument of Section 2

`Routing` records precisely the predecessor and ordering information used by
Lemma 3. It does not assume an edge-count conclusion. Constructing this data
from shortest paths is a separate obligation, not an axiom of this file.
-/
namespace LinearDistancePreservers

structure Routing (I V : Type*) where
  pred : I → V → Option V
  rank : I → V → ℕ
  rank_inj : ∀ i v w, pred i v ≠ none → pred i w ≠ none →
    rank i v = rank i w → v = w
  consistent : ∀ i j v w, pred i v ≠ none → pred j v ≠ none →
    pred i w ≠ none → pred j w ≠ none →
    rank i v < rank i w → rank j v < rank j w → pred i w = pred j w

namespace Routing
variable {I V : Type*} (R : Routing I V)

def BranchAt (i j k : I) (v : V) : Prop :=
  R.pred i v ≠ none ∧ R.pred j v ≠ none ∧ R.pred k v ≠ none ∧
  R.pred i v ≠ R.pred j v ∧ R.pred i v ≠ R.pred k v ∧
  R.pred j v ≠ R.pred k v

/-- A fixed triple of selected paths can branch at only one vertex (Lemma 3). -/
theorem branch_vertex_unique {i j k : I} {v w : V}
    (hv : R.BranchAt i j k v) (hw : R.BranchAt i j k w) : v = w := by
  rcases hv with ⟨hiv, hjv, hkv, hijv, hikv, hjkv⟩
  rcases hw with ⟨hiw, hjw, hkw, hijw, hikw, hjkw⟩
  by_contra hne
  have hi : R.rank i v ≠ R.rank i w := fun h => hne (R.rank_inj i v w hiv hiw h)
  have hj : R.rank j v ≠ R.rank j w := fun h => hne (R.rank_inj j v w hjv hjw h)
  have hk : R.rank k v ≠ R.rank k w := fun h => hne (R.rank_inj k v w hkv hkw h)
  rcases lt_or_gt_of_ne hi with hi | hi <;>
    rcases lt_or_gt_of_ne hj with hj | hj <;>
    rcases lt_or_gt_of_ne hk with hk | hk
  · exact hijw (R.consistent i j v w hiv hjv hiw hjw hi hj)
  · exact hijw (R.consistent i j v w hiv hjv hiw hjw hi hj)
  · exact hikw (R.consistent i k v w hiv hkv hiw hkw hi hk)
  · exact hjkv (R.consistent j k w v hjw hkw hjv hkv hj hk)
  · exact hjkw (R.consistent j k v w hjv hkv hjw hkw hj hk)
  · exact hikv (R.consistent i k w v hiw hkw hiv hkv hi hk)
  · exact hijv (R.consistent i j w v hiw hjw hiv hjv hi hj)
  · exact hijv (R.consistent i j w v hiw hjw hiv hjv hi hj)

variable [Fintype I] [Fintype V] [DecidableEq V]

noncomputable def tails (v : V) : Finset V :=
  Finset.univ.filter fun u => ∃ i, R.pred i v = some u

@[simp] theorem mem_tails {u v : V} : u ∈ R.tails v ↔ ∃ i, R.pred i v = some u := by
  classical
  simp [tails]

noncomputable def base (v : V) : Finset V :=
  Classical.choose (Finset.exists_subset_card_eq (s := R.tails v) (Nat.min_le_right 2 _))

theorem base_subset (v : V) : R.base v ⊆ R.tails v :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := R.tails v) (Nat.min_le_right 2 _))).1

theorem base_card (v : V) : (R.base v).card = min 2 (R.tails v).card :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := R.tails v) (Nat.min_le_right 2 _))).2

noncomputable def excess : Finset (V × V) :=
  Finset.univ.filter fun e => e.2 ∈ R.tails e.1 ∧ e.2 ∉ R.base e.1

/-- An excess incoming edge has two other incoming edges available as anchors. -/
theorem excess_anchors {v u : V} (hu : (v,u) ∈ R.excess) :
    ∃ a b, a ∈ R.tails v ∧ b ∈ R.tails v ∧ a ≠ b ∧ a ≠ u ∧ b ≠ u := by
  classical
  have hu' : u ∈ R.tails v ∧ u ∉ R.base v := by simpa [excess] using hu
  have htwo : 2 ≤ (R.tails v).card := by
    by_contra h
    have heq : R.base v = R.tails v :=
      Finset.eq_of_subset_of_card_le (R.base_subset v) (by
        rw [R.base_card]; omega)
    exact hu'.2 (heq ▸ hu'.1)
  have hc : (R.base v).card = 2 := by rw [R.base_card, Nat.min_eq_left htwo]
  obtain ⟨a,b,hab,heq⟩ := Finset.card_eq_two.mp hc
  have ha : a ∈ R.base v := by simp [heq]
  have hb : b ∈ R.base v := by simp [heq]
  exact ⟨a,b,R.base_subset v ha,R.base_subset v hb,hab,
    fun h => hu'.2 (h ▸ ha), fun h => hu'.2 (h ▸ hb)⟩

/-- Each excess edge is witnessed by an ordered triple of paths. -/
theorem excess_witness {v u : V} (hu : (v,u) ∈ R.excess) :
    ∃ t : I × I × I, R.BranchAt t.1 t.2.1 t.2.2 v ∧ R.pred t.2.2 v = some u := by
  obtain ⟨a,b,ha,hb,hab,hau,hbu⟩ := R.excess_anchors hu
  obtain ⟨i,hi⟩ := R.mem_tails.mp ha
  obtain ⟨j,hj⟩ := R.mem_tails.mp hb
  have hu' : u ∈ R.tails v := by classical simpa [excess] using (Finset.mem_filter.mp hu).2.1
  obtain ⟨k,hk⟩ := R.mem_tails.mp hu'
  refine ⟨(i,j,k), ?_, hk⟩
  simp only [BranchAt, hi, hj, hk, reduceCtorEq, ne_eq, Option.some.injEq]
  exact ⟨by trivial, by trivial, by trivial, hab, hau, hbu⟩

/-- Exact finite form sufficient for Lemmas 3--4: at most p^3 excess edges. -/
theorem excess_card_le : R.excess.card ≤ Fintype.card I ^ 3 := by
  classical
  let f : R.excess → I × I × I := fun e => Classical.choose (R.excess_witness e.property)
  have hf (e : R.excess) : R.BranchAt (f e).1 (f e).2.1 (f e).2.2 e.val.1 ∧
      R.pred (f e).2.2 e.val.1 = some e.val.2 := Classical.choose_spec (R.excess_witness e.property)
  have hinj : Function.Injective f := by
    intro e e' he
    have hv : e.val.1 = e'.val.1 := R.branch_vertex_unique (hf e).1 (by simpa [he] using (hf e').1)
    have hu : e.val.2 = e'.val.2 := by
      apply Option.some.inj
      calc
        some e.val.2 = R.pred (f e).2.2 e.val.1 := (hf e).2.symm
        _ = R.pred (f e').2.2 e'.val.1 := by rw [he,hv]
        _ = some e'.val.2 := (hf e').2
    exact Subtype.ext (Prod.ext hv hu)
  have := Fintype.card_le_of_injective f hinj
  simpa [Fintype.card_coe, Fintype.card_prod, pow_succ, pow_two, mul_assoc] using this

noncomputable def edges : Finset (V × V) :=
  Finset.univ.filter fun e => e.2 ∈ R.tails e.1

/-- Section 2's linear-regime estimate, with explicit constants. The pair
`(v,u)` represents the directed edge from `u` to `v`. -/
theorem edges_card_le : R.edges.card ≤ 2 * Fintype.card V + Fintype.card I ^ 3 := by
  classical
  let light : Finset (V × V) := Finset.univ.biUnion fun v => (R.base v).image (fun u => (v,u))
  have hlight : light.card ≤ 2 * Fintype.card V := by
    calc
      light.card ≤ ∑ v : V, ((R.base v).image (fun u => (v,u))).card := Finset.card_biUnion_le
      _ ≤ ∑ _v : V, 2 := Finset.sum_le_sum fun v _ =>
        (Finset.card_image_le).trans (by rw [R.base_card]; exact Nat.min_le_left _ _)
      _ = 2 * Fintype.card V := by simp [mul_comm]
  have hcover : R.edges ⊆ light ∪ R.excess := by
    intro e he
    have htail : e.2 ∈ R.tails e.1 := (Finset.mem_filter.mp he).2
    by_cases hb : e.2 ∈ R.base e.1
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨e.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨e.2,hb,rfl⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,htail,hb⟩)
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hlight R.excess_card_le))

/-- When p^3 ≤ n the union contains at most 3n edges. -/
theorem linear_regime (h : Fintype.card I ^ 3 ≤ Fintype.card V) :
    R.edges.card ≤ 3 * Fintype.card V := by
  have := R.edges_card_le
  omega

end Routing
end LinearDistancePreservers
