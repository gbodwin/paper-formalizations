import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Chain
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Balanced median shortcuts (Lemma 20)

This is the deterministic shortcut lemma `lem:supershortcut` of
Bodwin–Samborska, arXiv:2604.03412v3. Reachability is an arbitrary transitive
relation. `List.Pairwise R` expresses reachability in forward list order;
no antisymmetry or global reflexivity is assumed.

A balanced median tree is constructed from the input list, and its actual
finite shortcut edges are the reachable, nonloop edges of the two stars at
each recursive median. All counting is explicit: at depth `d`, the set has
at most `2 * p.length * d` edges, and each vertex has at most `d` possible
mediators. Choosing `d = Nat.log2 p.length + 1` covers even the empty list.
-/

namespace DirectedFlowCutGap.MedianShortcuts

open scoped Classical

variable {α : Type*}

/-- A binary recursion tree; its inorder list is the original ordered list. -/
inductive Tree (α : Type*) where
  | empty : Tree α
  | node : Tree α → α → Tree α → Tree α

namespace Tree

def vertices : Tree α → List α
  | .empty => []
  | .node l m r => l.vertices ++ m :: r.vertices

def height : Tree α → ℕ
  | .empty => 0
  | .node l _ r => max l.height r.height + 1

/-- At every nonempty node, the pivot is the middle entry of its inorder list. -/
def Balanced : Tree α → Prop
  | .empty => True
  | .node l m r => l.Balanced ∧ r.Balanced ∧
      l.vertices.length = (l.vertices ++ m :: r.vertices).length / 2

/-- Explicit balanced-median construction, by recursion on its depth budget. -/
theorem exists_balanced (p : List α) (d : ℕ) (hp : p.length < 2 ^ d) :
    ∃ t : Tree α, t.vertices = p ∧ t.height ≤ d ∧ t.Balanced := by
  induction d generalizing p with
  | zero =>
      have : p = [] := by simpa using hp
      subst p
      exact ⟨.empty, rfl, le_rfl, trivial⟩
  | succ d ih =>
      by_cases he : p = []
      · subst p
        exact ⟨.empty, rfl, Nat.zero_le _, trivial⟩
      have hpos : 0 < p.length := List.length_pos_iff.mpr he
      have hmid : p.length / 2 < p.length := Nat.div_lt_self hpos (by decide)
      let a := p.take (p.length / 2)
      let m := p[p.length / 2]
      let b := p.drop (p.length / 2 + 1)
      have hsplit : a ++ m :: b = p := by
        dsimp [a, m, b]
        rw [List.cons_getElem_drop_succ, List.take_append_drop]
      have ha : a.length = p.length / 2 := by
        simp [a, List.length_take, Nat.min_eq_left hmid.le]
      have hb : b.length = p.length - (p.length / 2 + 1) := by simp [b]
      have hpow : p.length < 2 ^ d * 2 := by simpa [pow_succ] using hp
      have ha' : a.length < 2 ^ d := by rw [ha]; omega
      have hb' : b.length < 2 ^ d := by rw [hb]; omega
      obtain ⟨l, hl, hld, hlb⟩ := ih a ha'
      obtain ⟨r, hr, hrd, hrb⟩ := ih b hb'
      refine ⟨.node l m r, ?_, ?_, ?_⟩
      · simpa [vertices, hl, hr] using hsplit
      · simp only [height]
        omega
      · refine ⟨hlb, hrb, ?_⟩
        rw [hl, hr, hsplit, ha]

/-- Two directed stars, retaining only reachable nonloop edges. -/
noncomputable def star (R : α → α → Prop) (p : List α) (m : α) : Finset (α × α) :=
  ((p.toFinset.image fun x => (x, m)) ∪
    (p.toFinset.image fun y => (m, y))).filter fun e => e.1 ≠ e.2 ∧ R e.1 e.2

noncomputable def edges (R : α → α → Prop) : Tree α → Finset (α × α)
  | .empty => ∅
  | .node l m r => star R (l.vertices ++ m :: r.vertices) m ∪
      (l.edges R ∪ r.edges R)

@[simp] theorem edges_empty (R : α → α → Prop) : (Tree.empty : Tree α).edges R = ∅ := rfl

@[simp] theorem edges_singleton (R : α → α → Prop) (x : α) :
    (Tree.node .empty x .empty).edges R = ∅ := by
  classical
  simp [edges, vertices, star]

/-- Medians on one search branch containing the ancestors needed for `x`.
The branch continues right when `x` itself is the pivot. -/
noncomputable def mediators : Tree α → α → Finset α
  | .empty, _ => ∅
  | .node l m r, x => insert m (if x ∈ l.vertices then l.mediators x else r.mediators x)

lemma star_in (R : α → α → Prop) (p : List α) (m x : α)
    (hx : x ∈ p) (hne : x ≠ m) (hR : R x m) : (x, m) ∈ star R p m := by
  classical
  simp only [star, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    List.mem_toFinset, Prod.mk.injEq]
  exact ⟨Or.inl ⟨x, hx, rfl, trivial⟩, hne, hR⟩

lemma star_out (R : α → α → Prop) (p : List α) (m y : α)
    (hy : y ∈ p) (hne : m ≠ y) (hR : R m y) : (m, y) ∈ star R p m := by
  classical
  simp only [star, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    List.mem_toFinset, Prod.mk.injEq]
  exact ⟨Or.inr ⟨y, hy, trivial, rfl⟩, hne, hR⟩

lemma star_valid (R : α → α → Prop) (p : List α) (m : α) (hm : m ∈ p)
    {x y : α} (he : (x, y) ∈ star R p m) :
    x ∈ p ∧ y ∈ p ∧ x ≠ y ∧ R x y := by
  classical
  simp only [star, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
    List.mem_toFinset, Prod.mk.injEq] at he
  rcases he with ⟨h | h, hne, hR⟩
  · obtain ⟨v, hv, rfl, rfl⟩ := h
    exact ⟨hv, hm, hne, hR⟩
  · obtain ⟨v, hv, rfl, rfl⟩ := h
    exact ⟨hm, hv, hne, hR⟩

theorem edges_valid (R : α → α → Prop) (t : Tree α) {x y : α}
    (he : (x, y) ∈ t.edges R) :
    x ∈ t.vertices ∧ y ∈ t.vertices ∧ x ≠ y ∧ R x y := by
  classical
  induction t with
  | empty => simp [edges] at he
  | node l m r il ir =>
      simp only [edges, Finset.mem_union] at he
      rcases he with h | h | h
      · exact star_valid R _ m (by simp [vertices]) h
      · obtain ⟨hx, hy, hn, hR⟩ := il h
        exact ⟨by simp [vertices, hx], by simp [vertices, hy], hn, hR⟩
      · obtain ⟨hx, hy, hn, hR⟩ := ir h
        exact ⟨by simp [vertices, hx], by simp [vertices, hy], hn, hR⟩

lemma star_card (R : α → α → Prop) (p : List α) (m : α) :
    (star R p m).card ≤ 2 * p.length := by
  classical
  unfold star
  calc
    _ ≤ (p.toFinset.image fun x => (x, m)).card +
        (p.toFinset.image fun y => (m, y)).card :=
      (Finset.card_filter_le _ _).trans (Finset.card_union_le _ _)
    _ ≤ p.toFinset.card + p.toFinset.card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ 2 * p.length := by have := p.toFinset_card_le; omega

/-- Explicit edge counting, without an asymptotic recurrence assumption. -/
theorem edges_card (R : α → α → Prop) (t : Tree α) :
    (t.edges R).card ≤ 2 * t.vertices.length * t.height := by
  classical
  induction t with
  | empty => simp [edges, vertices, height]
  | node l m r il ir =>
      have hs := star_card R (l.vertices ++ m :: r.vertices) m
      have hu := Finset.card_union_le
        (star R (l.vertices ++ m :: r.vertices) m) (l.edges R ∪ r.edges R)
      have hc := Finset.card_union_le (l.edges R) (r.edges R)
      have hl : l.height ≤ max l.height r.height := le_max_left _ _
      have hr : r.height ≤ max l.height r.height := le_max_right _ _
      have il' := Nat.mul_le_mul_left (2 * l.vertices.length) hl
      have ir' := Nat.mul_le_mul_left (2 * r.vertices.length) hr
      simp only [List.length_append, List.length_cons] at hs
      simp only [edges, vertices, height, List.length_append, List.length_cons]
      nlinarith

/-- The search follows only one child, so there is at most one mediator per depth. -/
theorem mediators_card (t : Tree α) (x : α) : (t.mediators x).card ≤ t.height := by
  classical
  induction t with
  | empty => simp [mediators, height]
  | node l m r il ir =>
      simp only [mediators, height]
      split_ifs with hx
      · exact (Finset.card_insert_le _ _).trans (by omega)
      · exact (Finset.card_insert_le _ _).trans (by omega)

theorem mediators_mem (t : Tree α) (x m : α) (hm : m ∈ t.mediators x) :
    m ∈ t.vertices := by
  classical
  induction t with
  | empty => simp [mediators] at hm
  | node l a r il ir =>
      simp only [mediators, Finset.mem_insert] at hm
      rcases hm with rfl | hm
      · simp [vertices]
      · split_ifs at hm with hx
        · have := il hm; simp [vertices, this]
        · have := ir hm; simp [vertices, this]

end Tree

/-- An actual path consisting of zero, one, or two selected edges. In the
last case its intermediate vertex must belong to the specified finite set. -/
def TwoHop (S : Finset (α × α)) (M : Finset α) (x y : α) : Prop :=
  x = y ∨ (x, y) ∈ S ∨ ∃ m ∈ M, (x, m) ∈ S ∧ (m, y) ∈ S

theorem TwoHop.refl (S : Finset (α × α)) (M : Finset α) (x : α) :
    TwoHop S M x x := Or.inl rfl

lemma TwoHop.mono {S T : Finset (α × α)} {M N : Finset α} {x y : α}
    (h : TwoHop S M x y) (hS : S ⊆ T) (hM : M ⊆ N) : TwoHop T N x y := by
  rcases h with h | h | ⟨m, hm, hx, hy⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl (hS h))
  · exact Or.inr (Or.inr ⟨m, hM hm, hS hx, hS hy⟩)

/-- If the zero- and one-edge alternatives are unavailable, the uniform
mediator set supplies both actual shortcut edges. -/
lemma TwoHop.two_edges {S : Finset (α × α)} {M : Finset α} {x y : α}
    (h : TwoHop S M x y) (hne : x ≠ y) (hnot : (x, y) ∉ S) :
    ∃ m ∈ M, (x, m) ∈ S ∧ (m, y) ∈ S := by
  rcases h with he | he | he
  · exact (hne he).elim
  · exact (hnot he).elim
  · exact he

/-- `TwoHop` gives a genuine simple directed vertex list with at most two
edges, not just a reachability assertion or an assumed distance oracle. -/
theorem TwoHop.exists_path {S : Finset (α × α)} {M : Finset α} {x y : α}
    (h : TwoHop S M x y) (hloop : ∀ a b, (a, b) ∈ S → a ≠ b) :
    ∃ q : List α, q.head? = some x ∧ q.getLast? = some y ∧ q.Nodup ∧
      q.IsChain (fun a b => (a, b) ∈ S) ∧ q.length - 1 ≤ 2 := by
  classical
  by_cases heq : x = y
  · subst y
    exact ⟨[x], by simp⟩
  rcases h with he | he | ⟨m, _hm, hxm, hmy⟩
  · exact (heq he).elim
  · exact ⟨[x, y], by simp [heq, he]⟩
  · have hxne := hloop x m hxm
    have hmne := hloop m y hmy
    exact ⟨[x, m, y], by simp [hxne, heq, hmne, hxm, hmy]⟩

/-- A generic median tree shortcuts every reachable pair in its inorder list.
The backward crossing case uses transitivity with the two forward segments. -/
theorem Tree.twoHop (R : α → α → Prop)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (t : Tree α) (hn : t.vertices.Nodup) (hf : t.vertices.Pairwise R)
    {x y : α} (hx : x ∈ t.vertices) (hy : y ∈ t.vertices) (hxy : R x y) :
    TwoHop (t.edges R) (t.mediators x) x y := by
  classical
  induction t with
  | empty => simp [Tree.vertices] at hx
  | node l m r il ir =>
      have hp : (l.vertices ++ m :: r.vertices).Pairwise R := hf
      obtain ⟨hfl, hfmr, hcross⟩ := List.pairwise_append.mp hp
      obtain ⟨hfm, hfr⟩ := List.pairwise_cons.mp hfmr
      obtain ⟨hnl, hnmr, hdisj⟩ := List.nodup_append.mp hn
      have hnr := (List.nodup_cons.mp hnmr).2
      have hS₀ : Tree.star R (l.vertices ++ m :: r.vertices) m ⊆
          (Tree.node l m r).edges R := by intro e he; exact Finset.mem_union_left _ he
      have hSl : l.edges R ⊆ (Tree.node l m r).edges R := by
        intro e he; exact Finset.mem_union_right _ (Finset.mem_union_left _ he)
      have hSr : r.edges R ⊆ (Tree.node l m r).edges R := by
        intro e he; exact Finset.mem_union_right _ (Finset.mem_union_right _ he)
      by_cases heq : x = y
      · exact Or.inl heq
      by_cases hxm : x = m
      · subst x
        exact Or.inr (Or.inl (hS₀ (Tree.star_out R _ m y hy heq hxy)))
      by_cases hym : y = m
      · subst y
        exact Or.inr (Or.inl (hS₀ (Tree.star_in R _ m x hx hxm hxy)))
      have hx' : x ∈ l.vertices ∨ x ∈ r.vertices := by
        simpa only [Tree.vertices, List.mem_append, List.mem_cons, hxm, false_or] using hx
      have hy' : y ∈ l.vertices ∨ y ∈ r.vertices := by
        simpa only [Tree.vertices, List.mem_append, List.mem_cons, hym, false_or] using hy
      have via (h₁ : R x m) (h₂ : R m y) :
          TwoHop ((Tree.node l m r).edges R) ((Tree.node l m r).mediators x) x y := by
        exact Or.inr (Or.inr ⟨m, by simp [Tree.mediators],
          hS₀ (Tree.star_in R _ m x hx hxm h₁),
          hS₀ (Tree.star_out R _ m y hy (Ne.symm hym) h₂)⟩)
      rcases hx' with hxl | hxr <;> rcases hy' with hyl | hyr
      · exact (il hnl hfl hxl hyl).mono hSl (by
          intro a ha; simp [Tree.mediators, hxl, ha])
      · exact via (hcross x hxl m (by simp)) (hfm y hyr)
      · exact via (htrans hxy (hcross y hyl m (by simp))) (htrans (hfm x hxr) hxy)
      · have hnxl : x ∉ l.vertices := by
          intro hxl
          exact hdisj x hxl x (by simp [hxr]) rfl
        exact (ir hnr hfr hxr hyr).mono hSr (by
          intro a ha; simp [Tree.mediators, hnxl, ha])

/-- This is the source's exact-distance-two clause. A two-edge shortcut walk
itself supplies membership and reachability of its endpoints; no extra target
membership assumption is necessary. -/
theorem Tree.mediate_two_step (R : α → α → Prop)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (t : Tree α) (hn : t.vertices.Nodup) (hf : t.vertices.Pairwise R)
    {x y z : α} (hxz : (x, z) ∈ t.edges R) (hzy : (z, y) ∈ t.edges R)
    (hne : x ≠ y) (hnot : (x, y) ∉ t.edges R) :
    ∃ m ∈ t.mediators x, (x, m) ∈ t.edges R ∧ (m, y) ∈ t.edges R := by
  obtain ⟨hx, _hz, _hxz, hRxz⟩ := t.edges_valid R hxz
  obtain ⟨_hz, hy, _hzy, hRzy⟩ := t.edges_valid R hzy
  exact (t.twoHop R htrans hn hf hx hy (htrans hRxz hRzy)).two_edges hne hnot

/-- The source lemma with finite constants. Every edge is a reachable nonloop
on the input list. Equal endpoints have the zero-edge path; empty and singleton
lists consequently need no nontrivial shortcut edges. The mediator set works
uniformly for all reachable targets of a fixed source. -/
theorem exists_shortcuts (R : α → α → Prop)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (p : List α) (hn : p.Nodup) (hf : p.Pairwise R) :
    ∃ (S : Finset (α × α)) (M : α → Finset α),
      S.card ≤ 2 * p.length * (Nat.log2 p.length + 1) ∧
      (∀ x y, (x, y) ∈ S → x ∈ p ∧ y ∈ p ∧ x ≠ y ∧ R x y) ∧
      (∀ x, (M x).card ≤ Nat.log2 p.length + 1) ∧
      (∀ x m, m ∈ M x → m ∈ p) ∧
      (∀ x ∈ p, ∀ y ∈ p, R x y → TwoHop S (M x) x y) := by
  have hd : p.length < 2 ^ (Nat.log2 p.length + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide) _
  obtain ⟨t, ht, hh, _hb⟩ := Tree.exists_balanced p (Nat.log2 p.length + 1) hd
  refine ⟨t.edges R, t.mediators, ?_, ?_, ?_, ?_, ?_⟩
  · exact (t.edges_card R).trans (by rw [ht]; exact Nat.mul_le_mul_left _ hh)
  · intro x y he
    simpa [ht] using t.edges_valid R he
  · intro x
    exact (t.mediators_card x).trans hh
  · intro x m hm
    simpa [ht] using t.mediators_mem x m hm
  · intro x hx y hy hxy
    exact t.twoHop R htrans (by simpa [ht] using hn) (by simpa [ht] using hf)
      (by simpa [ht] using hx) (by simpa [ht] using hy) hxy

end DirectedFlowCutGap.MedianShortcuts
