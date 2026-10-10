import Mathlib.Combinatorics.SimpleGraph.Paths
import Lean.Elab.Tactic.Omega

/-! Parallel-greedy graphs and their monotone walks. This is the actual
edge-label/matching model of Definition 1.1, not an assumed path-count bound. -/
namespace LengthExpander
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Edges sharing an endpoint and a matching index are identical. -/
def MatchingLabels (G : SimpleGraph V) (index : Sym2 V → ℕ) : Prop :=
  ∀ u v z, G.Adj u z → G.Adj v z → index s(u,z) = index s(v,z) → u = v

/-- An edge cannot be joined by an earlier-edge walk with at most s edges.
The walk formulation agrees with the far-endpoint condition in Definition 1.1. -/
def EarlierFar (G : SimpleGraph V) (index : Sym2 V → ℕ) (s : ℕ) : Prop :=
  ∀ u v, G.Adj u v → ∀ p : G.Walk u v,
    p.length ≤ s → (∀ e ∈ p.edges, index e < index s(u,v)) → False

structure IsParallelGreedy (G : SimpleGraph V) (index : Sym2 V → ℕ) (s : ℕ) : Prop where
  matching : MatchingLabels G index
  earlierFar : EarlierFar G index s

/-- Definition 3.1: strictly increasing labels along the edge sequence. -/
def Increasing (index : Sym2 V → ℕ) {u v : V} (p : G.Walk u v) : Prop :=
  (p.edges.map index).Pairwise (· < ·)

theorem increasing_concat_iff {index : Sym2 V → ℕ} {u v z : V}
    (p : G.Walk u v) (h : G.Adj v z) :
    Increasing index (p.concat h) ↔
      Increasing index p ∧ (∀ e ∈ p.edges, index e < index s(v,z)) := by
  simp [Increasing, Walk.edges_concat, List.pairwise_append]

theorem increasing_last_le {index : Sym2 V → ℕ} {u v z : V}
    {p : G.Walk u v} {h : G.Adj v z} (hp : Increasing index (p.concat h)) :
    ∀ e ∈ (p.concat h).edges, index e ≤ index s(v,z) := by
  intro e he
  have hi := (increasing_concat_iff p h).1 hp
  simp only [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · exact (hi.2 e he).le
  · rfl

theorem exists_concat_of_length_succ {u v : V} {p : G.Walk u v} {r : ℕ}
    (hp : p.length = r + 1) :
    ∃ z, ∃ q : G.Walk u z, ∃ h : G.Adj z v, q.length = r ∧ p = q.concat h := by
  have hn : ¬ p.Nil := by intro hn; have := hn.length_eq_zero; omega
  refine ⟨p.penultimate, p.dropLast, p.adj_penultimate hn, ?_, ?_⟩
  · rw [Walk.length_dropLast, hp]; omega
  · exact (Walk.concat_dropLast _).symm

/-- Lemma 3.3, strengthened to any r with 2r ≤ s+1. Odd s is included.
The proof uses the competing earlier walk directly, avoiding an informal
choice of a cycle from two paths. -/
theorem increasing_walk_unique {index : Sym2 V → ℕ} {s r : ℕ}
    (H : IsParallelGreedy G index s) (hr : 2*r ≤ s+1)
    {u v : V} (p q : G.Walk u v)
    (hp : Increasing index p) (hq : Increasing index q)
    (hlp : p.length = r) (hlq : q.length = r) : p = q := by
  induction r generalizing u v with
  | zero =>
    have hp0 := (Walk.length_eq_zero_iff.mp hlp)
    have hq0 := (Walk.length_eq_zero_iff.mp hlq)
    have huv := Walk.eq_of_length_eq_zero hlp
    subst v
    rw [hp0.eq_nil, hq0.eq_nil]
  | succ r ih =>
    obtain ⟨a, p, ha, hplen, rfl⟩ := exists_concat_of_length_succ hlp
    obtain ⟨b, q, hb, hqlen, rfl⟩ := exists_concat_of_length_succ hlq
    have hp' := (increasing_concat_iff p ha).1 hp
    have hq' := (increasing_concat_iff q hb).1 hq
    rcases lt_trichotomy (index s(a,v)) (index s(b,v)) with hlt | heq | hgt
    · exfalso
      apply H.earlierFar b v hb (q.reverse.append (p.concat ha))
      · simp only [Walk.length_append, Walk.length_reverse, Walk.length_concat, hplen, hqlen]
        omega
      · intro e he
        simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse] at he
        rcases he with he | he
        · exact hq'.2 e he
        · exact lt_of_le_of_lt (increasing_last_le hp e he) hlt
    · have hab := H.matching a b v ha hb heq
      subst b
      have hpq : p = q := ih (by omega) p q hp'.1 hq'.1 hplen hqlen
      subst q
      rfl
    · exfalso
      apply H.earlierFar a v ha (p.reverse.append (q.concat hb))
      · simp only [Walk.length_append, Walk.length_reverse, Walk.length_concat, hplen, hqlen]
        omega
      · intro e he
        simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse] at he
        rcases he with he | he
        · exact hp'.2 e he
        · exact lt_of_le_of_lt (increasing_last_le hq e he) hgt

/-- Split a walk at a specified edge, retaining its genuine graph walks. -/
theorem split_at_mem_edge {u v : V} (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ a b, ∃ hab : G.Adj a b, ∃ l : G.Walk u a, ∃ q : G.Walk b v,
      e = s(a,b) ∧ p = l.append (.cons hab q) := by
  induction p with
  | nil => simp at he
  | @cons u z v huz p ih =>
    rcases List.mem_cons.mp he with he | he
    · exact ⟨u,z,huz,.nil,p,he,rfl⟩
    · obtain ⟨a,b,hab,l,q,he,hp⟩ := ih he
      exact ⟨a,b,hab,.cons huz l,q,he,by rw [hp]; rfl⟩

/-- Lemma 3.2: the maximum matching index on a short cycle is attained
by at least two distinct edges. -/
theorem short_cycle_max_twice {index : Sym2 V → ℕ} {s : ℕ}
    (H : EarlierFar G index s) {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    (hlen : p.length ≤ s+1) {e : Sym2 V} (he : e ∈ p.edges)
    (hmax : ∀ d ∈ p.edges, index d ≤ index e) :
    ∃ d ∈ p.edges, d ≠ e ∧ index d = index e := by
  classical
  by_contra hnone
  have hstrict : ∀ d ∈ p.edges, d ≠ e → index d < index e := by
    intro d hd hde
    exact lt_of_le_of_ne (hmax d hd) (fun hi => hnone ⟨d,hd,hde,hi⟩)
  obtain ⟨a,b,hab,l,q,rfl,rfl⟩ := split_at_mem_edge p he
  apply H b a hab.symm (q.append l)
  · simp only [Walk.length_append, Walk.length_cons] at hlen ⊢
    omega
  · intro d hd
    have hnd := hp.isTrail.edges_nodup
    simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append, List.nodup_cons] at hnd
    have hd' : d ∈ (l.append (.cons hab q)).edges ∧ d ≠ s(a,b) := by
      simp only [Walk.edges_append, List.mem_append] at hd
      rcases hd with hd | hd
      · exact ⟨by simp [hd], fun heq => hnd.2.1.1 (heq ▸ hd)⟩
      · exact ⟨by simp [hd], fun heq => hnd.2.2 d hd s(a,b) (by simp) heq⟩
    have hi := hstrict d hd'.1 hd'.2
    simpa only [Sym2.eq_swap] using hi

end LengthExpander
