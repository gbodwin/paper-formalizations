import VFTSpanners.Padding
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Limitation of edge blocking sets

The final construction of Bodwin–Patel, arXiv:1812.05778v2 (2019).
An independent `t`-fold blowup replaces each base edge by a complete bipartite
 graph between its two vertex fibers. This is the construction described in
the paper's last paragraph, rather than the graph-theoretic Cartesian product.
Blocking pairs here are ordered, so the bound also bounds unordered pairs.
-/

namespace VFTSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Distinct graph edges meeting every cycle of at most `k` edges. -/
def IsEdgeBlockingSet {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (B : Set (Sym2 V × Sym2 V)) : Prop :=
  (∀ ⦃e e'⦄, (e,e') ∈ B → e ∈ G.edgeSet ∧ e' ∈ G.edgeSet ∧ e ≠ e') ∧
  ∀ ⦃a⦄ (p : G.Walk a a), p.IsCycle → p.length ≤ k →
    ∃ e e', (e,e') ∈ B ∧ e ∈ p.edges ∧ e' ∈ p.edges

/-- Replace each vertex by an independent fiber of `t` vertices. -/
def independentBlowup {V : Type*} (G : SimpleGraph V) (t : ℕ) :
    SimpleGraph (V × Fin t) where
  Adj a b := G.Adj a.1 b.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h⟩

@[simp] theorem independentBlowup_adj {V : Type*} (G : SimpleGraph V) (t : ℕ)
    (a b : V × Fin t) : (independentBlowup G t).Adj a b ↔ G.Adj a.1 b.1 := Iff.rfl

/-- Projection to the original graph. -/
def blowupProjection {V : Type*} (G : SimpleGraph V) (t : ℕ) :
    independentBlowup G t →g G where
  toFun := Prod.fst
  map_rel' := id

/-- Darts lift independently at both endpoints. -/
def blowupDartEquiv {V : Type*} (G : SimpleGraph V) (t : ℕ) :
    (independentBlowup G t).Dart ≃ G.Dart × (Fin t × Fin t) where
  toFun d := (⟨(d.fst.1,d.snd.1),d.adj⟩,d.fst.2,d.snd.2)
  invFun d := ⟨((d.1.fst,d.2.1),(d.1.snd,d.2.2)),d.1.adj⟩
  left_inv d := by cases d; rfl
  right_inv d := by rcases d with ⟨⟨⟨a,b⟩,h⟩,i,j⟩; rfl

/-- The blowup has exactly `t²` edges per base edge. -/
theorem independentBlowup_edge_count {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ℕ) :
    (independentBlowup G t).edgeFinset.card = t^2 * G.edgeFinset.card := by
  classical
  have h := Fintype.card_congr (blowupDartEquiv G t)
  simp only [Fintype.card_prod, Fintype.card_fin,
    dart_card_eq_twice_card_edges] at h
  nlinarith

/-- A short walk without adjacent repeated edges is a path in a high-girth
 graph. This is the length-bounded version of the corresponding forest fact. -/
theorem HighGirth.isPath_of_isChain {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hg : HighGirth G k) {u v : V} (p : G.Walk u v)
    (hlen : p.length ≤ k) (h : List.IsChain (· ≠ ·) p.edges) : p.IsPath := by
  classical
  induction p with
  | nil => simp
  | @cons u' v' _ head tail ih =>
    have hcc := List.isChain_cons.mp (Walk.edges_cons _ _ ▸ h)
    have ht : tail.IsPath := ih (by simpa using Nat.le_of_succ_le hlen) hcc.2
    refine (Walk.cons_isPath_iff head tail).mpr ⟨ht, ?_⟩
    rcases tail.length.eq_zero_or_pos with h' | h'
    · simp [Walk.nil_iff_support_eq.mp (Walk.length_eq_zero_iff.mp h'), head.ne]
    · intro hh
      have hc : (Walk.cons head (tail.takeUntil u' hh)).IsCycle := by
        simp only [Walk.isCycle_def, Walk.isTrail_def, Walk.edges_cons, List.nodup_cons,
          ne_eq, reduceCtorEq, not_false_eq_true, Walk.support_cons, List.tail_cons, true_and]
        have hn : (Walk.cons head (tail.takeUntil u' hh)).support.tail.Nodup :=
          tail.isPath_def.mp ht |>.sublist <| List.IsInfix.sublist
            ⟨[], (tail.dropUntil u' hh).support.tail, by simp [← Walk.support_append]⟩
        refine ⟨⟨?_, Walk.edges_nodup_of_support_nodup hn⟩, hn⟩
        intro hhh
        refine hcc.1 s(u',v') ?_ rfl
        rw [← tail.cons_tail_eq (by simp [Walk.not_nil_iff_lt_length, h'])]
        have he := Walk.IsPath.mk' hn |>.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hhh)
        simp [he, Walk.snd_takeUntil head.ne]
      have hl := hg u' _ hc
      have htlen := tail.length_takeUntil_le_length hh
      simp only [Walk.length_cons] at hl hlen
      omega

/-- For each directed edge, pair its underlying edge with all other lifts at
 the opposite endpoint over the same base vertex. -/
noncomputable def blowupBlockingPairs {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ℕ) : Finset (Sym2 (V × Fin t) × Sym2 (V × Fin t)) := by
  classical
  exact Finset.univ.biUnion fun d : (independentBlowup G t).Dart =>
    (Finset.univ.erase d.snd.2).image fun j => (d.edge,s(d.fst,(d.snd.1,j)))

/-- Even counting ordered pairs, there are at most `2(t-1)` blockers per edge. -/
theorem blowupBlockingPairs_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ℕ) :
    (blowupBlockingPairs G t).card ≤ 2*(t-1)*(independentBlowup G t).edgeFinset.card := by
  classical
  unfold blowupBlockingPairs
  calc
    _ ≤ ∑ d : (independentBlowup G t).Dart,
        ((Finset.univ.erase d.snd.2).image fun j =>
          (d.edge,s(d.fst,(d.snd.1,j)))).card := Finset.card_biUnion_le
    _ ≤ ∑ d : (independentBlowup G t).Dart, (Finset.univ.erase d.snd.2).card := by
      apply Finset.sum_le_sum
      intro d _
      exact Finset.card_image_le
    _ = 2*(t-1)*(independentBlowup G t).edgeFinset.card := by
      simp [Finset.card_erase_of_mem, dart_card_eq_twice_card_edges]
      ring

/-- Every generated pair consists of distinct edges of the blowup. -/
theorem blowupBlockingPairs_valid {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ℕ) {e e' : Sym2 (V × Fin t)}
    (h : (e,e') ∈ blowupBlockingPairs G t) :
    e ∈ (independentBlowup G t).edgeSet ∧
    e' ∈ (independentBlowup G t).edgeSet ∧ e ≠ e' := by
  classical
  unfold blowupBlockingPairs at h
  obtain ⟨d, _, hd⟩ := Finset.mem_biUnion.mp h
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hd
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  refine ⟨d.edge_mem, d.adj, ?_⟩
  intro heq
  have hjne := (Finset.mem_erase.mp hj).1
  rcases Sym2.eq_iff.mp heq with h | h
  · exact hjne (congrArg Prod.snd h.2).symm
  · exact d.fst_ne_snd h.2.symm

/-- A projected backtrack along a genuine two-edge path supplies a blocker. -/
theorem blowup_adjacent_mem {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ℕ) {a b c : V × Fin t}
    (hab : (independentBlowup G t).Adj a b) (hac : a.1 = c.1) (hne : a ≠ c) :
    (s(a,b),s(b,c)) ∈ blowupBlockingPairs G t := by
  classical
  let d : (independentBlowup G t).Dart := ⟨(b,a),hab.symm⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨d, Finset.mem_univ _, Finset.mem_image.mpr ⟨c.2, ?_, ?_⟩⟩
  · apply Finset.mem_erase.mpr
    exact ⟨fun h => hne (Prod.ext hac h.symm), Finset.mem_univ _⟩
  · change (s(b,a),s(b,(a.1,c.2))) = (s(a,b),s(b,c))
    have hc : (a.1,c.2) = c := Prod.ext hac rfl
    simp [hc, Sym2.eq_swap]

/-- In a trail avoiding the proposed blocking pairs, its projected edges
 cannot immediately repeat. -/
theorem blowupProjection_edges_chain {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ℕ) {a b : V × Fin t}
    (p : (independentBlowup G t).Walk a b) (hp : p.IsTrail)
    (havoid : ∀ e ∈ p.edges, ∀ e' ∈ p.edges, (e,e') ∉ blowupBlockingPairs G t) :
    List.IsChain (· ≠ ·) (p.map (blowupProjection G t)).edges := by
  induction p with
  | nil => simp
  | @cons a b z hab p ih =>
    have ht := ih hp.of_cons (fun e he e' he' =>
      havoid e (List.mem_cons_of_mem _ he) e' (List.mem_cons_of_mem _ he'))
    cases p with
    | nil => simp
    | @cons b c z hbc q =>
      simp only [Walk.map_cons, Walk.edges_cons, List.isChain_cons_cons]
      refine ⟨?_, ht⟩
      intro he
      have hac : a.1 = c.1 := by
        change s(a.1,b.1) = s(b.1,c.1) at he
        rcases Sym2.eq_iff.mp he with h | h
        · exact ((show G.Adj a.1 b.1 from hab).ne h.1).elim
        · exact h.1
      have hacne : a ≠ c := by
        intro hac'
        have hn := (List.nodup_cons.mp hp.edges_nodup).1
        apply hn
        subst c
        exact List.mem_cons.mpr (Or.inl Sym2.eq_swap)
      apply havoid s(a,b) (by simp) s(b,c) (by simp)
      exact blowup_adjacent_mem G t hab hac hacne

/-- Every short cycle in the blowup contains two incident edges over the same
 base edge. The explicit pairs therefore form an edge blocking set. -/
theorem blowupBlockingPairs_isBlocking {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t k : ℕ) (hg : HighGirth G k) :
    IsEdgeBlockingSet (independentBlowup G t) k (blowupBlockingPairs G t : Set _) := by
  classical
  refine ⟨fun _ _ h => blowupBlockingPairs_valid G t h, ?_⟩
  intro a p hp hlen
  by_contra h
  have havoid : ∀ e ∈ p.edges, ∀ e' ∈ p.edges,
      (e,e') ∉ blowupBlockingPairs G t := by
    intro e he e' he' hb
    exact h ⟨e,e',hb,he,he'⟩
  have hpath := hg.isPath_of_isChain (p.map (blowupProjection G t))
    (by simpa using hlen) (blowupProjection_edges_chain G t p hp.isTrail havoid)
  have hn := Walk.isPath_iff_nil.mp hpath
  have hz : p.length = 0 := by
    simpa using Walk.length_eq_zero_iff.mpr hn
  have hthree := hp.three_le_length
  omega

/-- A finite maximizer exists for the paper's extremal function. -/
theorem exists_extremal_graph (n k : ℕ) :
    ∃ G : SimpleGraph (Fin n), HighGirth G k ∧ G.edgeFinset.card = extremalEdges n k := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := Finset.univ.filter fun G => HighGirth G k
  have hbot : HighGirth (⊥ : SimpleGraph (Fin n)) k := by
    intro a p hp
    cases p with
    | nil => exact (hp.ne_nil rfl).elim
    | cons h p => exact h.elim
  have hn : S.Nonempty := ⟨⊥, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbot⟩⟩
  obtain ⟨G,hG,hmax⟩ := Finset.exists_mem_eq_sup S hn (fun G => G.edgeFinset.card)
  exact ⟨G, (Finset.mem_filter.mp hG).2, hmax.symm⟩

/-- With no short cycles, the empty edge-blocking set suffices. -/
theorem HighGirth.edgeBlocking_empty {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hg : HighGirth G k) : IsEdgeBlockingSet G k ∅ := by
  refine ⟨by simp, ?_⟩
  intro a p hp hlen
  exact (not_lt_of_ge hlen (hg a p hp)).elim

/-- The `f = 1` limitation is witnessed directly by a high-girth extremal
 graph, with no blocking pairs at all. -/
theorem edge_blocking_limitation_one (n k : ℕ) :
    ∃ H : SimpleGraph (Fin n),
      H.edgeFinset.card = extremalEdges n k ∧
      IsEdgeBlockingSet H k ∅ := by
  obtain ⟨H,hg,hcard⟩ := exists_extremal_graph n k
  exact ⟨H,hcard,hg.edgeBlocking_empty⟩

/-- Exact finite limitation theorem, for arbitrary base size and blowup factor.
 The graph has `n*t` vertices and `t²*b(n,k)` edges, but only
 `2(t-1)` ordered blocking pairs per edge. -/
theorem edge_blocking_limitation (n t k : ℕ) :
    ∃ (H : SimpleGraph (Fin n × Fin t))
      (B : Finset (Sym2 (Fin n × Fin t) × Sym2 (Fin n × Fin t))),
      Fintype.card (Fin n × Fin t) = n*t ∧
      H.edgeFinset.card = t^2 * extremalEdges n k ∧
      IsEdgeBlockingSet H k (B : Set _) ∧
      B.card ≤ 2*(t-1)*H.edgeFinset.card := by
  classical
  obtain ⟨G,hg,hcount⟩ := exists_extremal_graph n k
  refine ⟨independentBlowup G t, blowupBlockingPairs G t, by simp, ?_,
    blowupBlockingPairs_isBlocking G t k hg, blowupBlockingPairs_card G t⟩
  rw [independentBlowup_edge_count, hcount]

/-- The paper's fault-budget specialization. For `f ≥ 2` this exhibits graphs
 with at least `f²*b(N/f,k)/9` edges and an edge blocking set of size at most
 `f*|E|`, where the exact vertex count is `N = n*floor(f/2)`.
 This proves a limitation of the blocking-set property, not an EFT-spanner
 lower bound or a claim that these graphs are EFT-greedy outputs. -/
theorem edge_blocking_limitation_faults (n f k : ℕ) (hf : 2 ≤ f) :
    ∃ (H : SimpleGraph (Fin n × Fin (f/2)))
      (B : Finset (Sym2 (Fin n × Fin (f/2)) × Sym2 (Fin n × Fin (f/2)))),
      H.edgeFinset.card = (f/2)^2 * extremalEdges n k ∧
      IsEdgeBlockingSet H k (B : Set _) ∧
      B.card ≤ f*H.edgeFinset.card ∧
      f^2 * extremalEdges (Fintype.card (Fin n × Fin (f/2)) / f) k ≤
        9*H.edgeFinset.card := by
  classical
  obtain ⟨H,B,hvertices,hcount,hB,hcard⟩ := edge_blocking_limitation n (f/2) k
  refine ⟨H,B,hcount,hB,?_,?_⟩
  · exact hcard.trans (Nat.mul_le_mul_right _ (by omega))
  · have hr : f ≤ 3*(f/2) := by omega
    have hr2 : f^2 ≤ 9*(f/2)^2 := by nlinarith
    have hnv : Fintype.card (Fin n × Fin (f/2)) / f ≤ n := by
      rw [hvertices]
      apply Nat.div_le_of_le_mul
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left n (Nat.div_le_self f 2)
    have hb := extremalEdges_mono hnv k
    calc
      _ ≤ f^2 * extremalEdges n k := Nat.mul_le_mul_left _ hb
      _ ≤ (9*(f/2)^2) * extremalEdges n k := Nat.mul_le_mul_right _ hr2
      _ = 9*H.edgeFinset.card := by rw [hcount]; ring

end VFTSpanners
