import LinearDistancePreservers.ModularDistance
import LinearDistancePreservers.WeightedNativeForcing

/-! The repaired modular construction has perfect paths in an actual graph:
native unique shortest paths cover exactly its edge set, with the previously
proved injective edge indexing. Consequently every subset distance preserver
on the first and last layers must retain all k*n*x edges. This is a building
block for Theorem 3, before the obstacle product and parameter assembly. -/
namespace LinearDistancePreservers.ModularGraph
open SimpleGraph Finset WeightedDigraph WeightedNativeForcing
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {n k x : ℕ} [NeZero n]

theorem step_true_arc {u v : Vertex n k} {a : Fin x} (h : Step u v true a) :
    ∃ e : Fin k × (ZMod n × Fin x), arc e = (u,v) := by
  obtain ⟨hl, hc⟩ := h
  simp only [ite_true] at hl hc
  let i : Fin k := ⟨u.1.val, by have := v.1.isLt; omega⟩
  let s : ZMod n := u.2 - (i.val : ZMod n)*(a.val : ZMod n)
  refine ⟨(i,s,a), ?_⟩
  apply Prod.ext <;> apply Prod.ext
  · apply Fin.ext
    rfl
  · simp [arc, point, s]
  · apply Fin.ext
    dsimp [arc, point, i]
    omega
  · dsimp [arc, point, s]
    push_cast
    linear_combination -hc

theorem adj_iff_arc (u v : Vertex n k) :
    (graph n k x).Adj u v ↔
      ∃ e : Fin k × (ZMod n × Fin x), arc e = (u,v) ∨ arc e = (v,u) := by
  constructor
  · rintro ⟨b, a, hl, hc⟩
    cases b
    · obtain ⟨e, he⟩ := step_true_arc (a := a) (u := v) (v := u)
        ⟨by simpa using (show (u.1.val : ℤ)-(v.1.val : ℤ) = 1 by simpa using neg_eq_iff_eq_neg.mpr hl),
          by simpa using (congrArg Neg.neg hc)⟩
      exact ⟨e, Or.inr he⟩
    · obtain ⟨e, he⟩ := step_true_arc ⟨hl, hc⟩
      exact ⟨e, Or.inl he⟩
  · rintro ⟨e, h | h⟩
    · have he := canonical_adj e.2.1 e.2.2 e.1
      change (graph n k x).Adj (arc e).1 (arc e).2 at he
      simpa [h] using he
    · have he := (canonical_adj e.2.1 e.2.2 e.1).symm
      change (graph n k x).Adj (arc e).2 (arc e).1 at he
      simpa [h] using he

theorem graph_edgeFinset :
    (graph n k x).edgeFinset = univ.image (undirectedEdge (n := n) (k := k) (x := x)) := by
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    simp only [mem_edgeFinset, mem_edgeSet, mem_image, mem_univ, true_and,
      undirectedEdge, adj_iff_arc]
    constructor
    · rintro ⟨e, he⟩
      exact ⟨e, Sym2.mk_eq_mk_iff.mpr he⟩
    · rintro ⟨e, he⟩
      exact ⟨e, Sym2.mk_eq_mk_iff.mp he⟩

theorem graph_edge_count (hx : x ≤ n) : (graph n k x).edgeFinset.card = k*n*x := by
  rw [graph_edgeFinset]
  exact undirected_edge_count hx

theorem canonical_edge_mem (s : ZMod n) (a : Fin x) (i : Fin k) :
    undirectedEdge (i,s,a) ∈ (canonicalWalk (k := k) s a).edges := by
  apply (canonicalWalk s a).mk_mem_edges_iff_exists.mpr
  refine ⟨i.val, by simpa using i.isLt, ?_⟩
  dsimp [undirectedEdge, arc]
  rw [show (canonicalWalk s a).getVert i.val = point s a i.castSucc from
    canonicalWalk_getVert s a i.castSucc,
    show (canonicalWalk s a).getVert (i.val+1) = point s a i.succ from
    canonicalWalk_getVert s a i.succ]

theorem canonical_covers (e : Sym2 (Vertex n k)) (he : e ∈ (graph n k x).edgeSet) :
    ∃ p : ZMod n × Fin x, e ∈ (canonicalWalk (k := k) p.1 p.2).edges := by
  have hmem : e ∈ (graph n k x).edgeFinset := by simpa using he
  rw [graph_edgeFinset] at hmem
  obtain ⟨⟨i,s,a⟩, _, rfl⟩ := mem_image.mp hmem
  exact ⟨(s,a), canonical_edge_mem s a i⟩

theorem canonical_shortest (hn : (k+1)*x ≤ n) (s : ZMod n) (a : Fin x)
    (q : (graph n k x).Walk (point s a 0) (point s a (Fin.last k))) :
    realCost (weight n k x) (canonicalWalk s a) ≤ realCost (weight n k x) q := by
  have hx : x ≤ n := (Nat.le_mul_of_pos_left x (by omega)).trans hn
  rw [realCost, canonical_native_cost hx]
  exact (native_optimal hn q).1

theorem canonical_unique (hn : (k+1)*x ≤ n) (s : ZMod n) (a : Fin x)
    (q : (graph n k x).Walk (point s a 0) (point s a (Fin.last k)))
    (he : realCost (weight n k x) q = realCost (weight n k x) (canonicalWalk s a)) :
    q = canonicalWalk s a := by
  have hx : x ≤ n := (Nat.le_mul_of_pos_left x (by omega)).trans hn
  unfold realCost at he
  rw [canonical_native_cost hx] at he
  apply SimpleGraph.Walk.ext_support
  rw [canonicalWalk_support]
  exact (native_optimal hn q).2 he

/-- An arbitrary subgraph preserving all designated distances is the whole
graph. Attainment and the bridge to infimum distances are proved internally. -/
theorem preserver_eq (hn : (k+1)*x ≤ n) (H : SimpleGraph (Vertex n k))
    (hsub : H ≤ graph n k x)
    (hpres : ∀ (s : ZMod n) (a : Fin x),
      distance H.Adj (fun u v => (weight n k x u v : ℝ≥0∞))
        (point s a 0) (point s a (Fin.last k)) =
      distance (graph n k x).Adj (fun u v => (weight n k x u v : ℝ≥0∞))
        (point s a 0) (point s a (Fin.last k))) : H = graph n k x := by
  exact WeightedNativeForcing.eq_of_covers (weight n k x)
    (fun p : ZMod n × Fin x => point p.1 p.2 0)
    (fun p => point p.1 p.2 (Fin.last k))
    (fun p => canonicalWalk p.1 p.2)
    (fun p => canonical_shortest hn p.1 p.2)
    (fun p => canonical_unique hn p.1 p.2) canonical_covers hsub
    (fun p => hpres p.1 p.2)

noncomputable def terminals (n k : ℕ) [NeZero n] : Finset (Vertex n k) :=
  univ.filter fun v => v.1 = 0 ∨ v.1 = Fin.last k

theorem point_start_mem (s : ZMod n) (a : Fin x) :
    point (k := k) s a 0 ∈ terminals n k := by simp [terminals, point]

theorem point_end_mem (s : ZMod n) (a : Fin x) :
    point (k := k) s a (Fin.last k) ∈ terminals n k := by simp [terminals, point]

theorem terminals_card (hk : 0 < k) : (terminals n k).card = 2*n := by
  have hset : terminals n k = ({0, Fin.last k} : Finset (Fin (k+1))).product univ := by
    ext v
    simp [terminals]
  have hne : (0 : Fin (k+1)) ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp [hset, Finset.product_eq_sprod, hne, ZMod.card]

theorem canonical_edges (s : ZMod n) (a : Fin x) :
    (canonicalWalk (k := k) s a).edges = List.ofFn (fun i : Fin k => undirectedEdge (i,s,a)) := by
  apply List.ext_getElem
  · simp [SimpleGraph.Walk.length_edges]
  · intro i hi hj
    rw [List.getElem_ofFn, SimpleGraph.Walk.getElem_edges]
    let j : Fin k := ⟨i, by simpa using hj⟩
    rw [show (canonicalWalk s a).getVert i = point s a j.castSucc from
      canonicalWalk_getVert s a j.castSucc,
      show (canonicalWalk s a).getVert (i+1) = point s a j.succ from
      canonicalWalk_getVert s a j.succ]
    rfl

/-- Every undirected edge lies on exactly one designated path, as required
by Definition 8, rather than merely being covered by the family. -/
theorem canonical_edge_owner_unique (hx : x ≤ n)
    (e : Sym2 (Vertex n k)) (he : e ∈ (graph n k x).edgeSet) :
    ∃! p : ZMod n × Fin x, e ∈ (canonicalWalk (k := k) p.1 p.2).edges := by
  obtain ⟨p, hp⟩ := canonical_covers e he
  refine ⟨p, hp, ?_⟩
  intro q hq
  rw [canonical_edges, List.mem_ofFn] at hp hq
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  exact congrArg Prod.snd (undirected_edge_injective hx (hj.trans hi.symm))

theorem canonical_isPath (s : ZMod n) (a : Fin x) :
    (canonicalWalk (k := k) s a).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, canonicalWalk_support]
  exact List.nodup_ofFn.mpr (designated_simple s a)

/-- With at least two layers, path labels index distinct native routes.
For one layer only the incidence count of indexed routes is asserted. -/
theorem canonical_support_injective (hx : x ≤ n) (hk : 0 < k) :
    Function.Injective (fun p : ZMod n × Fin x => (canonicalWalk (k := k) p.1 p.2).support) := by
  intro p q h
  apply designated_paths_injective hx hk
  apply List.ofFn_injective
  simpa only [canonicalWalk_support] using h

theorem canonical_mem_support_iff (s : ZMod n) (a : Fin x) (v : Vertex n k) :
    v ∈ (canonicalWalk (k := k) s a).support ↔ point s a v.1 = v := by
  rw [canonicalWalk_support, List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩
    have hlayer : i = v.1 := congrArg Prod.fst hi
    simpa [hlayer] using hi
  · intro h
    exact ⟨v.1, h⟩

/-- Exact regular path incidence in the native graph interpretation. -/
theorem canonical_incidence (v : Vertex n k) :
    Fintype.card {p : ZMod n × Fin x // v ∈ (canonicalWalk (k := k) p.1 p.2).support} = x := by
  let e : {p : ZMod n × Fin x // v ∈ (canonicalWalk (k := k) p.1 p.2).support} ≃
      {p : ZMod n × Fin x // point (k := k) p.1 p.2 v.1 = v} :=
    Equiv.subtypeEquivRight (fun p => canonical_mem_support_iff p.1 p.2 v)
  exact (Fintype.card_congr e).trans (paths_through_card v)

/-- A finite lower-bound building block stated directly for subset distance
preservers: the first and last layers force all k*n*x undirected edges. -/
theorem subset_preserver_edge_count (hn : (k+1)*x ≤ n)
    (H : SimpleGraph (Vertex n k)) (hsub : H ≤ graph n k x)
    (hpres : ∀ u ∈ terminals n k, ∀ v ∈ terminals n k,
      distance H.Adj (fun u v => (weight n k x u v : ℝ≥0∞)) u v =
      distance (graph n k x).Adj (fun u v => (weight n k x u v : ℝ≥0∞)) u v) :
    H.edgeFinset.card = k*n*x := by
  have heq := preserver_eq hn H hsub
    (fun s a => hpres _ (point_start_mem s a) _ (point_end_mem s a))
  rw [heq]
  exact graph_edge_count ((Nat.le_mul_of_pos_left x (by omega)).trans hn)

end LinearDistancePreservers.ModularGraph
