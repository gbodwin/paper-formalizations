import LinearDistancePreservers.DirectionGraph
import LinearDistancePreservers.PathLowerBound

/-! Exact finite combinatorics for Theorem 6's vector construction.
Distinct bounded directions index edge-disjoint canonical paths, each
vertex has exactly |J| incident paths, and the graph has k n^d |J| edges.
Average rigidity supplies unique shortest paths and forces every edge.
This does not supply the sharp number of convex lattice directions. -/
namespace LinearDistancePreservers.DirectionGraph
open SimpleGraph Finset WeightedDigraph WeightedNativeForcing
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {D J : Type*} {n k r : ℕ}

def arc (v : J → D → ℕ) (e : Fin k × ((D → ZMod n) × J)) : Vertex D n k × Vertex D n k :=
  (point v e.2.1 e.2.2 e.1.castSucc,point v e.2.1 e.2.2 e.1.succ)

def undirectedEdge (v : J → D → ℕ) (e : Fin k × ((D → ZMod n) × J)) : Sym2 (Vertex D n k) :=
  Sym2.mk (arc v e).1 (arc v e).2

theorem arc_injective (v : J → D → ℕ) (hv : ∀ a d, v a d < n)
    (hinj : Function.Injective v) : Function.Injective (arc (n := n) (k := k) v) := by
  rintro ⟨i,s,a⟩ ⟨j,t,b⟩ he
  have hi : i = j := Fin.ext (congrArg (fun e : Vertex D n k × Vertex D n k => e.1.1.val) he)
  subst j
  have h0 (d : D) := congrArg (fun e : Vertex D n k × Vertex D n k => e.1.2 d) he
  have h1 (d : D) := congrArg (fun e : Vertex D n k × Vertex D n k => e.2.2 d) he
  simp only [arc,point,Fin.val_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one] at h0 h1
  have hab : a = b := by
    apply hinj
    funext d
    have hh : (v a d : ZMod n) = (v b d : ZMod n) := by linear_combination h1 d - h0 d
    have hh' := congrArg ZMod.val hh
    simpa [ZMod.val_natCast_of_lt (hv a d),ZMod.val_natCast_of_lt (hv b d)] using hh'
  subst b
  have hst : s = t := funext (fun d => add_right_cancel (h0 d))
  subst t
  rfl

theorem arc_ne_swap (v : J → D → ℕ) (e f : Fin k × ((D → ZMod n) × J)) :
    arc v e ≠ (arc v f).swap := by
  intro h
  have h1 := congrArg (fun z : Vertex D n k × Vertex D n k => z.1.1.val) h
  have h2 := congrArg (fun z : Vertex D n k × Vertex D n k => z.2.1.val) h
  simp only [arc,point,Prod.swap,Fin.val_succ,Fin.val_castSucc] at h1 h2
  omega

theorem undirected_edge_injective (v : J → D → ℕ) (hv : ∀ a d, v a d < n)
    (hinj : Function.Injective v) : Function.Injective (undirectedEdge (n := n) (k := k) v) := by
  intro e f h
  rcases Sym2.mk_eq_mk_iff.mp h with h | h
  · exact arc_injective v hv hinj h
  · exact False.elim (arc_ne_swap v e f h)

theorem step_true_arc (v : J → D → ℕ) {u w : Vertex D n k} {a : J}
    (h : Step v u w true a) : ∃ e : Fin k × ((D → ZMod n) × J), arc v e = (u,w) := by
  obtain ⟨hl,hc⟩ := h
  simp only [ite_true] at hl hc
  let i : Fin k := ⟨u.1.val,by have := w.1.isLt; omega⟩
  let s : D → ZMod n := fun d => u.2 d - (i.val : ZMod n)*(v a d : ZMod n)
  refine ⟨(i,s,a),?_⟩
  apply Prod.ext <;> apply Prod.ext
  · apply Fin.ext; rfl
  · funext d; simp [arc,point,s]
  · apply Fin.ext; dsimp [arc,point,i]; omega
  · funext d
    dsimp [arc,point,s]
    push_cast
    linear_combination -(hc d)

theorem adj_iff_arc (v : J → D → ℕ) (u w : Vertex D n k) :
    (graph v n k).Adj u w ↔
      ∃ e : Fin k × ((D → ZMod n) × J), arc v e = (u,w) ∨ arc v e = (w,u) := by
  constructor
  · rintro ⟨b,a,hl,hc⟩
    cases b
    · have hs : Step v w u true a := by
        refine ⟨?_,?_⟩
        · simp only [Bool.false_eq_true,ite_false] at hl
          simp only [ite_true]
          omega
        · intro d
          have hh := hc d
          simp only [Bool.false_eq_true,ite_false] at hh
          simp only [ite_true]
          linear_combination -hh
      obtain ⟨e,he⟩ := step_true_arc v hs
      exact ⟨e,Or.inr he⟩
    · obtain ⟨e,he⟩ := step_true_arc v ⟨hl,hc⟩
      exact ⟨e,Or.inl he⟩
  · rintro ⟨e,h | h⟩
    · have he := canonical_adj v e.2.1 e.2.2 e.1
      change (graph v n k).Adj (arc v e).1 (arc v e).2 at he
      simpa [h] using he
    · have he := (canonical_adj v e.2.1 e.2.2 e.1).symm
      change (graph v n k).Adj (arc v e).2 (arc v e).1 at he
      simpa [h] using he

theorem canonical_getVert (v : J → D → ℕ) (s : D → ZMod n) (a : J) (i : Fin (k+1)) :
    (canonicalWalk v s a).getVert i.val = point v s a i := by
  simpa only [canonical_support,List.getElem_ofFn] using
    (canonicalWalk (k := k) v s a).getVert_eq_support_getElem
      (show i.val ≤ (canonicalWalk v s a).length by simp; omega)

theorem canonical_edges (v : J → D → ℕ) (s : D → ZMod n) (a : J) :
    (canonicalWalk (k := k) v s a).edges = List.ofFn (fun i : Fin k => undirectedEdge v (i,s,a)) := by
  apply List.ext_getElem
  · simp [Walk.length_edges]
  · intro i hi hj
    rw [List.getElem_ofFn,Walk.getElem_edges]
    let j : Fin k := ⟨i,by simpa using hj⟩
    rw [show (canonicalWalk v s a).getVert i = point v s a j.castSucc from
      canonical_getVert v s a j.castSucc,
      show (canonicalWalk v s a).getVert (i+1) = point v s a j.succ from
      canonical_getVert v s a j.succ]
    rfl

theorem canonical_isPath (v : J → D → ℕ) (s : D → ZMod n) (a : J) :
    (canonicalWalk (k := k) v s a).IsPath := by
  rw [Walk.isPath_def,canonical_support]
  exact List.nodup_ofFn.mpr (fun i j h => congrArg Prod.fst h)

/-- With at least two layers the path labels are distinct native paths.
For k=0 only the count of indexed routes is asserted. -/
theorem canonical_support_injective (v : J → D → ℕ) (hv : ∀ a d, v a d < n)
    (hinj : Function.Injective v) (hk : 0 < k) :
    Function.Injective (fun p : (D → ZMod n) × J => (canonicalWalk (k := k) v p.1 p.2).support) := by
  intro p q h
  have he : point (k := k) v p.1 p.2 = point v q.1 q.2 :=
    List.ofFn_injective (by simpa only [canonical_support] using h)
  let i : Fin k := ⟨0,hk⟩
  have ha : arc v (i,p) = arc v (i,q) :=
    Prod.ext (congrFun he i.castSucc) (congrFun he i.succ)
  exact congrArg Prod.snd (arc_injective v hv hinj ha)

theorem canonical_mem_support_iff (v : J → D → ℕ) (s : D → ZMod n) (a : J) (u : Vertex D n k) :
    u ∈ (canonicalWalk v s a).support ↔ point v s a u.1 = u := by
  rw [canonical_support,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    have hl : i = u.1 := congrArg Prod.fst hi
    simpa [hl] using hi
  · intro h; exact ⟨u.1,h⟩

def pathsThroughEquiv (v : J → D → ℕ) (u : Vertex D n k) :
    {p : (D → ZMod n) × J // point v p.1 p.2 u.1 = u} ≃ J where
  toFun p := p.val.2
  invFun a := ⟨(fun d => u.2 d - (u.1.val : ZMod n)*(v a d : ZMod n),a),by
    apply Prod.ext
    · rfl
    · funext d; simp [point]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · funext d
      have h := congrArg (fun z : Vertex D n k => z.2 d) p.property
      simp only [point] at h
      exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h.symm)
    · rfl
  right_inv a := rfl

variable [Fintype D] [Fintype J] [NeZero n]

theorem vertex_count : Fintype.card (Vertex D n k) = (k+1)*n^(Fintype.card D) := by
  simp [Vertex,ZMod.card]

theorem path_count : Fintype.card ((D → ZMod n) × J) = n^(Fintype.card D)*Fintype.card J := by
  simp [ZMod.card]

theorem graph_edgeFinset (v : J → D → ℕ) :
    (graph v n k).edgeFinset = univ.image (undirectedEdge v) := by
  ext e
  induction e using Sym2.inductionOn with
  | hf u w =>
    simp only [mem_edgeFinset,mem_edgeSet,mem_image,mem_univ,true_and,undirectedEdge,adj_iff_arc]
    constructor
    · rintro ⟨e,he⟩; exact ⟨e,Sym2.mk_eq_mk_iff.mpr he⟩
    · rintro ⟨e,he⟩; exact ⟨e,Sym2.mk_eq_mk_iff.mp he⟩

theorem graph_edge_count (v : J → D → ℕ) (hv : ∀ a d, v a d < n) (hinj : Function.Injective v) :
    (graph v n k).edgeFinset.card = k*n^(Fintype.card D)*Fintype.card J := by
  rw [graph_edgeFinset,card_image_of_injective _ (undirected_edge_injective v hv hinj)]
  simp [ZMod.card,mul_assoc]

theorem canonical_covers (v : J → D → ℕ) (e : Sym2 (Vertex D n k))
    (he : e ∈ (graph v n k).edgeSet) :
    ∃ p : (D → ZMod n) × J, e ∈ (canonicalWalk v p.1 p.2).edges := by
  have hmem : e ∈ (graph v n k).edgeFinset := by simpa using he
  rw [graph_edgeFinset] at hmem
  obtain ⟨⟨i,s,a⟩,_,rfl⟩ := mem_image.mp hmem
  refine ⟨(s,a),?_⟩
  rw [canonical_edges,List.mem_ofFn]
  exact ⟨i,rfl⟩

theorem canonical_edge_owner_unique (v : J → D → ℕ) (hv : ∀ a d, v a d < n)
    (hinj : Function.Injective v) (e : Sym2 (Vertex D n k)) (he : e ∈ (graph v n k).edgeSet) :
    ∃! p : (D → ZMod n) × J, e ∈ (canonicalWalk v p.1 p.2).edges := by
  obtain ⟨p,hp⟩ := canonical_covers v e he
  refine ⟨p,hp,?_⟩
  intro q hq
  rw [canonical_edges,List.mem_ofFn] at hp hq
  obtain ⟨i,hi⟩ := hp
  obtain ⟨j,hj⟩ := hq
  exact congrArg Prod.snd (undirected_edge_injective v hv hinj (hj.trans hi.symm))

theorem canonical_incidence (v : J → D → ℕ) (u : Vertex D n k) :
    Fintype.card {p : (D → ZMod n) × J // u ∈ (canonicalWalk v p.1 p.2).support} = Fintype.card J := by
  let e : {p : (D → ZMod n) × J // u ∈ (canonicalWalk v p.1 p.2).support} ≃
      {p : (D → ZMod n) × J // point v p.1 p.2 u.1 = u} :=
    Equiv.subtypeEquivRight (fun p => canonical_mem_support_iff v p.1 p.2 u)
  exact (Fintype.card_congr e).trans (Fintype.card_congr (pathsThroughEquiv v u))

/-- All edges are forced by the designated endpoint pairs, for ordinary
unweighted distances (represented by unit weights in the shared metric). -/
theorem preserver_eq (v : J → D → ℕ) (hv : ∀ a d, v a d < r)
    (hn : (k+1)*r ≤ n) (hrigid : AverageRigid v) (H : SimpleGraph (Vertex D n k))
    (hsub : H ≤ graph v n k)
    (hpres : ∀ (s : D → ZMod n) (a : J),
      distance H.Adj (fun _ _ => 1) (point v s a 0) (point v s a (Fin.last k)) =
      distance (graph v n k).Adj (fun _ _ => 1) (point v s a 0) (point v s a (Fin.last k))) :
    H = graph v n k := by
  classical
  apply WeightedNativeForcing.eq_of_covers (fun _ _ => 1)
    (fun p : (D → ZMod n) × J => point v p.1 p.2 0)
    (fun p => point v p.1 p.2 (Fin.last k)) (fun p => canonicalWalk v p.1 p.2)
  · intro p q
    rw [PathLowerBound.realCost_one,PathLowerBound.realCost_one,canonical_length]
    have hh := LayeredWalks.layer_le_length (fun u => (u.1.val : ℤ)) (graph_layered v) q
    have hh' : (k : ℤ) ≤ q.length := by simpa [point] using hh
    exact_mod_cast hh'
  · intro p q he
    apply canonical_unique v hv hn hrigid p.1 p.2 q
    simp only [PathLowerBound.realCost_one,canonical_length] at he
    exact_mod_cast he.le
  · exact canonical_covers v
  · exact hsub
  · intro p; simpa using hpres p.1 p.2

end LinearDistancePreservers.DirectionGraph
