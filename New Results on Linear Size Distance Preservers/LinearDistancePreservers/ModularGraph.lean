import LinearDistancePreservers.QuadraticRepair
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sym.Sym2

/-! Finite modular graphs for the corrected construction in Theorem 5.
Vertices are (layer,column). Edges connect adjacent layers with a slope in
[0,x). `Walk` explicitly stores vertices and legal steps in this graph.
The corrected integer edge weight is k*x^2+1+a^2 for k+1 layers.
-/
namespace LinearDistancePreservers.ModularGraph
open Finset
open QuadraticRepair

abbrev Vertex (n k : ℕ) := Fin (k+1) × ZMod n

def point {n k x : ℕ} (s : ZMod n) (a : Fin x) (i : Fin (k+1)) : Vertex n k :=
  (i,s+(i.val : ZMod n)*(a.val : ZMod n))

structure Walk (n k x m : ℕ) where
  vertex : Fin (m+1) → Vertex n k
  forward : Fin m → Bool
  slope : Fin m → Fin x
  layer_step : ∀ i, ((vertex i.succ).1.val : ℤ) - ((vertex i.castSucc).1.val : ℤ) =
    if forward i then 1 else -1
  column_step : ∀ i, (vertex i.succ).2 - (vertex i.castSucc).2 =
    if forward i then ((slope i).val : ZMod n) else -((slope i).val : ZMod n)

/-- The designated constant-slope path is a walk in the finite graph. -/
def canonical {n k x : ℕ} (s : ZMod n) (a : Fin x) : Walk n k x k where
  vertex := point s a
  forward := fun _ => true
  slope := fun _ => a
  layer_step := by intro i; simp [point]
  column_step := by intro i; simp [point,Nat.cast_add]; ring

/-- Telescoping the local step equations gives the endpoint equation. -/
theorem telescope {A : Type*} [AddCommGroup A] {m : ℕ} (f : Fin (m+1) → A) :
    (∑ i : Fin m, (f i.succ - f i.castSucc)) = f (Fin.last m) - f 0 := by
  have h1 := Fin.sum_univ_succ f
  have h2 := Fin.sum_univ_castSucc f
  rw [sum_sub_distrib]
  apply sub_eq_sub_iff_add_eq_add.mpr
  calc
    (∑ i : Fin m, f i.succ) + f 0 = ∑ i, f i := by rw [h1]; abel
    _ = f (Fin.last m) + ∑ i : Fin m, f i.castSucc := by rw [h2]; abel

namespace Walk
variable {n k x m : ℕ} (W : Walk n k x m)

theorem height_endpoint : height W.forward =
    ((W.vertex (Fin.last m)).1.val : ℤ) - ((W.vertex 0).1.val : ℤ) := by
  rw [← telescope (fun i => ((W.vertex i).1.val : ℤ))]
  exact sum_congr rfl fun i _ => (W.layer_step i).symm

theorem column_endpoint : (displacement W.forward (fun i => (W.slope i).val) : ZMod n) =
    (W.vertex (Fin.last m)).2 - (W.vertex 0).2 := by
  rw [← telescope (fun i => (W.vertex i).2)]
  simp only [displacement,Int.cast_sum]
  apply sum_congr rfl
  intro i _
  rw [W.column_step i]
  cases W.forward i <;> simp

/-- For fixed steps and initial vertex there is only one vertex sequence. -/
theorem vertices_of_forward_constant {s : ZMod n} {a : Fin x} (W : Walk n k x k)
    (hs : W.vertex 0 = point s a 0)
    (hf : ∀ i, W.forward i = true) (ha : ∀ i, W.slope i = a) :
    W.vertex = point s a := by
  funext i
  induction i using Fin.induction with
  | zero => exact hs
  | succ i ih =>
    have hl := W.layer_step i
    have hc := W.column_step i
    rw [hf i,ha i] at hc
    rw [hf i] at hl
    simp only [ite_true] at hl hc
    rw [ih] at hl hc
    apply Prod.ext
    · apply Fin.ext
      simp only [point,Fin.val_succ,Fin.val_castSucc] at *
      omega
    · simp only [point,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one] at *
      linear_combination hc

/-- Corrected unique-shortest-path statement in the explicit finite graph.
Equality forces the length, all directions and all slopes of the canonical
path. `vertices_of_forward_constant` then identifies its vertex sequence. -/
theorem optimal {s : ZMod n} {a : Fin x}
    (hn : (k+1)*x ≤ n)
    (hs : W.vertex 0 = point s a 0)
    (ht : W.vertex (Fin.last m) = point s a (Fin.last k)) :
    (k:ℤ)*(baseline k x+(a.val:ℤ)^2) ≤ cost k x (fun i => (W.slope i).val) ∧
    (cost k x (fun i => (W.slope i).val) = (k:ℤ)*(baseline k x+(a.val:ℤ)^2) →
      m = k ∧ (∀ i, W.forward i = true) ∧ (∀ i, W.slope i = a)) := by
  have hh : height W.forward = (k:ℤ) := by
    rw [W.height_endpoint,hs,ht]
    simp [point]
  have hc : displacement W.forward (fun i => (W.slope i).val) % (n:ℤ) =
      ((k:ℤ)*a.val) % (n:ℤ) := by
    apply (ZMod.intCast_eq_intCast_iff' _ _ n).mp
    rw [W.column_endpoint,hs,ht]
    simp [point]
  obtain ⟨hl,he⟩ := constant_slope_unique_shortest a.isLt hn W.forward
    (fun i => (W.slope i).val) (fun i => (W.slope i).isLt) hh hc
  refine ⟨hl,fun h => ?_⟩
  obtain ⟨hm,hf,ha⟩ := he h
  exact ⟨hm,hf,fun i => Fin.ext (ha i)⟩

/-- Equality identifies the full vertex sequence, including its length. -/
theorem unique_vertex_sequence {s : ZMod n} {a : Fin x}
    (hn : (k+1)*x ≤ n)
    (hs : W.vertex 0 = point s a 0)
    (ht : W.vertex (Fin.last m) = point s a (Fin.last k))
    (heq : cost k x (fun i => (W.slope i).val) = (k:ℤ)*(baseline k x+(a.val:ℤ)^2)) :
    m = k ∧ HEq W.vertex (point (k := k) s a) := by
  obtain ⟨hm,hf,ha⟩ := (W.optimal hn hs ht).2 heq
  subst m
  exact ⟨rfl,heq_of_eq (W.vertices_of_forward_constant hs hf ha)⟩

end Walk

@[simp] theorem canonical_cost {n k x : ℕ} (s : ZMod n) (a : Fin x) :
    cost k x (fun i => ((canonical (k := k) s a).slope i).val) =
      (k:ℤ)*(baseline k x+(a.val:ℤ)^2) := by
  simp [cost,canonical]

/-- There are exactly x designated paths through any given vertex. -/
def pathsThroughEquiv {n k x : ℕ} (v : Vertex n k) :
    {p : ZMod n × Fin x // point (k := k) p.1 p.2 v.1 = v} ≃ Fin x where
  toFun p := p.val.2
  invFun a := ⟨(v.2-(v.1.val:ZMod n)*(a.val:ZMod n),a),by
    apply Prod.ext
    · rfl
    · simp [point]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · have h := congrArg Prod.snd p.property
      simp only [point] at h
      exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h.symm)
    · rfl
  right_inv a := rfl

theorem paths_through_card {n k x : ℕ} [NeZero n] (v : Vertex n k) :
    Fintype.card {p : ZMod n × Fin x // point (k := k) p.1 p.2 v.1 = v} = x := by
  classical
  exact (Fintype.card_congr (pathsThroughEquiv v)).trans (Fintype.card_fin x)

theorem vertices_card (n k : ℕ) [NeZero n] : Fintype.card (Vertex n k) = (k+1)*n := by
  simp [Vertex,ZMod.card]

theorem designated_paths_card (n x : ℕ) [NeZero n] : Fintype.card (ZMod n × Fin x) = n*x := by
  simp [ZMod.card]


/-- Increasing-layer orientations of the undirected edges. Each edge belongs
to the designated path indexed by the label's second component. -/
def arc {n k x : ℕ} (e : Fin k × (ZMod n × Fin x)) : Vertex n k × Vertex n k :=
  (point e.2.1 e.2.2 e.1.castSucc,point e.2.1 e.2.2 e.1.succ)

/-- No two path/position labels describe the same graph edge. -/
theorem arc_injective {n k x : ℕ} (hx : x ≤ n) :
    Function.Injective (arc (n := n) (k := k) (x := x)) := by
  rintro ⟨i,s,a⟩ ⟨j,t,b⟩ he
  have hi : i = j := by
    apply Fin.ext
    have := congrArg (fun e : Vertex n k × Vertex n k => e.1.1.val) he
    exact this
  subst j
  have h0 := congrArg (fun e : Vertex n k × Vertex n k => e.1.2) he
  have h1 := congrArg (fun e : Vertex n k × Vertex n k => e.2.2) he
  simp only [arc,point,Fin.val_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one] at h0 h1
  have hab : (a.val : ZMod n) = (b.val : ZMod n) := by linear_combination h1-h0
  have hab' : a = b := by
    apply Fin.ext
    have hv := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt (lt_of_lt_of_le a.isLt hx),
      ZMod.val_natCast_of_lt (lt_of_lt_of_le b.isLt hx)] using hv
  subst b
  have hst : s = t := add_right_cancel h0
  subst t
  rfl

/-- Since edges have a unique increasing-layer orientation, this is also
an undirected edge count. -/
theorem edge_count {n k x : ℕ} [NeZero n] (hx : x ≤ n) :
    (Finset.univ.image (arc (n := n) (k := k) (x := x))).card = k*n*x := by
  rw [Finset.card_image_of_injective _ (arc_injective hx)]
  simp [ZMod.card,mul_assoc]

/-- With at least two layers the indexed designated paths are distinct. -/
theorem designated_paths_injective {n k x : ℕ} (hx : x ≤ n) (hk : 0 < k) :
    Function.Injective (fun p : ZMod n × Fin x => point (k := k) p.1 p.2) := by
  intro p q he
  let i : Fin k := ⟨0,hk⟩
  have harc : arc (i,p) = arc (i,q) := by
    apply Prod.ext
    · exact congrFun he i.castSucc
    · exact congrFun he i.succ
  exact congrArg Prod.snd (arc_injective hx harc)

/-- A designated route is simple, since its layer increases at every step. -/
theorem designated_simple {n k x : ℕ} (s : ZMod n) (a : Fin x) :
    Function.Injective (point (k := k) s a) := by
  intro i j h
  exact congrArg Prod.fst h


/-- An increasing-layer arc cannot equal a reversed increasing-layer arc. -/
theorem arc_ne_swap {n k x : ℕ} (e f : Fin k × (ZMod n × Fin x)) :
    arc e ≠ (arc f).swap := by
  intro h
  have h1 := congrArg (fun z : Vertex n k × Vertex n k => z.1.1.val) h
  have h2 := congrArg (fun z : Vertex n k × Vertex n k => z.2.1.val) h
  simp only [arc,point,Prod.swap,Fin.val_succ,Fin.val_castSucc] at h1 h2
  omega

def undirectedEdge {n k x : ℕ} (e : Fin k × (ZMod n × Fin x)) : Sym2 (Vertex n k) :=
  Sym2.mk (arc e).1 (arc e).2

theorem undirected_edge_injective {n k x : ℕ} (hx : x ≤ n) :
    Function.Injective (undirectedEdge (n := n) (k := k) (x := x)) := by
  intro e f h
  rcases Sym2.mk_eq_mk_iff.mp h with h | h
  · exact arc_injective hx h
  · exact False.elim (arc_ne_swap e f h)

/-- The undirected graph has exactly k*n*x edges, each owned by a unique
position on a unique designated path. -/
theorem undirected_edge_count {n k x : ℕ} [NeZero n] (hx : x ≤ n) :
    (Finset.univ.image (undirectedEdge (n := n) (k := k) (x := x))).card = k*n*x := by
  rw [Finset.card_image_of_injective _ (undirected_edge_injective hx)]
  simp [ZMod.card,mul_assoc]

end LinearDistancePreservers.ModularGraph
