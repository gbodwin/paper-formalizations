import LinearDistancePreservers.ConvexDirections
import LinearDistancePreservers.LayeredWalks
import LinearDistancePreservers.ModularGraph

/-! The native unweighted graph behind Theorem 6. Bounded integer
directions with the stated average-rigidity property give unique shortest
paths. The property is about integer vectors, not graph distances. Common
sphere directions supply a proved special case; sharp direction counts
are not asserted here. -/
namespace LinearDistancePreservers.DirectionGraph
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {D J : Type*} {n k r : ℕ}

abbrev Vertex (D : Type*) (n k : ℕ) := Fin (k+1) × (D → ZMod n)

def point (v : J → D → ℕ) (s : D → ZMod n) (a : J) (i : Fin (k+1)) : Vertex D n k :=
  (i,fun d => s d + (i.val : ZMod n)*(v a d : ZMod n))

def Step (v : J → D → ℕ) (u w : Vertex D n k) (b : Bool) (a : J) : Prop :=
  (w.1.val : ℤ) - u.1.val = (if b then 1 else -1) ∧
    ∀ d, w.2 d - u.2 d = (if b then (v a d : ZMod n) else -(v a d : ZMod n))

def graph (v : J → D → ℕ) (n k : ℕ) : SimpleGraph (Vertex D n k) where
  Adj u w := ∃ b a, Step v u w b a
  symm := ⟨by
    rintro u w ⟨b,a,hl,hc⟩
    refine ⟨!b,a,?_⟩
    cases b <;> simp only [Step,Bool.not_false,Bool.not_true,Bool.false_eq_true,
      ite_false,ite_true] at * <;> constructor
    · omega
    · intro d; linear_combination -(hc d)
    · omega
    · intro d; linear_combination -(hc d)⟩
  loopless := ⟨by rintro u ⟨b,a,h,_⟩; cases b <;> simp at h⟩

theorem graph_layered (v : J → D → ℕ) :
    LayeredWalks.Layered (graph v n k) (fun u => (u.1.val : ℤ)) := by
  rintro u w ⟨b,a,h,_⟩
  cases b
  · exact Or.inr h
  · exact Or.inl h

theorem canonical_adj (v : J → D → ℕ) (s : D → ZMod n) (a : J) (i : Fin k) :
    (graph v n k).Adj (point v s a i.castSucc) (point v s a i.succ) := by
  refine ⟨true,a,?_,?_⟩
  · simp [point]
  · intro d; simp [point,Nat.cast_add]; ring

def canonicalWalk (v : J → D → ℕ) (s : D → ZMod n) (a : J) :
    (graph v n k).Walk (point v s a 0) (point v s a (Fin.last k)) :=
  walkOfSequence (point v s a) (canonical_adj v s a)

@[simp] theorem canonical_length (v : J → D → ℕ) (s : D → ZMod n) (a : J) :
    (canonicalWalk (k := k) v s a).length = k := length_walkOfSequence _ _

theorem canonical_support (v : J → D → ℕ) (s : D → ZMod n) (a : J) :
    (canonicalWalk (k := k) v s a).support = List.ofFn (point v s a) :=
  support_walkOfSequence _ _

/-- A finite average of allowed vectors equalling an allowed vector is
constant. This is the geometric input, before any graph construction. -/
def AverageRigid (v : J → D → ℕ) : Prop :=
  ∀ (m : ℕ) (a : J) (f : Fin m → J),
    (∀ d, ∑ i, (v (f i) d : ℤ) = (m : ℤ)*(v a d : ℤ)) →
      ∀ i, v (f i) = v a

theorem sphere_rigid [Fintype D] (v : J → D → ℕ)
    (hs : ∀ a b, ∑ d, (v a d : ℤ)^2 = ∑ d, (v b d : ℤ)^2) : AverageRigid v := by
  intro m a f hsum
  have h := ConvexDirections.sphere_average_unique (fun i d => (v (f i) d : ℤ))
    (fun d => (v a d : ℤ)) (fun i => hs (f i) a) hsum
  intro i
  funext d
  exact_mod_cast congrFun (h i) d

/-- Theorem 6's shortest-path argument, with the no-wrap inequality
explicit and all undirected competitors included. -/
theorem canonical_unique (v : J → D → ℕ)
    (hv : ∀ a d, v a d < r) (hn : (k+1)*r ≤ n) (hrigid : AverageRigid v)
    (s : D → ZMod n) (a : J)
    (q : (graph v n k).Walk (point v s a 0) (point v s a (Fin.last k)))
    (hq : q.length ≤ k) : q = canonicalWalk v s a := by
  have hlo := LayeredWalks.layer_le_length (fun u => (u.1.val : ℤ)) (graph_layered v) q
  have hlo' : (k : ℤ) ≤ q.length := by
    simpa only [point,Fin.val_zero,Fin.val_last,Nat.cast_zero,sub_zero] using hlo
  have hlen : q.length = k := by omega
  have hrise := LayeredWalks.tight_walk_rises (fun u => (u.1.val : ℤ)) (graph_layered v) q
    (by change (k : ℤ)-0 = (q.length : ℤ); omega)
  have hstep (i : Fin k) : ((q.getVert (i.val+1)).1.val : ℤ) =
      (q.getVert i.val).1.val + 1 := by
    have hi : i.val < q.darts.length := by simp [hlen]
    have hh := hrise q.darts[i.val] (List.getElem_mem hi)
    simpa only [Walk.darts_getElem_eq_getVert] using hh
  have hdir (i : Fin k) : ∃ b : J, ∀ d,
      (q.getVert (i.val+1)).2 d - (q.getVert i.val).2 d = (v b d : ZMod n) := by
    obtain ⟨b,j,hl,hc⟩ := q.adj_getVert_succ (show i.val < q.length by omega)
    cases b
    · have hh := hstep i
      simp only [Bool.false_eq_true,ite_false] at hl
      omega
    · exact ⟨j,hc⟩
  let f : Fin k → J := fun i => (hdir i).choose
  have hcol (i : Fin k) (d : D) :
      (q.getVert (i.val+1)).2 d - (q.getVert i.val).2 d = (v (f i) d : ZMod n) :=
    (hdir i).choose_spec d
  have hsum (d : D) : ∑ i, (v (f i) d : ZMod n) = (k : ZMod n)*(v a d : ZMod n) := by
    calc
      _ = ∑ i : Fin k, ((q.getVert i.succ.val).2 d - (q.getVert i.castSucc.val).2 d) :=
        sum_congr rfl (fun i _ => (hcol i d).symm)
      _ = (q.getVert k).2 d - (q.getVert 0).2 d :=
        ModularGraph.telescope (fun i : Fin (k+1) => (q.getVert i.val).2 d)
      _ = _ := by
        have hend : q.getVert k = point v s a (Fin.last k) := by
          simpa only [hlen] using q.getVert_length
        rw [hend,Walk.getVert_zero]
        simp [point]
  have hconst := hrigid k a f
    (ConvexDirections.no_wrap_sum (fun i => v (f i)) (v a) (fun i => hv (f i)) (hv a) hn hsum)
  have hvertices (i : Fin (k+1)) : q.getVert i.val = point v s a i := by
    induction i using Fin.induction with
    | zero => simp
    | succ i ih =>
      have hl := hstep i
      apply Prod.ext
      · apply Fin.ext
        have hp : (q.getVert i.val).1.val = i.val := congrArg (fun u => u.1.val) ih
        change (q.getVert (i.val+1)).1.val = i.val+1
        omega
      · funext d
        have hc := hcol i d
        rw [hconst i] at hc
        have hp : (q.getVert i.val).2 d = s d + (i.val : ZMod n)*(v a d : ZMod n) :=
          congrArg (fun u => u.2 d) ih
        change (q.getVert (i.val+1)).2 d = s d + ((i.val+1 : ℕ) : ZMod n)*(v a d : ZMod n)
        push_cast
        linear_combination hc + hp
  apply Walk.ext_support
  rw [support_eq_ofFn,canonical_support]
  simp only [hlen]
  exact congrArg List.ofFn (funext hvertices)

end LinearDistancePreservers.DirectionGraph
