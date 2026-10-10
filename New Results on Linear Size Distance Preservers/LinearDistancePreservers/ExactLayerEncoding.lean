import LinearDistancePreservers.DirectionPerfect

namespace LinearDistancePreservers.DirectionGraph
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {D J : Type*} {n k r : ℕ}

/-- Theorem 6's shortest-path argument, with the no-wrap inequality
explicit and all undirected competitors included. -/
theorem canonical_unique_fixed_length (v : J → D → ℕ)
    (hv : ∀ a d, v a d < r) (hn : (k+1)*r ≤ n) (hrigid : ∀ (a : J) (f : Fin k → J),
      (∀ d, ∑ i, (v (f i) d : ℤ) = (k : ℤ)*(v a d : ℤ)) →
        ∀ i, v (f i) = v a)
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
  have hconst := hrigid a f
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

namespace LinearDistancePreservers.DirectionEncoding
open Finset

def encode (B : ℕ) : {d : ℕ} → (Fin d → ℕ) → ℕ
  | 0, _ => 0
  | _+1, v => v 0 + B * encode B (fun i => v i.succ)

theorem encode_injective {B : ℕ} (hB : 0<B) {d : ℕ}
    {v w : Fin d → ℕ} (hv : ∀ i, v i<B) (hw : ∀ i, w i<B)
    (he : encode B v=encode B w) : v=w := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    have h0 : v 0=w 0 := by
      have h := congrArg (fun x => x%B) he
      simpa [encode,Nat.mod_eq_of_lt (hv 0),Nat.mod_eq_of_lt (hw 0)] using h
    have ht : encode B (fun i => v i.succ)=encode B (fun i => w i.succ) := by
      simp only [encode,h0,Nat.add_left_cancel_iff] at he
      exact Nat.eq_of_mul_eq_mul_left hB he
    have hi := ih (fun i => hv i.succ) (fun i => hw i.succ) ht
    funext i
    exact Fin.cases h0 (fun j => congrFun hi j) i

theorem encode_sum {B d : ℕ} {J : Type*} [Fintype J] (v : J → Fin d → ℕ) :
    encode B (fun i => ∑ j, v j i)=∑ j, encode B (v j) := by
  induction d with
  | zero => simp [encode]
  | succ d ih =>
    simp only [encode,Finset.sum_add_distrib]
    rw [ih,Finset.mul_sum]

theorem encode_mul {B d : ℕ} (k : ℕ) (v : Fin d → ℕ) :
    encode B (fun i => k*v i)=k*encode B v := by
  induction d with
  | zero => simp [encode]
  | succ d ih => simp only [encode,ih]; ring

/-- The leading digit bound saves one factor of the base. -/
theorem encode_lt {B r : ℕ} (hrB : r≤B) {d : ℕ}
    (v : Fin (d+1) → ℕ) (hv : ∀ i, v i<r) : encode B v<r*B^d := by
  induction d with
  | zero => simpa [encode] using hv 0
  | succ d ih =>
    have ht := ih (fun i => v i.succ) (fun i => hv i.succ)
    have hmul := Nat.mul_le_mul_left B (Nat.succ_le_of_lt ht)
    have h0 := hv 0
    change v 0+B*encode B (fun i => v i.succ)<r*B^(d+1)
    rw [pow_succ]
    simp only [Nat.succ_eq_add_one] at hmul
    nlinarith only [hmul,h0,hrB]

/-- A carry-free base encoding retains the one average length used by the graph.
Full convex rigidity of the scalar codes is neither required nor asserted. -/
theorem fixed_length_rigid {J : Type*} {d k r B : ℕ}
    (hB : 0<B) (hkr : k*r<B) (v : J → Fin d → ℕ)
    (hv : ∀ a i, v a i<r) (hrigid : DirectionGraph.AverageRigid v)
    (a : J) (f : Fin k → J)
    (he : ∑ j, (encode B (v (f j)) : ℤ)=(k : ℤ)*(encode B (v a) : ℤ)) :
    ∀ j, encode B (v (f j))=encode B (v a) := by
  have heN : ∑ j, encode B (v (f j))=k*encode B (v a) := by exact_mod_cast he
  have hsum (i : Fin d) : (∑ j, v (f j) i)<B := by
    have hle : (∑ j, v (f j) i)≤k*r := by
      calc
        _ ≤ ∑ _j : Fin k, r := Finset.sum_le_sum (fun j _ => (hv (f j) i).le)
        _ = k*r := by simp
    exact hle.trans_lt hkr
  have ha (i : Fin d) : k*v a i<B := (Nat.mul_le_mul_left k (hv a i).le).trans_lt hkr
  have hcode : encode B (fun i => ∑ j, v (f j) i)=encode B (fun i => k*v a i) := by
    rw [encode_sum,encode_mul]; exact heN
  have hcoord := encode_injective hB hsum ha hcode
  have hh := hrigid k a f (fun i => by exact_mod_cast congrFun hcoord i)
  intro j
  rw [hh j]

end LinearDistancePreservers.DirectionEncoding
