import LinearDistancePreservers.ModularGraph
import LinearDistancePreservers.WalkSequence
import LinearDistancePreservers.PreserverForcing

/-! The repaired Theorem 5 construction as an actual finite undirected
weighted graph. Every native walk is encoded in the previously verified
modular walk datatype, so the optimality theorem covers all graph walks.
Weights are symmetric and strictly positive. -/
namespace LinearDistancePreservers.ModularGraph
set_option backward.isDefEq.respectTransparency.types false
open SimpleGraph Finset
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
variable {n k x : ℕ} [NeZero n]

def Step (u v : Vertex n k) (b : Bool) (a : Fin x) : Prop :=
  (v.1.val : ℤ) - (u.1.val : ℤ) = (if b then 1 else -1) ∧
  v.2 - u.2 = (if b then (a.val : ZMod n) else -(a.val : ZMod n))

def graph (n k x : ℕ) : SimpleGraph (Vertex n k) where
  Adj u v := ∃ (b : Bool) (a : Fin x), Step u v b a
  symm := by
    constructor
    rintro u v ⟨b, a, hl, hc⟩
    refine ⟨!b, a, ?_⟩
    cases b <;> simp only [Step, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true] at * <;> constructor
    all_goals first | omega | linear_combination -hc
  loopless := by
    constructor
    rintro u ⟨b, a, hl, hc⟩
    cases b <;> simp [Step] at hl

noncomputable def columnSlope (u v : Vertex n k) : ℕ :=
  if u.1.val < v.1.val then (v.2-u.2).val else (u.2-v.2).val

theorem columnSlope_symm (u v : Vertex n k) :
    (graph n k x).Adj u v → columnSlope u v = columnSlope v u := by
  rintro ⟨b, a, hl, hc⟩
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hl hc
  · have hv : v.1.val < u.1.val := by omega
    simp [columnSlope, hv, not_lt.mpr hv.le]
  · have hu : u.1.val < v.1.val := by omega
    simp [columnSlope, hu, not_lt.mpr hu.le]

theorem columnSlope_step (hx : x ≤ n) {u v : Vertex n k} {b : Bool} {a : Fin x}
    (h : Step u v b a) : columnSlope u v = a.val := by
  obtain ⟨hl, hc⟩ := h
  have ha : a.val < n := lt_of_lt_of_le a.isLt hx
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hl hc
  · have hv : ¬u.1.val < v.1.val := by omega
    have he : u.2-v.2 = (a.val : ZMod n) := by linear_combination -hc
    simp [columnSlope, hv, he, ZMod.val_natCast_of_lt ha]
  · have hu : u.1.val < v.1.val := by omega
    simp [columnSlope, hu, hc, ZMod.val_natCast_of_lt ha]

noncomputable def weight (n k x : ℕ) [NeZero n] (u v : Vertex n k) : ℝ≥0 :=
  (k*x^2+1+(columnSlope u v)^2 : ℕ)

theorem weight_pos (u v : Vertex n k) : 0 < weight n k x u v := by
  simp only [weight, Nat.cast_pos]
  omega

theorem weight_symm {u v : Vertex n k} (h : (graph n k x).Adj u v) :
    weight n k x u v = weight n k x v u := by
  simp only [weight, columnSlope_symm u v h]

/-- Decode each native graph step, with no restrictions on backtracking. -/
noncomputable def encode {s t : Vertex n k} (p : (graph n k x).Walk s t) :
    ModularGraph.Walk n k x p.length where
  vertex i := p.getVert i.val
  forward i := (p.adj_getVert_succ i.isLt).choose
  slope i := (p.adj_getVert_succ i.isLt).choose_spec.choose
  layer_step i := (p.adj_getVert_succ i.isLt).choose_spec.choose_spec.1
  column_step i := (p.adj_getVert_succ i.isLt).choose_spec.choose_spec.2

theorem encode_slope (hx : x ≤ n) {s t : Vertex n k}
    (p : (graph n k x).Walk s t) (i : Fin p.length) :
    columnSlope (p.getVert i.val) (p.getVert (i.val+1)) = ((encode p).slope i).val :=
  columnSlope_step hx (p.adj_getVert_succ i.isLt).choose_spec.choose_spec

/-- The integer cost in the repaired construction is the actual weighted
cost of the native walk, after the canonical embedding into the reals. -/
theorem native_cost (hx : x ≤ n) {s t : Vertex n k} (p : (graph n k x).Walk s t) :
    (p.darts.map fun d => (weight n k x d.fst d.snd : ℝ)).sum =
      (QuadraticRepair.cost k x (fun i => ((encode p).slope i).val) : ℝ) := by
  rw [darts_sum_eq (fun u v => (weight n k x u v : ℝ)) p]
  simp only [QuadraticRepair.cost, Int.cast_sum]
  apply sum_congr rfl
  intro i _
  simp [weight, encode_slope hx, QuadraticRepair.baseline]

theorem canonical_adj (s : ZMod n) (a : Fin x) (i : Fin k) :
    (graph n k x).Adj (point s a i.castSucc) (point s a i.succ) :=
  ⟨true, a, (canonical s a).layer_step i, (canonical s a).column_step i⟩

def canonicalWalk (s : ZMod n) (a : Fin x) :
    (graph n k x).Walk (point s a 0) (point s a (Fin.last k)) :=
  walkOfSequence (point s a) (canonical_adj s a)

@[simp] theorem canonicalWalk_support (s : ZMod n) (a : Fin x) :
    (canonicalWalk (k := k) s a).support = List.ofFn (point s a) :=
  support_walkOfSequence _ _

@[simp] theorem canonicalWalk_length (s : ZMod n) (a : Fin x) :
    (canonicalWalk (k := k) s a).length = k := length_walkOfSequence _ _

theorem canonicalWalk_getVert (s : ZMod n) (a : Fin x) (i : Fin (k+1)) :
    (canonicalWalk (k := k) s a).getVert i.val = point s a i := by
  simpa only [canonicalWalk_support, List.getElem_ofFn] using
    (canonicalWalk (k := k) s a).getVert_eq_support_getElem
      (show i.val ≤ (canonicalWalk s a).length by simp; omega)

theorem canonical_native_cost (hx : x ≤ n) (s : ZMod n) (a : Fin x) :
    ((canonicalWalk (k := k) s a).darts.map fun d => (weight n k x d.fst d.snd : ℝ)).sum =
      (k : ℝ) * ((QuadraticRepair.baseline k x : ℤ) + (a.val : ℝ)^2) := by
  rw [native_cost hx]
  have he : ∀ i : Fin (canonicalWalk (k := k) s a).length,
      ((encode (canonicalWalk s a)).slope i).val = a.val := by
    intro i
    let j : Fin k := ⟨i.val, by simpa using i.isLt⟩
    rw [← encode_slope hx]
    change columnSlope ((canonicalWalk s a).getVert j.val)
      ((canonicalWalk s a).getVert (j.val+1)) = a.val
    rw [show (canonicalWalk s a).getVert j.val = point s a j.castSucc from
      canonicalWalk_getVert s a j.castSucc,
      show (canonicalWalk s a).getVert (j.val+1) = point s a j.succ from
      canonicalWalk_getVert s a j.succ]
    exact columnSlope_step hx ⟨(canonical s a).layer_step j, (canonical s a).column_step j⟩
  simp [QuadraticRepair.cost, he]

theorem native_optimal {s : ZMod n} {a : Fin x}
    (hn : (k+1)*x ≤ n)
    (p : (graph n k x).Walk (point s a 0) (point s a (Fin.last k))) :
    (k : ℝ) * ((QuadraticRepair.baseline k x : ℤ) + (a.val : ℝ)^2) ≤
      (p.darts.map fun d => (weight n k x d.fst d.snd : ℝ)).sum ∧
    ((p.darts.map fun d => (weight n k x d.fst d.snd : ℝ)).sum =
      (k : ℝ) * ((QuadraticRepair.baseline k x : ℤ) + (a.val : ℝ)^2) →
      p.support = List.ofFn (point s a)) := by
  have hx : x ≤ n := (Nat.le_mul_of_pos_left x (by omega)).trans hn
  have hs : (encode p).vertex 0 = point s a 0 := by simp [encode]
  have ht : (encode p).vertex (Fin.last p.length) = point s a (Fin.last k) := by simp [encode]
  obtain ⟨hopt, hu⟩ := (encode p).optimal hn hs ht
  rw [native_cost hx]
  refine ⟨by exact_mod_cast hopt, ?_⟩
  intro he
  have hei : QuadraticRepair.cost k x (fun i => ((encode p).slope i).val) =
      (k : ℤ) * (QuadraticRepair.baseline k x + (a.val : ℤ)^2) := by exact_mod_cast he
  obtain ⟨hm, hv⟩ := (encode p).unique_vertex_sequence hn hs ht hei
  rw [support_eq_ofFn]
  have hseq : HEq (fun i : Fin (p.length+1) => p.getVert i.val) (point (k := k) s a) := hv
  have aux {m l : ℕ} {f : Fin (m+1) → Vertex n k} {g : Fin (l+1) → Vertex n k}
      (hml : m = l) (hfg : HEq f g) : List.ofFn f = List.ofFn g := by
    subst l
    exact congrArg List.ofFn (eq_of_heq hfg)
  exact aux hm hseq

end LinearDistancePreservers.ModularGraph
