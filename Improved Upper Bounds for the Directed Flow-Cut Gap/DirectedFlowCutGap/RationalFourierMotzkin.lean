import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact feasibility for rational affine inequalities. Eliminating the first
coordinate pairs each lower bound with each upper bound. Back-substitution
chooses a rational endpoint of the interval of allowed values. -/
namespace DirectedFlowCutGap.RationalFourierMotzkin

structure Row (n : ℕ) where
  coeff : Fin n → ℚ
  constant : ℚ

def Row.eval {K : Type*} [Field K] {n : ℕ} (r : Row n) (x : Fin n → K) : K :=
  (r.constant : K)+∑ i, (r.coeff i : K)*x i

def Satisfies {K : Type*} [Field K] [LE K] {n : ℕ} (rows : List (Row n)) (x : Fin n → K) : Prop :=
  ∀ r ∈ rows, 0 ≤ r.eval x

private def Row.tail {n : ℕ} (r : Row (n+1)) : Row n :=
  ⟨Fin.tail r.coeff,r.constant⟩

private def Row.endpoint {n : ℕ} (r : Row (n+1)) : Row n :=
  ⟨fun i => -r.tail.coeff i/r.coeff 0,-r.tail.constant/r.coeff 0⟩

private def Row.sub {n : ℕ} (r s : Row n) : Row n :=
  ⟨fun i => r.coeff i-s.coeff i,r.constant-s.constant⟩

/-- Materialize each projected row once so the next elimination cannot
re-evaluate a tree of older rational coefficients. -/
private def Row.store {n : ℕ} (r : Row n) : Row n :=
  let coefficients := Vector.ofFn r.coeff
  ⟨coefficients.get,r.constant⟩

private theorem store_value {n : ℕ} (r : Row n) : r.store=r := by
  cases r with
  | mk coeff constant =>
    have same : (Vector.ofFn coeff).get=coeff := by
      funext i
      change (Vector.ofFn coeff)[i.val]=coeff i
      exact Vector.getElem_ofFn i.isLt
    simp only [Row.store,same]

private theorem eval_cons {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (r : Row (n+1)) (a : K) (x : Fin n → K) :
    r.eval (Fin.cons a x) = (r.coeff 0 : K)*a+r.tail.eval x := by
  simp only [Row.eval,Row.tail,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.tail]
  ac_rfl

private theorem eval_endpoint {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (r : Row (n+1)) (x : Fin n → K) : r.endpoint.eval x = -(r.tail.eval x)/(r.coeff 0 : K) := by
  simp only [Row.eval,Row.endpoint,Rat.cast_div,Rat.cast_neg]
  simp only [div_eq_mul_inv,neg_add,add_mul,← Finset.sum_neg_distrib,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem eval_sub {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (r s : Row n) (x : Fin n → K) : (r.sub s).eval x = r.eval x-s.eval x := by
  simp only [Row.eval,Row.sub,Rat.cast_sub,sub_mul,Finset.sum_sub_distrib]
  ring

private theorem lower_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
    (r : Row (n+1)) (h : 0 < r.coeff 0) (a : K) (x : Fin n → K) :
    0 ≤ r.eval (Fin.cons a x) ↔ r.endpoint.eval x ≤ a := by
  have pos : 0 < (r.coeff 0 : K) := Rat.cast_pos.mpr h
  rw [eval_cons,eval_endpoint,div_le_iff₀ pos]
  rw [mul_comm a]
  constructor <;> intro h <;> linarith only [h]

private theorem upper_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
    (r : Row (n+1)) (h : r.coeff 0 < 0) (a : K) (x : Fin n → K) :
    0 ≤ r.eval (Fin.cons a x) ↔ a ≤ r.endpoint.eval x := by
  have neg : (r.coeff 0 : K) < 0 := Rat.cast_lt_zero.mpr h
  rw [eval_cons,eval_endpoint,le_div_iff_of_neg neg,mul_comm a]
  constructor <;> intro h <;> linarith only [h]

private def equalRows {n : ℕ} (rows : List (Row (n+1))) := rows.filter fun r => r.coeff 0 = 0
private def lowerRows {n : ℕ} (rows : List (Row (n+1))) := rows.filter fun r => 0 < r.coeff 0
private def upperRows {n : ℕ} (rows : List (Row (n+1))) := rows.filter fun r => r.coeff 0 < 0

private theorem mem_equalRows {n : ℕ} {rows : List (Row (n+1))} {r : Row (n+1)} :
    r ∈ equalRows rows ↔ r ∈ rows ∧ r.coeff 0=0 := by simp [equalRows]

private theorem mem_lowerRows {n : ℕ} {rows : List (Row (n+1))} {r : Row (n+1)} :
    r ∈ lowerRows rows ↔ r ∈ rows ∧ 0<r.coeff 0 := by simp [lowerRows]

private theorem mem_upperRows {n : ℕ} {rows : List (Row (n+1))} {r : Row (n+1)} :
    r ∈ upperRows rows ↔ r ∈ rows ∧ r.coeff 0<0 := by simp [upperRows]

private def reduce {n : ℕ} (rows : List (Row (n+1))) : List (Row n) :=
  (equalRows rows).map (fun r => r.tail.store) ++ (lowerRows rows).flatMap fun l =>
    let low := l.endpoint.store
    (upperRows rows).map fun u => (u.endpoint.sub low).store

private theorem reduce_sound {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
    (rows : List (Row (n+1))) (a : K) (x : Fin n → K) (h : Satisfies rows (Fin.cons a x)) :
    Satisfies (reduce rows) x := by
  intro r mem
  simp only [reduce,store_value,List.mem_append,List.mem_map,List.mem_flatMap] at mem
  rcases mem with ⟨eq,he,rfl⟩ | ⟨l,hl,u,hu,rfl⟩
  · obtain ⟨he,zero⟩ := mem_equalRows.mp he
    simpa only [eval_cons,zero,Rat.cast_zero,zero_mul,zero_add] using h eq he
  · obtain ⟨hl,pl⟩ := mem_lowerRows.mp hl
    obtain ⟨hu,pu⟩ := mem_upperRows.mp hu
    rw [eval_sub,sub_nonneg]
    exact ((lower_iff l pl a x).mp (h l hl)).trans ((upper_iff u pu a x).mp (h u hu))

private def choose (lower upper : List ℚ) : ℚ :=
  lower.max?.getD (upper.min?.getD 0)

private theorem choose_spec (lower upper : List ℚ)
    (ordered : ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u) :
    (∀ l ∈ lower, l ≤ choose lower upper) ∧ (∀ u ∈ upper, choose lower upper ≤ u) := by
  cases hl : lower.max? with
  | some l =>
    have top := List.max?_eq_some_iff.mp hl
    exact ⟨by simpa only [choose,hl,Option.getD_some] using top.2,
      fun u h => by simpa only [choose,hl,Option.getD_some] using ordered l top.1 u h⟩
  | none =>
    have empty := List.max?_eq_none_iff.mp hl
    constructor
    · simp [empty]
    · cases hu : upper.min? with
      | none => simp [List.min?_eq_none_iff.mp hu]
      | some u => simpa only [choose,hl,hu,Option.getD_none,Option.getD_some] using (List.min?_eq_some_iff.mp hu).2

private def extend {n : ℕ} (rows : List (Row (n+1))) (x : Fin n → ℚ) : Fin (n+1) → ℚ :=
  let lower := (lowerRows rows).map fun r => r.endpoint.eval x
  let upper := (upperRows rows).map fun r => r.endpoint.eval x
  Fin.cons (choose lower upper) x

private theorem extend_sound {n : ℕ} (rows : List (Row (n+1))) (x : Fin n → ℚ)
    (h : Satisfies (reduce rows) x) : Satisfies rows (extend rows x) := by
  let lower := (lowerRows rows).map fun r => r.endpoint.eval x
  let upper := (upperRows rows).map fun r => r.endpoint.eval x
  have cross : ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u := by
    intro l hl u hu
    obtain ⟨lo,hlo,rfl⟩ := List.mem_map.mp hl
    obtain ⟨up,hup,rfl⟩ := List.mem_map.mp hu
    have pair := h (up.endpoint.sub lo.endpoint) (by
      simp only [reduce,store_value,List.mem_append,List.mem_flatMap,List.mem_map]
      exact Or.inr ⟨lo,hlo,up,hup,rfl⟩)
    rwa [eval_sub,sub_nonneg] at pair
  have between := choose_spec lower upper cross
  intro r hr
  change 0 ≤ r.eval (Fin.cons (choose lower upper) x)
  rcases lt_trichotomy (r.coeff 0) 0 with neg | zero | pos
  · exact (upper_iff r neg ..).mpr (between.2 _ (List.mem_map.mpr ⟨r,mem_upperRows.mpr ⟨hr,neg⟩,rfl⟩))
  · have tail := h r.tail (by
      simp only [reduce,store_value,List.mem_append,List.mem_map]
      exact Or.inl ⟨r,mem_equalRows.mpr ⟨hr,zero⟩,rfl⟩)
    simpa only [eval_cons,zero,Rat.cast_zero,zero_mul,zero_add] using tail
  · exact (lower_iff r pos ..).mpr (between.1 _ (List.mem_map.mpr ⟨r,mem_lowerRows.mpr ⟨hr,pos⟩,rfl⟩))

private def extendStored {n : ℕ} (rows : List (Row (n+1))) (x : Vector ℚ n) : Vector ℚ (n+1) :=
  let head := extend rows x.get 0
  Vector.ofFn (Fin.cons (α := fun _ => ℚ) head x.get)

private theorem extendStored_value {n : ℕ} (rows : List (Row (n+1))) (x : Vector ℚ n) :
    (extendStored rows x).get=extend rows x.get := by
  funext i
  change (Vector.ofFn (Fin.cons (α := fun _ => ℚ) (extend rows x.get 0) x.get))[i.val]=_
  rw [Vector.getElem_ofFn]
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Store the reconstructed coordinates at each step. A subsequent lookup
uses the stored value without solving the same tail system again. -/
private def solveStored : (n : ℕ) → List (Row n) → Option (Vector ℚ n)
  | 0,rows => if rows.all (fun r => 0 ≤ r.constant) then some #v[] else none
  | n+1,rows => (solveStored n (reduce rows)).map (extendStored rows)

def solve (n : ℕ) (rows : List (Row n)) : Option (Fin n → ℚ) :=
  (solveStored n rows).map Vector.get

private theorem solveStored_sound {n : ℕ} (rows : List (Row n)) (x : Vector ℚ n)
    (h : solveStored n rows=some x) : Satisfies rows x.get := by
  induction n with
  | zero =>
    simp only [solveStored] at h
    split at h
    · rename_i ready
      intro r hr
      have holds := List.all_eq_true.mp ready r hr
      simpa [Row.eval] using holds
    · contradiction
  | succ n ih =>
    obtain ⟨y,hy,rfl⟩ := Option.map_eq_some_iff.mp h
    rw [extendStored_value]
    exact extend_sound rows y.get (ih (reduce rows) y hy)

theorem solve_sound {n : ℕ} (rows : List (Row n)) (x : Fin n → ℚ) (h : solve n rows=some x) :
    Satisfies rows x := by
  obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
  exact solveStored_sound rows v hv

private theorem solveStored_complete {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
    (rows : List (Row n)) (x : Fin n → K) (h : Satisfies rows x) : (solveStored n rows).isSome := by
  induction n with
  | zero =>
    have all : rows.all (fun r => 0 ≤ r.constant)=true := List.all_eq_true.mpr fun r hr => by
      have holds := h r hr
      simp only [Row.eval,Finset.univ_eq_empty,Finset.sum_empty,add_zero,Rat.cast_nonneg] at holds
      simpa only [decide_eq_true_eq] using holds
    simp only [solveStored,all,ite_true,Option.isSome_some]
  | succ n ih =>
    have tail : Satisfies (reduce rows) (Fin.tail x) :=
      reduce_sound rows (x 0) (Fin.tail x) (by simpa only [Fin.cons_self_tail] using h)
    simpa only [solveStored,Option.isSome_map] using ih (reduce rows) (Fin.tail x) tail

theorem solve_complete {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
    (rows : List (Row n)) (x : Fin n → K) (h : Satisfies rows x) : (solve n rows).isSome := by
  simpa only [solve,Option.isSome_map] using solveStored_complete rows x h

theorem rational_to_real {n : ℕ} (rows : List (Row n)) (x : Fin n → ℚ) (h : Satisfies rows x) :
    Satisfies rows (fun i => (x i : ℝ)) := by
  intro r hr
  have holds : 0 ≤ r.eval x := h r hr
  simpa only [Row.eval,Rat.cast_id,Rat.cast_add,Rat.cast_sum,Rat.cast_mul] using
    (Rat.cast_nonneg.mpr holds : (0 : ℝ) ≤ ((r.eval x : ℚ) : ℝ))

/-! A nonnegative objective is the last retained coordinate. Project all
other coordinates, select its smallest permitted value, and reconstruct
the eliminated variables with the same exact rational extension. -/

private def lastProjection : (n : ℕ) → List (Row (n+1)) → List (Row 1)
  | 0,rows => rows
  | n+1,rows => lastProjection n (reduce rows)

private def point {K : Type*} (q : K) : Fin 1 → K := fun _ => q

private theorem lastProjection_complete {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) (rows : List (Row (n+1))) (x : Fin (n+1) → K) (valid : Satisfies rows x) :
    Satisfies (lastProjection n rows) (point (x (Fin.last n))) := by
  induction n with
  | zero =>
    have same : point (x (Fin.last 0))=x := by
      funext i
      have unique : i=Fin.last 0 := Fin.ext (by have inside := i.isLt; change i.val<1 at inside; omega)
      exact congrArg x unique.symm
    simpa only [lastProjection,same] using valid
  | succ n ih =>
    have smaller := reduce_sound rows (x 0) (Fin.tail x) (by simpa only [Fin.cons_self_tail] using valid)
    change Satisfies (lastProjection n (reduce rows)) (point (x (Fin.last n).succ))
    exact ih (reduce rows) (Fin.tail x) smaller

private def restoreLast : (n : ℕ) → List (Row (n+1)) → Vector ℚ 1 → Vector ℚ (n+1)
  | 0,_,remaining => remaining
  | n+1,rows,remaining => extendStored rows (restoreLast n (reduce rows) remaining)

private theorem restoreLast_sound (n : ℕ) (rows : List (Row (n+1))) (q : Vector ℚ 1)
    (valid : Satisfies (lastProjection n rows) q.get) :
    Satisfies rows (restoreLast n rows q).get ∧ (restoreLast n rows q).get (Fin.last n)=q.get 0 := by
  induction n with
  | zero => exact ⟨valid,rfl⟩
  | succ n ih =>
    let next := restoreLast n (reduce rows) q
    obtain ⟨good,unchanged⟩ := ih (reduce rows) valid
    change Satisfies rows (extendStored rows next).get ∧
      (extendStored rows next).get (Fin.last n).succ=q.get 0
    rw [extendStored_value]
    exact ⟨extend_sound rows next.get good,unchanged⟩

private def positiveEndpoints (rows : List (Row 1)) : List ℚ :=
  (lowerRows rows).map fun r => -r.constant/r.coeff 0

private def leastPoint (rows : List (Row 1)) : ℚ :=
  max 0 ((positiveEndpoints rows).max?.getD 0)

private theorem eval_point {K : Type*} [Field K] (r : Row 1) (q : K) :
    r.eval (point q)=(r.constant : K)+(r.coeff 0 : K)*q := by
  simp only [Row.eval,Fin.sum_univ_one,point]

private theorem all_endpoints_le {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (rows : List (Row 1)) (q : K) (valid : Satisfies rows (point q)) :
    ∀ b∈positiveEndpoints rows, (b : K)≤q := by
  intro b member
  obtain ⟨r,inside,rfl⟩ := List.mem_map.mp member
  obtain ⟨within,pos⟩ := mem_lowerRows.mp inside
  have equation := valid r within
  rw [eval_point] at equation
  simp only [Rat.cast_div,Rat.cast_neg]
  apply (div_le_iff₀ (Rat.cast_pos.mpr pos)).mpr
  linarith only [equation]

private theorem least_le {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (rows : List (Row 1)) (q : K) (nonneg : 0≤q) (valid : Satisfies rows (point q)) :
    (leastPoint rows : K)≤q := by
  have endpoints := all_endpoints_le rows q valid
  unfold leastPoint
  rw [Rat.cast_max,Rat.cast_zero]
  apply max_le nonneg
  cases hm : (positiveEndpoints rows).max? with
  | none => simpa only [hm,Option.getD_none,Rat.cast_zero] using nonneg
  | some p => simpa only [hm,Option.getD_some] using endpoints p (List.max?_eq_some_iff.mp hm).1

private theorem endpoint_reached (rows : List (Row 1)) (b : ℚ) (inside : b∈positiveEndpoints rows) :
    b≤leastPoint rows := by
  unfold leastPoint
  cases h : (positiveEndpoints rows).max? with
  | none =>
    rw [List.max?_eq_none_iff.mp h] at inside
    exact (List.not_mem_nil inside).elim
  | some top =>
    exact ((List.max?_eq_some_iff.mp h).2 b inside).trans (le_max_right _ _)

private theorem least_valid {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (rows : List (Row 1)) (q : K) (nonnegative : 0≤q) (valid : Satisfies rows (point q)) :
    Satisfies rows (point (leastPoint rows)) := by
  intro r within
  simp only [eval_point,Rat.cast_id]
  by_cases pos : 0<r.coeff 0
  · have endpoint := endpoint_reached rows (-r.constant/r.coeff 0)
      (List.mem_map.mpr ⟨r,mem_lowerRows.mpr ⟨within,pos⟩,rfl⟩)
    have bound := (div_le_iff₀ pos).mp endpoint
    rw [mul_comm] at bound
    linarith only [bound]
  · have qValid := valid r within
    rw [eval_point] at qValid
    have nonpos : (r.coeff 0 : K)≤0 := Rat.cast_nonpos.mpr (le_of_not_gt pos)
    have next := mul_le_mul_of_nonpos_left (least_le rows q nonnegative valid) nonpos
    have cast : (0 : K)≤(r.constant : K)+(r.coeff 0 : K)*(leastPoint rows : K) := by linarith only [qValid,next]
    have casted : (0 : K)≤((r.constant+r.coeff 0*leastPoint rows : ℚ) : K) := by
      rw [Rat.cast_add,Rat.cast_mul]
      exact cast
    exact Rat.cast_nonneg.mp casted

def minimizeLast (n : ℕ) (rows : List (Row (n+1))) : Option (ℚ × (Fin (n+1) → ℚ)) :=
  let projected := lastProjection n rows
  let q := leastPoint projected
  if projected.all (fun r => 0≤r.eval (point q)) then
    let x := restoreLast n rows (Vector.ofFn (point q))
    some (q,x.get)
  else none

theorem minimizeLast_sound (n : ℕ) (rows : List (Row (n+1))) {q : ℚ} {y : Fin (n+1) → ℚ}
    (returned : minimizeLast n rows=some (q,y)) :
    0≤q ∧ y (Fin.last n)=q ∧ Satisfies rows y := by
  unfold minimizeLast at returned
  dsimp only at returned
  split at returned
  · rename_i checked
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj returned)
    let q := leastPoint (lastProjection n rows)
    let v := Vector.ofFn (point q)
    have actual : v.get=point q := by funext i; exact Vector.getElem_ofFn i.isLt
    have valid : Satisfies (lastProjection n rows) v.get := by
      rw [actual]
      intro r within
      exact decide_eq_true_eq.mp (List.all_eq_true.mp checked r within)
    obtain ⟨yes,last⟩ := restoreLast_sound n rows v valid
    rw [actual] at last
    exact ⟨le_max_left _ _,last,yes⟩
  · cases returned

theorem minimizeLast_optimal {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) (rows : List (Row (n+1))) {q : ℚ} {y : Fin (n+1) → ℚ}
    (returned : minimizeLast n rows=some (q,y)) (x : Fin (n+1) → K)
    (nonnegative : 0≤x (Fin.last n)) (valid : Satisfies rows x) : (q : K)≤x (Fin.last n) := by
  unfold minimizeLast at returned
  dsimp only at returned
  split at returned
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj returned)
    exact least_le _ _ nonnegative (lastProjection_complete n rows x valid)
  · cases returned

theorem minimizeLast_complete {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) (rows : List (Row (n+1))) (x : Fin (n+1) → K)
    (nonnegative : 0≤x (Fin.last n)) (valid : Satisfies rows x) :
    (minimizeLast n rows).isSome := by
  have possible := least_valid _ _ nonnegative (lastProjection_complete n rows x valid)
  have checked : (lastProjection n rows).all (fun r => 0≤r.eval (point (leastPoint (lastProjection n rows)))) := by
    apply List.all_eq_true.mpr
    intro r within
    exact decide_eq_true_eq.mpr (possible r within)
  simp only [minimizeLast,checked,ite_true,Option.isSome_some]

end DirectedFlowCutGap.RationalFourierMotzkin
