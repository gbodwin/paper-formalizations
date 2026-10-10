import DirectedFlowCutGap.EncodedTablePreparation
import DirectedFlowCutGap.EncodedRoundingState

/-!
# The concrete flag-union body reached by a cut round

This fixed program reads two retained flag rows, executes Boolean OR, advances
an actual binary predecessor loop, and pays both suffix-copy materialization
and construction of the retained result. No callback or encoder is supplied.
`rowValue` and `merged` occur only in representation statements. Runtime input
is the already retained finite data plus its binary count.

The output refines the exact union called by `roundData`; no optimizer or random
request is changed. Input producers, the remaining round operations and the
common representation overhead remain separate whole-entry obligations.
-/
namespace DirectedFlowCutGap.EncodedFlagUnion
open BinaryArithmetic EncodedSequenceAccess EncodedTablePreparation

def rowValue (xs : List Bool) : Value := EncodedSequenceAccess.sequence (xs.map Value.flag)

/-- Literal tag elimination and the one Boolean operation of the callback. -/
def orPayload : Option Value → Option Value → Option Bool
  | some (.flag a), some (.flag b) => some (a || b)
  | _, _ => none

def orAt (i : Bits) (x y : Value) : Option Bool × ℕ :=
  let a := read i x
  let b := read i y
  (orPayload a.1 b.1,a.2+b.2+12)

inductive OrAtExec (i : Bits) (x y : Value) : Option Bool → ℕ → Prop
  | run (a b : Option Value) (q r : ℕ) :
      ReadExec i x a q → ReadExec i y b r → OrAtExec i x y (orPayload a b) (q+r+12)

theorem orAt_exec (i : Bits) (x y : Value) : OrAtExec i x y (orAt i x y).1 (orAt i x y).2 :=
  .run _ _ _ _ (read_exec i x) (read_exec i y)

theorem OrAtExec.result {i : Bits} {x y : Value} {out : Option Bool} {q : ℕ}
    (h : OrAtExec i x y out q) : out = (orAt i x y).1 ∧ q = (orAt i x y).2 := by
  cases h with
  | run a b q r ha hb =>
      have hx := ha.result
      have hy := hb.result
      constructor <;> simp only [orAt,hx.1,hx.2,hy.1,hy.2]

theorem orAt_get (i : Bits) (xs ys : List Bool)
    (hx : value i < xs.length) (hy : value i < ys.length) :
    (orAt i (rowValue xs) (rowValue ys)).1 = some (xs[value i] || ys[value i]) := by
  have h₁ : (read i (rowValue xs)).1 = some (.flag xs[value i]) := by
    rw [rowValue,read_get,List.getElem?_map,List.getElem?_eq_getElem hx]
    rfl
  have h₂ : (read i (rowValue ys)).1 = some (.flag ys[value i]) := by
    rw [rowValue,read_get,List.getElem?_map,List.getElem?_eq_getElem hy]
    rfl
  simp only [orAt,h₁,h₂,orPayload]

def orAtBound (n m B : ℕ) : ℕ := 20*(n+1)*(B+1)+20*(m+1)*(B+1)+28

theorem orAt_bound (i : Bits) (xs ys : List Bool) (B : ℕ) (hi : i.length ≤ B) :
    (orAt i (rowValue xs) (rowValue ys)).2 ≤ orAtBound xs.length ys.length B := by
  have flagSize (zs : List Bool) : ∀ x∈zs.map Value.flag, x.size ≤ 2 := by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    rfl
  have hx := read_bound i (xs.map Value.flag) B 2 hi (flagSize xs)
  have hy := read_bound i (ys.map Value.flag) B 2 hi (flagSize ys)
  simp only [List.length_map] at hx hy
  dsimp only [orAt,orAtBound,rowValue]
  omega

/-- Only the finite OR body can be reached at an index. -/
def loop (x y : Value) (fuel : Bits) (acc : List Value) : Option (List Value) × ℕ :=
  let z := isZero fuel
  if hz : z.1 = true then (some acc,z.2+4) else
    let p := predCore fuel
    let head := orAt p.1 x y
    match head.1 with
    | none => (none,z.2+p.2+head.2+8)
    | some b =>
        let r := loop x y p.1 (.flag b::acc)
        (r.1,z.2+p.2+head.2+r.2+12)
termination_by value fuel
decreasing_by
  have hv : 0 < value fuel := Nat.pos_of_ne_zero
    (fun h => hz ((isZero_spec fuel).1.mpr h))
  have hp := (predCore_spec fuel).1 hv
  omega

inductive LoopExec (x y : Value) : Bits → List Value → Option (List Value) → ℕ → Prop
  | zero (fuel : Bits) (acc : List Value) :
      (isZero fuel).1 = true → LoopExec x y fuel acc (some acc) ((isZero fuel).2+4)
  | missing (fuel : Bits) (acc : List Value) (q : ℕ) :
      (isZero fuel).1 = false → OrAtExec (predCore fuel).1 x y none q →
      LoopExec x y fuel acc none ((isZero fuel).2+(predCore fuel).2+q+8)
  | step (fuel : Bits) (acc : List Value) (b : Bool) (out : Option (List Value)) (q r : ℕ) :
      (isZero fuel).1 = false → OrAtExec (predCore fuel).1 x y (some b) q →
      LoopExec x y (predCore fuel).1 (.flag b::acc) out r →
      LoopExec x y fuel acc out ((isZero fuel).2+(predCore fuel).2+q+r+12)

theorem loop_exec (x y : Value) (fuel : Bits) (acc : List Value) :
    LoopExec x y fuel acc (loop x y fuel acc).1 (loop x y fuel acc).2 := by
  have aux : ∀ k, ∀ f : Bits, value f = k → ∀ a : List Value,
      LoopExec x y f a (loop x y f a).1 (loop x y f a).2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro f hf a
      rw [loop]
      cases hz : (isZero f).1 with
      | true => simpa only [hz,dite_true] using LoopExec.zero (x := x) (y := y) f a hz
      | false =>
          have hv : 0 < value f := Nat.pos_of_ne_zero (fun h => by
            have ht := (isZero_spec f).1.mpr h
            rw [hz] at ht
            contradiction)
          have hp := (predCore_spec f).1 hv
          have hr := orAt_exec (predCore f).1 x y
          cases hread : (orAt (predCore f).1 x y).1 with
          | none =>
              rw [hread] at hr
              simpa only [hz,Bool.false_eq_true,dite_false,hread] using
                LoopExec.missing f a _ hz hr
          | some b =>
              rw [hread] at hr
              have hrec := ih (value (predCore f).1) (by omega) (predCore f).1 rfl (.flag b::a)
              simpa only [hz,Bool.false_eq_true,dite_false,hread] using
                LoopExec.step f a b _ _ _ hz hr hrec
  exact aux (value fuel) fuel rfl acc

/-- Every reached accumulator consists of produced flags; no large payload is
silently introduced during the loop. -/
inductive Reach (x y : Value) (initial : Bits) : Bits → List Value → Prop
  | start : Reach x y initial initial []
  | step (fuel : Bits) (acc : List Value) (b : Bool) (q : ℕ) :
      Reach x y initial fuel acc → (isZero fuel).1 = false →
      OrAtExec (predCore fuel).1 x y (some b) q →
      Reach x y initial (predCore fuel).1 (.flag b::acc)

theorem Reach.invariants {x y : Value} {initial fuel : Bits} {acc : List Value}
    (h : Reach x y initial fuel acc) :
    fuel.length ≤ initial.length ∧ value fuel+acc.length = value initial ∧
    ∀ v∈acc, v.size ≤ 2 := by
  induction h with
  | start => exact ⟨le_rfl,by simp,by simp⟩
  | step f a b q hp hz hr ih =>
      have hf : 0 < value f := Nat.pos_of_ne_zero (fun h => by
        have ht := (isZero_spec f).1.mpr h
        rw [hz] at ht
        contradiction)
      have hv := (predCore_spec f).1 hf
      refine ⟨(predCore_spec f).2.1.trans ih.1,?_,?_⟩
      · simp only [List.length_cons]
        omega
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · rfl
        · exact ih.2.2 v hv

theorem Reach.size_bound {x y : Value} {initial fuel : Bits} {acc : List Value}
    (h : Reach x y initial fuel acc) :
    (EncodedSequenceAccess.sequence acc).size ≤ value initial*3+1 := by
  have hi := h.invariants
  exact (sequence_size_bound hi.2.2).trans (by gcongr; omega)

/-- Proof-side observation of the source pointwise union. -/
def merged (xs ys : List Bool) : List Value := List.zipWith (fun a b => Value.flag (a || b)) xs ys

theorem merged_size (xs ys : List Bool) : ∀ v∈merged xs ys, v.size ≤ 2 := by
  intro v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hv
  simpa only [merged,List.getElem_zipWith,Value.size] using (show (2 : ℕ) ≤ 2 from le_rfl)

theorem loop_value (xs ys : List Bool) (fuel : Bits) (acc : List Value)
    (hcount : value fuel ≤ (merged xs ys).length) :
    (loop (rowValue xs) (rowValue ys) fuel acc).1 =
      some ((merged xs ys).take (value fuel)++acc) := by
  have aux : ∀ k, ∀ f : Bits, value f = k → ∀ a : List Value,
      value f ≤ (merged xs ys).length →
      (loop (rowValue xs) (rowValue ys) f a).1 = some ((merged xs ys).take (value f)++a) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro f hf a hc
      rw [loop]
      split_ifs with hz
      · have hv := (isZero_spec f).1.mp hz
        simp only [hv,List.take_zero,List.nil_append]
      · have hv : 0 < value f := Nat.pos_of_ne_zero (fun h => hz ((isZero_spec f).1.mpr h))
        have hp := (predCore_spec f).1 hv
        have hlt : value (predCore f).1 < (merged xs ys).length := by omega
        have hx : value (predCore f).1 < xs.length := List.lt_length_left_of_zipWith hlt
        have hy : value (predCore f).1 < ys.length := List.lt_length_right_of_zipWith hlt
        have hr := orAt_get (predCore f).1 xs ys hx hy
        have hhead : (merged xs ys)[value (predCore f).1] =
            Value.flag (xs[value (predCore f).1] || ys[value (predCore f).1]) :=
          List.getElem_zipWith
        simp only [hr]
        rw [ih (value (predCore f).1) (by omega) (predCore f).1 rfl
          (.flag (xs[value (predCore f).1] || ys[value (predCore f).1])::a) (by omega)]
        rw [← hp,List.take_succ_eq_append_getElem hlt,List.append_assoc,hhead]
        rfl
  exact aux (value fuel) fuel rfl acc hcount

def loopBound (count n m B : ℕ) : ℕ := (count+1)*(orAtBound n m B+24*(B+1)+12)

theorem loop_bound (xs ys : List Bool) (fuel : Bits) (acc : List Value) (B : ℕ)
    (hf : fuel.length ≤ B) :
    (loop (rowValue xs) (rowValue ys) fuel acc).2 ≤ loopBound (value fuel) xs.length ys.length B := by
  have aux : ∀ k, ∀ f : Bits, value f = k → ∀ a : List Value,
      f.length ≤ B → (loop (rowValue xs) (rowValue ys) f a).2 ≤
        loopBound (value f) xs.length ys.length B := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro f hk a hf
      have hz := (isZero_spec f).2
      rw [loop]
      split_ifs with hzero
      · have hv := (isZero_spec f).1.mp hzero
        unfold loopBound orAtBound
        rw [hv]
        nlinarith
      · have hv : 0 < value f := Nat.pos_of_ne_zero (fun h => hzero ((isZero_spec f).1.mpr h))
        have hp := predCore_spec f
        have hvp := hp.1 hv
        have hpf : (predCore f).1.length ≤ B := hp.2.1.trans hf
        have hread := orAt_bound (predCore f).1 xs ys B hpf
        let C := orAtBound xs.length ys.length B+24*(B+1)+12
        have hstep : (isZero f).2+(predCore f).2+
            (orAt (predCore f).1 (rowValue xs) (rowValue ys)).2+12 ≤ C := by
          dsimp only [C]
          nlinarith [hp.2.2]
        cases hr : (orAt (predCore f).1 (rowValue xs) (rowValue ys)).1 with
        | none =>
            simp only [hr]
            change _ ≤ (value f+1)*C
            exact (show _ ≤ C by omega).trans (Nat.le_mul_of_pos_left C (by omega))
        | some b =>
            have hrec := ih (value (predCore f).1) (by omega) (predCore f).1 rfl (.flag b::a) hpf
            have hrec' : (loop (rowValue xs) (rowValue ys) (predCore f).1 (.flag b::a)).2 ≤ value f*C := by
              simpa only [loopBound,hvp] using hrec
            simp only [hr]
            change _ ≤ (value f+1)*C
            calc
              _ ≤ C+value f*C := by omega
              _ = (value f+1)*C := by ring
  exact aux (value fuel) fuel rfl acc hf

/-- The actual loop result is copied/materialized and retained once. -/
def union (x y : Value) (count : Bits) : Option Value × ℕ :=
  let r := loop x y count []
  match r.1 with
  | none => (none,r.2+4)
  | some cells =>
      let c := collectValues cells
      let p := prepareRow c.1
      (some p.1,r.2+c.2+p.2+12)

inductive UnionExec (x y : Value) (count : Bits) : Option Value → ℕ → Prop
  | missing (q : ℕ) : LoopExec x y count [] none q → UnionExec x y count none (q+4)
  | found (cells copied : List Value) (out : Value) (q r s : ℕ) :
      LoopExec x y count [] (some cells) q → CollectValuesExec cells copied r →
      RowExec copied out s → UnionExec x y count (some out) (q+r+s+12)

theorem union_exec (x y : Value) (count : Bits) : UnionExec x y count (union x y count).1 (union x y count).2 := by
  have h := loop_exec x y count []
  cases hr : (loop x y count []).1 with
  | none =>
      rw [hr] at h
      simpa only [union,hr] using UnionExec.missing (x := x) (y := y) (count := count) _ h
  | some cells =>
      rw [hr] at h
      simpa only [union,hr] using UnionExec.found (x := x) (y := y) (count := count)
        cells _ _ _ _ _ h (collectValues_exec cells) (prepareRow_exec (collectValues cells).1)

theorem union_value (xs ys : List Bool) (count : Bits)
    (hc : value count = (merged xs ys).length) :
    (union (rowValue xs) (rowValue ys) count).1 = some (EncodedSequenceAccess.sequence (merged xs ys)) := by
  have h := loop_value xs ys count [] (by omega)
  simp only [hc,List.take_length,List.append_nil] at h
  simp only [union,h,collectValues_value,prepareRow_value]

def unionBound (n B : ℕ) : ℕ := loopBound n n n B+32*(n^2+7*n+1)+rowBound n 2+12

theorem union_bound (xs ys : List Bool) (count : Bits) (B : ℕ)
    (hlen : ys.length = xs.length) (hc : value count = xs.length) (hw : count.length ≤ B) :
    (union (rowValue xs) (rowValue ys) count).2 ≤ unionBound xs.length B := by
  have hm : (merged xs ys).length = xs.length := by simp [merged,hlen]
  have hv := loop_value xs ys count [] (by omega)
  rw [hc,← hm,List.take_length,List.append_nil] at hv
  have hl := loop_bound xs ys count [] B hw
  have hcopy := collectValues_bound (merged xs ys) 2 (merged_size xs ys)
  have hrow := prepareRow_bound (merged xs ys) 2 (merged_size xs ys)
  simp only [hlen,hc] at hl
  simp only [hm] at hcopy hrow
  simp only [union,hv,collectValues_value]
  unfold unionBound
  omega

theorem merged_vector {n : ℕ} (x y : RetainedGridState.Flags n) :
    merged x.toList y.toList = (RetainedGridState.unionFlags x y).toList.map Value.flag := by
  have he : Vector.zipWith Bool.or x y = RetainedGridState.unionFlags x y := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_zipWith,RetainedGridState.unionFlags,Vector.getElem_ofFn]
  rw [← he,Vector.toList_zipWith,List.map_zipWith]
  rfl

/-- Exact data operation used inside every reached `roundData` call. Both
representation maps are mathematical observations of the retained input. -/
theorem source_union {n : ℕ} (x y : RetainedGridState.Flags n) (count : Bits)
    (hc : value count = n) :
    (union (rowValue x.toList) (rowValue y.toList) count).1 =
      some (rowValue (EncodedRoundingState.union x y).1.toList) := by
  rw [EncodedRoundingState.union_value]
  have hcount : value count = (merged x.toList y.toList).length := by simpa [merged] using hc
  rw [union_value _ _ _ hcount,merged_vector]
  rfl

theorem source_union_bound {n : ℕ} (x y : RetainedGridState.Flags n) (count : Bits) (B : ℕ)
    (hc : value count = n) (hw : count.length ≤ B) :
    (union (rowValue x.toList) (rowValue y.toList) count).2 ≤ unionBound n B := by
  simpa using union_bound x.toList y.toList count B (by simp) (by simpa using hc) hw

theorem source_work_positive {n : ℕ} (x y : RetainedGridState.Flags n) :
    1 ≤ (EncodedRoundingState.union x y).2 := by
  unfold EncodedRoundingState.union
  rw [EncodedRoundingInput.tabulate_work]
  unfold EncodedRoundingInput.arrayBound
  omega

/-- A proved body-to-annotation domination for this actual operation. The
multiplier is derived from the fixed execution above, not an assumed cost of
an arbitrary function. Later controller composition may take a common maximum
over the separately certified reached bodies. -/
theorem source_union_dominated {n : ℕ} (x y : RetainedGridState.Flags n)
    (count : Bits) (B : ℕ) (hc : value count = n) (hw : count.length ≤ B) :
    (union (rowValue x.toList) (rowValue y.toList) count).2 ≤
      unionBound n B*(EncodedRoundingState.union x y).2 := by
  apply (source_union_bound x y count B hc hw).trans
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (unionBound n B) (source_work_positive x y)

/-- The supplied values are actual retained state rows. Their equations are
representation premises, not requests to execute an encoding map at this call. -/
theorem reached_roundData_cut {n : ℕ} (s : RetainedGridState.Data n)
    (p : RetainedGridState.Pair n) (cut : RetainedGridState.Flags n)
    (storedOld storedNew : Value) (count : Bits)
    (hold : storedOld = rowValue s.cut.toList) (hnew : storedNew = rowValue cut.toList)
    (hc : value count = n) :
    (union storedOld storedNew count).1 =
      some (rowValue (EncodedRoundingState.roundData s p cut).1.cut.toList) := by
  subst storedOld
  subst storedNew
  simpa only [EncodedRoundingState.roundData] using source_union s.cut cut count hc

end DirectedFlowCutGap.EncodedFlagUnion
