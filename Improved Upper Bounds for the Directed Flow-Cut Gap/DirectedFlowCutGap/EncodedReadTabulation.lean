import DirectedFlowCutGap.EncodedSequenceAccess

/-!
# Binary-controlled tabulation of the concrete retained-read callback

The fixed loop reads indices in descending order and prepends each returned
value to its accumulator, exactly the callback order of List.ofFn/Fin.foldr.
It uses actual binary zero and predecessor operations and the full-copy read
body. No higher-order callback is admitted. The final collect is the explicit
suffix-copy constructor program, executed once on the actual loop output.

Natural denotations below occur in termination and specification proofs, not
as executable loop fuel. The caller must bound the numerical count, stored
index width, sequence length and actual payload sizes. Those remain visible
until the concrete input/state shape invariants instantiate them.
-/
namespace DirectedFlowCutGap.EncodedReadTabulation
open BinaryArithmetic EncodedSequenceAccess

/-- One actual retained read before each recursive continuation. -/
def loop (table : Value) (fuel : Bits) (acc : List Value) : Option (List Value) × ℕ :=
  let z := isZero fuel
  if hz : z.1 = true then (some acc,z.2+4) else
    let p := predCore fuel
    let head := read p.1 table
    match head.1 with
    | none => (none,z.2+p.2+head.2+8)
    | some x =>
        let r := loop table p.1 (x::acc)
        (r.1,z.2+p.2+head.2+r.2+12)
termination_by value fuel
decreasing_by
  have hv : 0 < value fuel := Nat.pos_of_ne_zero
    (fun h => hz ((isZero_spec fuel).1.mpr h))
  have hp := (predCore_spec fuel).1 hv
  omega

/-- The operational body permits only the named zero/predecessor/read calls,
list construction and its own recursive continuation. Charges are observations
of this derivation, not executed natural counter arithmetic. -/
inductive LoopExec (table : Value) : Bits → List Value → Option (List Value) → ℕ → Prop
  | zero (fuel : Bits) (acc : List Value) :
      (isZero fuel).1 = true → LoopExec table fuel acc (some acc) ((isZero fuel).2+4)
  | missing (fuel : Bits) (acc : List Value) (q : ℕ) :
      (isZero fuel).1 = false → ReadExec (predCore fuel).1 table none q →
      LoopExec table fuel acc none ((isZero fuel).2+(predCore fuel).2+q+8)
  | step (fuel : Bits) (acc : List Value) (x : Value) (out : Option (List Value)) (q r : ℕ) :
      (isZero fuel).1 = false → ReadExec (predCore fuel).1 table (some x) q →
      LoopExec table (predCore fuel).1 (x::acc) out r →
      LoopExec table fuel acc out ((isZero fuel).2+(predCore fuel).2+q+r+12)

theorem loop_exec (table : Value) (fuel : Bits) (acc : List Value) :
    LoopExec table fuel acc (loop table fuel acc).1 (loop table fuel acc).2 := by
  have aux : ∀ k, ∀ f : Bits, value f = k → ∀ a : List Value,
      LoopExec table f a (loop table f a).1 (loop table f a).2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro f hf a
      rw [loop]
      cases hz : (isZero f).1 with
      | true =>
          simpa only [hz,dite_true] using LoopExec.zero (table := table) f a hz
      | false =>
          have hv : 0 < value f := Nat.pos_of_ne_zero (fun h => by
            have ht := (isZero_spec f).1.mpr h
            rw [hz] at ht
            contradiction)
          have hp := (predCore_spec f).1 hv
          have hr := read_exec (predCore f).1 table
          cases hread : (read (predCore f).1 table).1 with
          | none =>
              rw [hread] at hr
              simpa only [hz,Bool.false_eq_true,dite_false,hread] using
                LoopExec.missing f a _ hz hr
          | some x =>
              rw [hread] at hr
              have hrec := ih (value (predCore f).1) (by omega) (predCore f).1 rfl (x::a)
              simpa only [hz,Bool.false_eq_true,dite_false,hread] using
                LoopExec.step f a x _ _ _ hz hr hrec
  exact aux (value fuel) fuel rfl acc

/-- Prefix reachability names only recursive calls actually admitted by the
fixed body. It is used to bound intermediate accumulators, not just the result. -/
inductive Reach (table : Value) (initial : Bits) (input : List Value) :
    Bits → List Value → Prop
  | start : Reach table initial input initial input
  | step (fuel : Bits) (acc : List Value) (x : Value) (q : ℕ) :
      Reach table initial input fuel acc → (isZero fuel).1 = false →
      ReadExec (predCore fuel).1 table (some x) q →
      Reach table initial input (predCore fuel).1 (x::acc)

theorem Reach.invariants {xs input acc : List Value} {initial fuel : Bits}
    (h : Reach (sequence xs) initial input fuel acc) :
    fuel.length ≤ initial.length ∧
    value fuel+acc.length = value initial+input.length ∧
    ∀ x∈acc, x∈xs ∨ x∈input := by
  induction h with
  | start => exact ⟨le_rfl,rfl,fun x hx => Or.inr hx⟩
  | step f a x q hp hz hr ih =>
      have hf : 0 < value f := Nat.pos_of_ne_zero (fun h => by
        have ht := (isZero_spec f).1.mpr h
        rw [hz] at ht
        contradiction)
      have hv := (predCore_spec f).1 hf
      have hx : x∈xs := by
        have he := hr.result.1.symm
        rw [read_get] at he
        exact List.mem_of_getElem? he
      refine ⟨(predCore_spec f).2.1.trans ih.1,?_,?_⟩
      · simp only [List.length_cons]
        omega
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl hx
        · exact ih.2.2 y hy

/-- Every reached accumulator has a polynomial representation bound under the
same actual input-payload bound; copying cannot introduce larger encodings. -/
theorem Reach.representation_bound {xs input acc : List Value} {initial fuel : Bits}
    (h : Reach (sequence xs) initial input fuel acc) (S : ℕ)
    (hs : ∀ x∈xs, x.size ≤ S) (hi : ∀ x∈input, x.size ≤ S) :
    (sequence acc).size ≤ (value initial+input.length)*(S+1)+1 := by
  have inv := h.invariants
  have ha : ∀ x∈acc, x.size ≤ S := by
    intro x hx
    exact (inv.2.2 x hx).elim (hs x) (hi x)
  exact (sequence_size_bound ha).trans (by gcongr; omega)

theorem loop_value (xs : List Value) (fuel : Bits) (acc : List Value)
    (hcount : value fuel ≤ xs.length) :
    (loop (sequence xs) fuel acc).1 = some (xs.take (value fuel)++acc) := by
  have aux : ∀ k, ∀ f : Bits, value f = k → ∀ a : List Value,
      value f ≤ xs.length →
      (loop (sequence xs) f a).1 = some (xs.take (value f)++a) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro f hf a hc
      rw [loop]
      split_ifs with hz
      · have hv := (isZero_spec f).1.mp hz
        simp only [hv,List.take_zero,List.nil_append]
      · have hv : 0 < value f := Nat.pos_of_ne_zero
          (fun h => hz ((isZero_spec f).1.mpr h))
        have hp := (predCore_spec f).1 hv
        have hlt : value (predCore f).1 < xs.length := by omega
        have hr : (read (predCore f).1 (sequence xs)).1 =
            some xs[value (predCore f).1] := by
          rw [read_get,List.getElem?_eq_getElem hlt]
        simp only [hr]
        rw [ih (value (predCore f).1) (by omega) (predCore f).1 rfl
          (xs[value (predCore f).1]::a) (by omega)]
        rw [← hp,List.take_succ_eq_append_getElem hlt,List.append_assoc]
        rfl
  exact aux (value fuel) fuel rfl acc hcount

def loopBound (count length B S : ℕ) : ℕ :=
  (count+1)*(20*(length+1)*(B+1)+4*S+24*(B+1))

theorem loop_bound (xs : List Value) (fuel : Bits) (acc : List Value) (B S : ℕ)
    (hf : fuel.length ≤ B) (hs : ∀ x∈xs, x.size ≤ S) :
    (loop (sequence xs) fuel acc).2 ≤ loopBound (value fuel) xs.length B S := by
  have aux : ∀ k, ∀ f : Bits, value f = k → ∀ a : List Value,
      f.length ≤ B → (loop (sequence xs) f a).2 ≤ loopBound (value f) xs.length B S := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro f hk a hf
      have hz := (isZero_spec f).2
      rw [loop]
      split_ifs with hzero
      · have hv := (isZero_spec f).1.mp hzero
        unfold loopBound
        rw [hv]
        nlinarith
      · have hv : 0 < value f := Nat.pos_of_ne_zero
          (fun h => hzero ((isZero_spec f).1.mpr h))
        have hp := predCore_spec f
        have hvp := hp.1 hv
        have hpf : (predCore f).1.length ≤ B := hp.2.1.trans hf
        have hread := read_bound (predCore f).1 xs B S hpf hs
        let C := 20*(xs.length+1)*(B+1)+4*S+24*(B+1)
        have hstep : (isZero f).2+(predCore f).2+
            (read (predCore f).1 (sequence xs)).2+12 ≤ C := by
          dsimp only [C]
          nlinarith [hp.2.2]
        cases hr : (read (predCore f).1 (sequence xs)).1 with
        | none =>
            simp only [hr]
            change _ ≤ (value f+1)*C
            exact (show _ ≤ C by omega).trans (Nat.le_mul_of_pos_left C (by omega))
        | some x =>
            have hrec := ih (value (predCore f).1) (by omega) (predCore f).1 rfl (x::a) hpf
            have hrec' : (loop (sequence xs) (predCore f).1 (x::a)).2 ≤ value f*C := by
              simpa only [loopBound,hvp] using hrec
            simp only [hr]
            change _ ≤ (value f+1)*C
            calc
              _ ≤ C+value f*C := by omega
              _ = (value f+1)*C := by ring
  exact aux (value fuel) fuel rfl acc hf

/-- Actual loop output is consumed once by the full-copy collect body. -/
def tabulate (table : Value) (count : Bits) : Option (List Value) × ℕ :=
  let r := loop table count []
  match r.1 with
  | none => (none,r.2+4)
  | some xs =>
      let out := collectValues xs
      (some out.1,r.2+out.2+8)

inductive TabulateExec (table : Value) (count : Bits) : Option (List Value) → ℕ → Prop
  | missing (q : ℕ) : LoopExec table count [] none q → TabulateExec table count none (q+4)
  | found (xs out : List Value) (q r : ℕ) :
      LoopExec table count [] (some xs) q → CollectValuesExec xs out r →
      TabulateExec table count (some out) (q+r+8)

theorem tabulate_exec (table : Value) (count : Bits) :
    TabulateExec table count (tabulate table count).1 (tabulate table count).2 := by
  have h := loop_exec table count []
  cases hr : (loop table count []).1 with
  | none =>
      rw [hr] at h
      simpa only [tabulate,hr] using TabulateExec.missing (table := table) (count := count) _ h
  | some xs =>
      rw [hr] at h
      simpa only [tabulate,hr] using
        TabulateExec.found (table := table) (count := count) xs _ _ _ h (collectValues_exec xs)

theorem tabulate_value (xs : List Value) (count : Bits) (hc : value count = xs.length) :
    (tabulate (sequence xs) count).1 = some xs := by
  have h := loop_value xs count [] (by omega)
  simp only [hc,List.take_length,List.append_nil] at h
  simp only [tabulate,h,collectValues_value]

def tabulateBound (n B S : ℕ) : ℕ :=
  loopBound n n B S+8*(S+2)*(n^2+7*n+1)+8

theorem tabulate_bound (xs : List Value) (count : Bits) (B S : ℕ)
    (hc : value count = xs.length) (hw : count.length ≤ B)
    (hs : ∀ x∈xs, x.size ≤ S) :
    (tabulate (sequence xs) count).2 ≤ tabulateBound xs.length B S := by
  have hv := loop_value xs count [] (by omega)
  simp only [hc,List.take_length,List.append_nil] at hv
  have hl := loop_bound xs count [] B S hw hs
  have hcopy := collectValues_bound xs S hs
  simp only [tabulate,hv]
  unfold tabulateBound
  rw [hc] at hl
  omega

/-- Closed refinement of the actual retained-read tabulation. The source
callback is fixed to table lookup; no arbitrary f/encoder is run by this code. -/
theorem retained_read_tabulation {n : ℕ} (table : Vector Value n) (count : Bits)
    (hc : value count = n) :
    (tabulate (sequence table.toList) count).1 =
      some (EncodedRoundingInput.tabulate (EncodedArrayStorage.readCallback table)).1.toList := by
  rw [EncodedArrayStorage.read_tabulate_value]
  exact tabulate_value table.toList count (by simpa using hc)

/-- Complete fixed-body certificate for this concrete callback family. -/
theorem retained_read_certificate {n : ℕ} (table : Vector Value n) (count : Bits)
    (B S : ℕ) (hc : value count = n) (hw : count.length ≤ B)
    (hs : ∀ x∈table.toList, x.size ≤ S) :
    ∃ q, TabulateExec (sequence table.toList) count
      (some (EncodedRoundingInput.tabulate (EncodedArrayStorage.readCallback table)).1.toList) q ∧
      q ≤ tabulateBound n B S := by
  have h := tabulate_exec (sequence table.toList) count
  rw [retained_read_tabulation table count hc] at h
  exact ⟨_,h,by simpa using tabulate_bound table.toList count B S (by simpa using hc) hw hs⟩

end DirectedFlowCutGap.EncodedReadTabulation
