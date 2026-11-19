import DirectedFlowCutGap.BinaryDivision

/-! Euclidean gcd on literal binary words. Two nonterminal divisions
decrease the denominator by a bit, so the fuel is a stored width. -/

namespace DirectedFlowCutGap.BinaryEuclidean

open BinaryArithmetic BinaryDivision

def loop : ℕ → Bits → Bits → Bits × ℕ
  | 0,a,_ => (a,1)
  | fuel+1,a,b =>
    let bz := isZero b
    if bz.1 then (a,bz.2+4) else
      let r := divide a b
      let rz := isZero r.remainder
      if rz.1 then (b,bz.2+r.steps+rz.2+8) else
        let s := divide b r.remainder
        let tail := loop fuel r.remainder s.remainder
        (tail.1,bz.2+r.steps+rz.2+s.steps+tail.2+16)

private theorem halve {a b : ℕ} (hb : 0 < b) (hr : 0 < a%b) : 2*(b%(a%b)) < b := by
  let r := a%b
  change 2*(b%r)<b
  have h1 : r < b := Nat.mod_lt _ hb
  have h2 : b%r < r := Nat.mod_lt _ hr
  by_cases small : 2*r ≤ b
  · omega
  · have shift : b%r=b-r := by
      rw [Nat.mod_eq_sub_mod h1.le,Nat.mod_eq_of_lt (by omega : b-r < r)]
    omega

private theorem once (a b : ℕ) : a.gcd b = b.gcd (a%b) := by
  rw [Nat.gcd_comm a b,Nat.gcd_rec b a,Nat.gcd_comm (a%b) b]

theorem loop_value (fuel : ℕ) (a b : Bits) (enough : (value b).size ≤ fuel) :
    value (loop fuel a b).1 = (value a).gcd (value b) := by
  induction fuel generalizing a b with
  | zero =>
    have low := Nat.size_le.mp enough
    have h : value b=0 := by simp only [pow_zero] at low; omega
    simp only [loop,h,Nat.gcd_zero_right]
  | succ fuel ih =>
    by_cases zero : (isZero b).1=true
    · have hz := (isZero_spec b).1.mp zero
      simp only [loop,ite_eq_left zero,hz,Nat.gcd_zero_right]
    · let r := divide a b
      let s := divide b r.remainder
      have hB : 0 < value b := Nat.pos_of_ne_zero (fun h => zero ((isZero_spec b).1.mpr h))
      have hr : value r.remainder = value a % value b := (divide_spec a b).2.1
      have hs : value s.remainder = value b % value r.remainder := (divide_spec b r.remainder).2.1
      have sameGcd : (value a).gcd (value b) = (value b).gcd (value r.remainder) := by
        rw [hr]
        exact once _ _
      change value (if (isZero b).1 then (a,(isZero b).2+4) else
        if (isZero r.remainder).1 then (b,(isZero b).2+r.steps+(isZero r.remainder).2+8) else
        ((loop fuel r.remainder s.remainder).1,
          (isZero b).2+r.steps+(isZero r.remainder).2+s.steps+(loop fuel r.remainder s.remainder).2+16)).1
          = (value a).gcd (value b)
      rw [ite_eq_right zero,sameGcd]
      by_cases z : (isZero r.remainder).1=true
      · rw [ite_eq_left z,(isZero_spec _).1.mp z,Nat.gcd_zero_right]
      · have hn : 0 < value r.remainder :=
          Nat.pos_of_ne_zero (fun h => z ((isZero_spec r.remainder).1.mpr h))
        have decrease : 2*value s.remainder < value b := by
          rw [hs,hr]
          exact halve hB (by rw [← hr]; exact hn)
        have sz := Nat.size_le.mp enough
        rw [pow_succ] at sz
        have next : (value s.remainder).size ≤ fuel := Nat.size_le.mpr (by omega)
        rw [ite_eq_right z,ih r.remainder s.remainder next,once (value b) (value r.remainder),hs]

def stepBudget {R : Type*} [Semiring R] (B : R) : R := 2048*(B+1)^2+8*(B+1)+16

theorem loop_paid {B : ℕ} (fuel : ℕ) (a b : Bits) (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (loop fuel a b).1.length ≤ B ∧ (loop fuel a b).2 ≤ fuel*stepBudget B+1 := by
  induction fuel generalizing a b with
  | zero => exact ⟨ha,by simp [loop]⟩
  | succ fuel ih =>
    have bz := (isZero_spec b).2.trans (Nat.mul_le_mul_left 4 (Nat.add_le_add_right hb 1))
    by_cases zero : (isZero b).1 = true
    · simp only [loop,ite_eq_left zero]
      refine ⟨ha,?_⟩
      rw [Nat.add_mul,Nat.one_mul]
      unfold stepBudget
      omega
    · let r := divide a b
      let s := divide b r.remainder
      have dr : r.steps ≤ 1024*(B+1)^2 := divide_charge_bound ha hb
      have rlen : r.remainder.length ≤ B := by
        rw [(divide_spec a b).2.2.2]
        exact (Nat.size_le_size (Nat.mod_le _ _)).trans ((Nat.size_le.mpr (value_lt _)).trans ha)
      have rz := (isZero_spec r.remainder).2.trans (Nat.mul_le_mul_left 4 (Nat.add_le_add_right rlen 1))
      by_cases z : (isZero r.remainder).1=true
      · rw [loop,ite_eq_right zero,ite_eq_left (show (isZero (divide a b).remainder).1=true from z)]
        refine ⟨hb,?_⟩
        change (isZero b).2+r.steps+(isZero r.remainder).2+8 ≤ _
        rw [Nat.add_mul,Nat.one_mul]
        unfold stepBudget
        omega
      · have ds : s.steps ≤ 1024*(B+1)^2 := divide_charge_bound hb rlen
        have slen : s.remainder.length ≤ B := by
          rw [(divide_spec b r.remainder).2.2.2]
          exact (Nat.size_le_size (Nat.mod_le _ _)).trans ((Nat.size_le.mpr (value_lt _)).trans hb)
        have tail := ih r.remainder s.remainder rlen slen
        rw [loop,ite_eq_right zero,ite_eq_right (show (isZero (divide a b).remainder).1≠true from z)]
        refine ⟨tail.1,?_⟩
        change (isZero b).2+r.steps+(isZero r.remainder).2+s.steps+(loop fuel r.remainder s.remainder).2+16 ≤ _
        rw [Nat.add_mul,Nat.one_mul]
        unfold stepBudget at tail ⊢
        omega

def gcd (a b : Bits) : Bits × ℕ := loop b.length a b

theorem gcd_value (a b : Bits) : value (gcd a b).1 = (value a).gcd (value b) :=
  loop_value b.length a b (Nat.size_le.mpr (value_lt b))

theorem gcd_paid {a b : Bits} {B : ℕ} (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (gcd a b).1.length ≤ B ∧ (gcd a b).2 ≤ B*stepBudget B+1 :=
  let bound := loop_paid b.length a b ha hb
  ⟨bound.1,bound.2.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hb) 1)⟩

end DirectedFlowCutGap.BinaryEuclidean
