import GreedyShortcuts.FinitePotential

/-! Integer reciprocal decay and a two-stage stopping bound. -/
namespace GreedyShortcuts.FinitePotential

private theorem quadratic_product_step (K n a b : ℕ) (hK : 0<K)
    (hab : a≤b) (hq : b^2≤K*(b-a)) (hb : (n+1)*b≤K) :
    (n+2)*a≤K := by
  let x := K-(n+1)*b
  have hx : x+(n+1)*b=K := Nat.sub_add_cancel hb
  have hx2 := congrArg (fun z : ℕ => z*z) hx
  have hxb := congrArg (fun z : ℕ => (n+2)*b*z) hx
  have hpoly : (n+2)*K*b≤K^2+(n+2)*b^2 := by
    nlinarith [Nat.zero_le (n*b*x),Nat.zero_le (x*x),Nat.zero_le (b*b)]
  have hs := Nat.mul_le_mul_left (n+2) hq
  have he := congrArg (fun z : ℕ => (n+2)*K*z) (Nat.add_sub_of_le hab)
  have hm : K*((n+2)*a)≤K*K := by nlinarith
  exact Nat.le_of_mul_le_mul_left hm hK

/-- No real reciprocals or division rounding are needed for the sharp
integer reciprocal-decay estimate. -/
theorem reciprocal_decay (P : ℕ → ℕ) (K : ℕ) (hmono : Antitone P)
    (hstep : ∀ i,(P i)^2≤K*(P i-P (i+1))) (n : ℕ) :
    (n+1)*P n≤K := by
  have hstart : P 0≤K := by
    have hq := hstep 0
    have hd : P 0-P 1≤P 0 := Nat.sub_le _ _
    have hh := hq.trans (Nat.mul_le_mul_left K hd)
    nlinarith
  by_cases hK : K=0
  · have hp : P n≤P 0 := hmono (Nat.zero_le n)
    simp only [hK] at hstart ⊢
    have hz : P n=0 := by omega
    simp only [hz,Nat.mul_zero,Nat.le_refl]
  · have hKpos : 0<K := Nat.pos_of_ne_zero hK
    induction n with
    | zero => simpa using hstart
    | succ n ih =>
        simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using
          quadratic_product_step K n (P (n+1)) (P n) hKpos
            (hmono (Nat.le_succ n)) (hstep n) ih

/-- Quadratic decay plus a fixed active-step floor yields a logarithm-free
stopping bound. The first block brings potential to S*D; the second spends
that remaining budget. -/
theorem zero_after_quadratic (P : ℕ → ℕ) (S D : ℕ) (hD : 0<D)
    (hmono : Antitone P)
    (hquad : ∀ i,(P i)^2≤25*S^2*(P i-P (i+1)))
    (hfloor : ∀ i,0<P i → D^2≤25*(P i-P (i+1))) :
    P (2*(25*S/D+1))=0 := by
  let B := 25*S/D+1
  have hBD : 25*S≤B*D := by
    have hmod := Nat.mod_lt (25*S) hD
    have hdiv := Nat.mod_add_div (25*S) D
    dsimp [B]
    nlinarith
  have hrec := reciprocal_decay P (25*S^2) hmono hquad B
  have hmiddle : P B≤S*D := by
    have hmul := Nat.mul_le_mul_left S hBD
    have hscaled : (B+1)*P B≤(B+1)*(S*D) := by nlinarith
    exact Nat.le_of_mul_le_mul_left hscaled (Nat.zero_lt_succ B)
  by_contra hne
  have hp : 0<P (2*B) := by exact Nat.pos_of_ne_zero hne
  have hsum : ∀ j,j≤B → 25*P (B+j)+j*D^2≤25*P B := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro hj
        have hi := ih (by omega)
        have hjB : B+j≤2*B := by omega
        have hpos : 0<P (B+j) := hp.trans_le (hmono hjB)
        have hd := hfloor (B+j) hpos
        have hm : P (B+(j+1))≤P (B+j) := hmono (by omega)
        have he := Nat.add_sub_of_le hm
        have he25 := congrArg (fun z : ℕ => 25*z) he
        simp only [Nat.add_assoc] at hd he25
        nlinarith
  have hlast := hsum B (Nat.le_refl _)
  have hbudget := Nat.mul_le_mul_right D hBD
  have he : B+B=2*B := by omega
  rw [he] at hlast
  nlinarith

end GreedyShortcuts.FinitePotential
