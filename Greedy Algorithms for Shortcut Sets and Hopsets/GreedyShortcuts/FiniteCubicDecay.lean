import GreedyShortcuts.FiniteQuadraticDecay

/-! Cubic natural decay is quadratic reciprocal decay of the squared account.
A separate positive-step floor yields an exact rounded two-block bound. -/
namespace GreedyShortcuts.FinitePotential

theorem cubic_reciprocal_decay (P : ℕ → ℕ) (K : ℕ) (hmono : Antitone P)
    (hcube : ∀ i,(P i)^3≤K*(P i-P (i+1))) (n : ℕ) :
    (n+1)*(P n)^2≤K := by
  have hsqmono : Antitone (fun i => (P i)^2) := fun i j hij =>
    Nat.pow_le_pow_left (hmono hij) 2
  apply reciprocal_decay (fun i => (P i)^2) K hsqmono _ n
  intro i
  have hle := hmono (Nat.le_succ i)
  have hsub := Nat.sub_add_cancel hle
  have hsqsub := Nat.sub_add_cancel (Nat.pow_le_pow_left hle 2)
  have hdiff : P i*(P i-P (i+1))≤(P i)^2-(P (i+1))^2 := by nlinarith
  have hmul := Nat.mul_le_mul_left (P i) (hcube i)
  have hright := Nat.mul_le_mul_left K hdiff
  nlinarith

/-- For every positive R with R³≤D², cubic decay plus the active D² floor
stops after 2*(256*S/R²+1) rounds. No real roots or asymptotic premise occurs. -/
theorem zero_after_cubic_floor (P : ℕ → ℕ) (S D R : ℕ) (hR : 0<R)
    (hscale : R^3≤D^2) (hmono : Antitone P)
    (hcube : ∀ i,(P i)^3≤256*S^3*(P i-P (i+1)))
    (hfloor : ∀ i,0<P i → D^2≤25*(P i-P (i+1))) :
    P (2*(256*S/R^2+1))=0 := by
  let B := 256*S/R^2+1
  have hBR : 256*S≤B*R^2 := by
    have hmod := Nat.mod_lt (256*S) (pow_pos hR 2)
    have hdiv := Nat.mod_add_div (256*S) (R^2)
    dsimp [B]
    nlinarith
  have hrec := cubic_reciprocal_decay P (256*S^3) hmono hcube B
  have hmiddle : P B≤S*R := by
    have hm := Nat.mul_le_mul_left (S^2) hBR
    have hh : (B+1)*(P B)^2≤(B+1)*(S*R)^2 := by nlinarith
    have hs := Nat.le_of_mul_le_mul_left hh (Nat.zero_lt_succ B)
    exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp hs
  have hbudget : 25*S*R≤B*D^2 := by
    have hm := Nat.mul_le_mul_right R hBR
    have hs := Nat.mul_le_mul_left B hscale
    nlinarith
  by_contra hne
  have hp : 0<P (2*B) := Nat.pos_of_ne_zero hne
  have hsum : ∀ j,j≤B → 25*P (B+j)+j*D^2≤25*P B := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro hj
        have hi := ih (by omega)
        have hpos : 0<P (B+j) := hp.trans_le (hmono (by omega : B+j≤2*B))
        have hd := hfloor (B+j) hpos
        have hm : P (B+(j+1))≤P (B+j) := hmono (by omega)
        have he := Nat.add_sub_of_le hm
        have he25 := congrArg (fun z : ℕ => 25*z) he
        simp only [Nat.add_assoc] at hd he25
        nlinarith
  have hlast := hsum B (Nat.le_refl _)
  have he : B+B=2*B := by omega
  rw [he] at hlast
  nlinarith

end GreedyShortcuts.FinitePotential
