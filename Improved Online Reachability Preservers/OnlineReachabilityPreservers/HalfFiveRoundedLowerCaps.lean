import OnlineReachabilityPreservers.HalfFiveStartingLowerCaps

/-! Integer degree and length thresholds recover the exact lower caps in some budget ranges. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- The total charge for deleting one item at just below each original
lower cap, summed over the original budgets. -/
def frozenLowerPeelCharge (n p M : ℕ) : ℕ :=
  n*((M-1)/(4*n))+p*((M-1)/(4*p))

private theorem frozen_lower_cap_iff_floor_lt {M q x : ℕ} (positive : 0 < M) (budget : 0 < q) :
    (M:ℝ)/(4*(q:ℝ)) ≤ (x:ℝ) ↔ (M-1)/(4*q) < x := by
  have width : 0 < 4*q := by omega
  have realWidth : 0 < 4*(q:ℝ) := by exact_mod_cast width
  rw [div_le_iff₀ realWidth, Nat.div_lt_iff_lt_mul width]
  have equivalent : M ≤ x*(4*q) ↔ M-1 < x*(4*q) := by omega
  exact (by exact_mod_cast equivalent)

/-- Fractions just above the integer removal threshold force the exact cap. -/
theorem frozen_lower_fraction_interval {M q : ℕ} (positive : 0 < M) (budget : 0 < q) :
    let t := (M-1)/(4*q)
    let bound := (q:ℝ)*(t:ℝ)/(M:ℝ)
    0 ≤ bound ∧ bound < 1/4 ∧
      ∀ {a : ℝ}, bound < a → ∀ {x : ℕ}, a*(M:ℝ)/q ≤ x →
        (M:ℝ)/(4*(q:ℝ)) ≤ x := by
  let t := (M-1)/(4*q)
  let bound := (q:ℝ)*(t:ℝ)/(M:ℝ)
  have rq : (0:ℝ) < q := by exact_mod_cast budget
  have rm : (0:ℝ) < M := by exact_mod_cast positive
  have prior : (t:ℝ)*(4*(q:ℝ)) < (M:ℝ) := by
    have floor : t*(4*q) ≤ M-1 := Nat.div_mul_le_self _ _
    exact_mod_cast (show t*(4*q) < M by omega)
  have top : bound < 1/4 := by
    dsimp only [bound]
    exact (div_lt_iff₀ rm).mpr (by linarith only [prior])
  refine ⟨by positivity,top,?_⟩
  intro a higher x hx
  have below : (t:ℝ) < a*(M:ℝ)/q := by
    apply (lt_div_iff₀ rq).mpr
    have agrees : (t:ℝ)*(q:ℝ) = bound*(M:ℝ) := by
      unfold bound
      field_simp [rm.ne']
    rw [agrees]
    exact mul_lt_mul_of_pos_right higher rm
  have xLarge : t < x := by exact_mod_cast below.trans_le hx
  exact (frozen_lower_cap_iff_floor_lt positive budget).mpr xLarge

private theorem frozen_lower_fractions_of_charge {n p M : ℕ} (positive : 0 < M)
    (hn : 0 < n) (hp : 0 < p) (charge : 15*frozenLowerPeelCharge n p M < 7*M) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a ≤ 1/4 ∧ b ≤ 1/4 ∧ a+b ≤ 7/15 ∧
      (∀ {x : ℕ}, a*(M:ℝ)/n ≤ x → (M:ℝ)/(4*(n:ℝ)) ≤ x) ∧
      (∀ {y : ℕ}, b*(M:ℝ)/p ≤ y → (M:ℝ)/(4*(p:ℝ)) ≤ y) := by
  let dn := (n:ℝ)*(((M-1)/(4*n):ℕ):ℝ)/(M:ℝ)
  let lp := (p:ℝ)*(((M-1)/(4*p):ℕ):ℝ)/(M:ℝ)
  obtain ⟨dn0,dnTop,degree⟩ := frozen_lower_fraction_interval positive hn
  obtain ⟨lp0,lpTop,path⟩ := frozen_lower_fraction_interval positive hp
  have sum : dn+lp < 7/15 := by
    have real : 15*((n:ℝ)*(((M-1)/(4*n):ℕ):ℝ)+(p:ℝ)*(((M-1)/(4*p):ℕ):ℝ)) < 7*(M:ℝ) := by
      exact_mod_cast (show 15*(n*((M-1)/(4*n))+p*((M-1)/(4*p))) < 7*M from charge)
    dsimp only [dn,lp]
    rw [← add_div]
    apply (div_lt_iff₀ (Nat.cast_pos.mpr positive)).mpr
    linarith only [real]
  let gap := min ((1/4-dn)/2) (min ((1/4-lp)/2) ((7/15-dn-lp)/2))
  have dGap : gap ≤ (1/4-dn)/2 := min_le_left _ _
  have lGap : gap ≤ (1/4-lp)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have sGap : gap ≤ (7/15-dn-lp)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have gp : 0 < gap := by
    have first : dn < 1/4 := dnTop
    have second : lp < 1/4 := lpTop
    exact lt_min (by linarith only [first]) (lt_min (by linarith only [second]) (by linarith only [sum]))
  have d0 : 0 ≤ dn := dn0
  have l0 : 0 ≤ lp := lp0
  exact ⟨dn+gap,lp+gap,add_nonneg d0 gp.le,add_nonneg l0 gp.le,by linarith only [dGap,gp],
    by linarith only [lGap,gp],by linarith only [sGap],
    fun {_} => degree (by linarith only [gp] : dn < dn+gap),
    fun {_} => path (by linarith only [gp] : lp < lp+gap)⟩

/-- When the integer removal charge leaves sufficient room, a simple
half-five family has a witness with all four exact starting-average caps. -/
theorem regularization_list_frozen_half_five_of_integer_lower_charge {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (room : let M := ∑ i, (paths i).length; 15*frozenLowerPeelCharge n p M < 7*M) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 930*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨a,b,a0,b0,aMax,bMax,sum,degree,path⟩ :=
    frozen_lower_fractions_of_charge (hn.trans_le dense) hn hp room
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,vBounds,iBounds⟩ :=
    regularization_list_half_five_of_starting_lower_caps paths simple free hn hp dense long a0 b0 aMax bMax sum
  exact ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,
    fun v => ⟨degree (vBounds v).1,(vBounds v).2⟩,
    fun i => ⟨path (iBounds i).1,(iBounds i).2⟩⟩

/-- The same charge test gives all four exact starting-average caps for
distinct nonempty input and output rows. -/
theorem regularization_literal_frozen_half_five_of_integer_lower_charge {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    (room : let M := ∑ i, (paths i).length; 15*frozenLowerPeelCharge n p M < 7*M) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧
      HalfBridgeFree (Before rows) 5 ∧ M ≤ 930*(∑ i, (rows i).length) ∧
      (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨a,b,a0,b0,aMax,bMax,sum,degree,path⟩ :=
    frozen_lower_fractions_of_charge (hn.trans_le dense) hn hp room
  obtain ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,rowsFree,retain,upper,vBounds,iBounds⟩ :=
    regularization_literal_half_five_of_starting_lower_caps paths distinct valid free hn hp dense a0 b0 aMax bMax sum
  exact ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,rowsFree,retain,upper,
    fun v => ⟨degree (vBounds v).1,(vBounds v).2⟩,
    fun i => ⟨path (iBounds i).1,(iBounds i).2⟩⟩

end OnlineReachabilityPreservers
