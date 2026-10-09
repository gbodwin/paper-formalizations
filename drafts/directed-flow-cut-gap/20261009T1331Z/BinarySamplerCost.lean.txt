import DirectedFlowCutGap.BinaryBoundedSampler

/-!
# Actual bounded-sampler instruction and storage bounds

These bounds apply to every supported result of the concrete binary routine,
for any supplied bit law. The bit request is one primitive instruction in this
model. Pricing a more expensive callback or heap addresses is separate. The
bound uses both the numerical trial budget and the supplied list lengths, so
leading-zero input padding is never silently treated as free.
-/
namespace DirectedFlowCutGap.BinarySamplerCost
open BinaryArithmetic BinaryCounters BinaryBoundedSampler

theorem width_bits_length (bound : Bits) :
    (sizeBits bound).1.length ≤ bound.length+1 := by
  have h := (lengthBits_spec (trim bound).1).2.1
  have ht := (trim_spec bound).2.2.1
  simpa only [sizeBits] using h.trans (Nat.add_le_add_right ht 1)

theorem width_value_le (bound : Bits) : value (sizeBits bound).1 ≤ bound.length := by
  rw [(sizeBits_spec bound).1]
  exact Nat.size_le.mpr (value_lt bound)

theorem predecessor_length (fuel : Bits) :
    (predecessor fuel).1.length ≤ fuel.length := by
  rw [(predecessor_spec fuel).2.1]
  exact (Nat.size_le_size (Nat.sub_le _ _)).trans (Nat.size_le.mpr (value_lt fuel))

def instructionBound (bound fuel : Bits) : ℕ :=
  2048*(value fuel+1)*(value fuel+bound.length+fuel.length+2)^2

def Bounded (bound fuel : Bits) (r : Output bound) : Prop :=
  r.trials.length ≤ value fuel ∧
  r.consumed.length ≤ value fuel+bound.length+1 ∧
  r.steps ≤ instructionBound bound fuel

private theorem base_budget (B F z : ℕ) (hz : z ≤ 4*(F+1)) :
    z+8 ≤ 2048*(B+F+2)^2 := by
  have hs := Nat.le_self_pow (by decide : 2 ≠ 0) (B+F+2)
  nlinarith

private theorem step_budget (T B F z w x c p i a : ℕ)
    (hz : z ≤ 4*(F+1)) (hw : w ≤ 32*(B+1)^2)
    (hx : x ≤ 64*(B+2)^2) (hc : c ≤ 16*(B+1))
    (hp : p ≤ 32*(F+1)) (hi : i ≤ 8*T) (ha : a ≤ 16*(T+B+1)) :
    z+w+x+c+p+i+a+24 ≤ 2048*(T+B+F+2)^2 := by
  have hs := Nat.le_self_pow (by decide : 2 ≠ 0) (T+B+F+2)
  have hb1 : (B+1)^2 ≤ (T+B+F+2)^2 := Nat.pow_le_pow_left (by omega) 2
  have hb2 : (B+2)^2 ≤ (T+B+F+2)^2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith

noncomputable section

/-- This is a bound on supported executions of the actual recurrence, rather
than on a postulated transcript or on the decoded output magnitude alone. -/
theorem draw_bounded (bit : PMF Bool) (bound fuel : Bits) (positive : 0<value bound)
    {r : Output bound} (hr : r ∈ (draw bit bound positive fuel).support) :
    Bounded bound fuel r := by
  have aux : ∀ T, ∀ f : Bits, value f=T → ∀ r : Output bound,
      r ∈ (draw bit bound positive f).support → Bounded bound f r := by
    intro T
    induction T using Nat.strong_induction_on with
    | h T ih =>
      intro f hf r hr
      have hz := isZero_spec f
      have hw := sizeBits_spec bound
      have hwl := width_bits_length bound
      have hwv := width_value_le bound
      rw [draw] at hr
      split at hr
      next hzero =>
        have he := (PMF.mem_support_pure_iff _ _).mp hr
        subst r
        have hv := hz.1.mp hzero
        unfold Bounded instructionBound
        simp only [List.length_nil,hv,zero_add,zero_le,true_and]
        exact base_budget bound.length f.length (isZero f).2 hz.2
      next hzero =>
        have hv : 0<value f := Nat.pos_of_ne_zero (fun h => hzero (hz.1.mpr h))
        obtain ⟨x,hx,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
        have hxlen : x.bits.length ≤ bound.length := x.length_eq.le.trans hwv
        have hxcost : x.steps ≤ 64*(bound.length+2)^2 := by
          have h := x.steps_le
          unfold BinaryRandomWord.instructionBound at h
          calc
            x.steps ≤ 64*(value (sizeBits bound).1+1)*((sizeBits bound).1.length+1) := h
            _ ≤ 64*(bound.length+2)^2 := by
              calc
                _ ≤ 64*(bound.length+2)*(bound.length+2) :=
                  Nat.mul_le_mul (Nat.mul_le_mul_left 64 (by omega)) (by omega)
                _ = _ := by ring
        have hc := (compare_spec x.bits bound).2.2
        have hcl : max x.bits.length bound.length=bound.length := max_eq_right hxlen
        rw [hcl] at hc
        dsimp only at hr
        split at hr
        next accepted =>
          have he := (PMF.mem_support_pure_iff _ _).mp hr
          subst r
          unfold Bounded instructionBound
          simp only [List.length_cons,List.length_nil]
          refine ⟨by omega,by omega,?_⟩
          have hb := step_budget (value f) bound.length f.length (isZero f).2
            (sizeBits bound).2 x.steps (BinaryArithmetic.compare x.bits bound).steps 0 0 0
            hz.2 hw.2 hxcost hc (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
          have hm : 2048*(value f+bound.length+f.length+2)^2 ≤
              2048*(value f+1)*(value f+bound.length+f.length+2)^2 :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        next rejected =>
          obtain ⟨tail,htail,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
          have he := (PMF.mem_support_pure_iff _ _).mp hr
          subst r
          have hp := predecessor_spec f
          have hpl := predecessor_length f
          have hind := ih (value (predecessor f).1) (by rw [hp.1,← hf];omega)
            (predecessor f).1 rfl tail htail
          rcases hind with ⟨htlen,hblen,htcost⟩
          have ht := increment_spec true tail.trials
          have hb := add_spec false (sizeBits bound).1 tail.consumed
          have htlen' : tail.trials.length+1 ≤ value f := by rw [hp.1] at htlen;omega
          have hblen' : tail.consumed.length ≤ value f+bound.length := by
            rw [hp.1] at hblen
            omega
          have hmax : max (sizeBits bound).1.length tail.consumed.length ≤
              value f+bound.length := by omega
          have htailcost : tail.steps ≤
              2048*value f*(value f+bound.length+f.length+2)^2 := by
            unfold instructionBound at htcost
            calc
              _ ≤ 2048*(value (predecessor f).1+1)*
                  (value (predecessor f).1+bound.length+(predecessor f).1.length+2)^2 := htcost
              _ ≤ _ := by
                have hpred : value (predecessor f).1+1=value f := by rw [hp.1];omega
                rw [hpred]
                exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [hp.1];omega) 2)
          unfold Bounded advance instructionBound
          dsimp only
          refine ⟨by omega,by omega,?_⟩
          have hi : (increment true tail.trials).2 ≤ 8*value f :=
            ht.2.2.trans (Nat.mul_le_mul_left 8 htlen')
          have ha : (add false (sizeBits bound).1 tail.consumed).2 ≤
              16*(value f+bound.length+1) :=
            hb.2.2.trans (Nat.mul_le_mul_left 16 (by omega))
          have hstep := step_budget (value f) bound.length f.length (isZero f).2
            (sizeBits bound).2 x.steps (BinaryArithmetic.compare x.bits bound).steps
            (predecessor f).2 (increment true tail.trials).2
            (add false (sizeBits bound).1 tail.consumed).2 hz.2 hw.2 hxcost hc hp.2.2 hi ha
          calc
            _ ≤ 2048*value f*(value f+bound.length+f.length+2)^2+
                2048*(value f+bound.length+f.length+2)^2 := by omega
            _ = _ := by ring
  exact aux (value fuel) fuel rfl r hr

/-- Includes the actual initial zero-bound guard on both return branches. -/
def checkedInstructionBound (bound fuel : Bits) : ℕ :=
  instructionBound bound fuel+4*(bound.length+1)+8

theorem checked_draw_bounded (bit : PMF Bool) (bound fuel : Bits)
    {out : Option (Output bound) × ℕ}
    (hout : out ∈ (checkedDrawCharged bit bound fuel).support) :
    out.2 ≤ checkedInstructionBound bound fuel ∧
      ∀ r, out.1=some r → Bounded bound fuel r := by
  have hz := isZero_spec bound
  rw [checkedDrawCharged] at hout
  split at hout
  next hzero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    constructor
    · dsimp only [checkedInstructionBound]
      omega
    · intro r hr
      cases hr
  next hpositive =>
    obtain ⟨r,hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    have h := draw_bounded bit bound fuel _ hr
    constructor
    · dsimp only [checkedInstructionBound]
      have hc := h.2.2
      omega
    · intro s hs
      cases hs
      exact h

end
end DirectedFlowCutGap.BinarySamplerCost
