import DirectedFlowCutGap.BinaryRetainedTape

/-!
# Summed charge of the actual retained binary tape callback

Every execution premise below is support membership in the existing concrete
PMF program. The induction follows its actual retained-list loops and its same
physical ledger. In particular, input padding is retained, each local draw is
charged once, and the callback returns its fresh subtotal rather than a prior
cumulative charge. No exact ideal sampling law is assumed.

These are summed charges in the adapter's declared model. Active enumeration,
the native index conversion and the structural representation simulation still
have the obligations documented by BinaryRetainedTape. A controller-wide
reached-ledger bound and the stateful finite-bit-source lifting are separate;
this component alone does not discharge the controller's uniform hK premise.
-/
namespace DirectedFlowCutGap.BinaryRetainedTapeCost
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape RetainedGridState

set_option backward.isDefEq.respectTransparency false

def delta (B : ℕ) (fuel : Bits) : ℕ := value fuel+B+2

/-- A common allowance for one reached draw, its index conversion, and the
larger permutation predecessor/constructor branch. -/
def stepBound (S Q B : ℕ) (fuel : Bits) : ℕ :=
  2048*(value fuel+1)*(value fuel+B+fuel.length+2)^2+
    40*(S+(Q+1)*delta B fuel)+80*(B+1)

def drawBudget (n : ℕ) : ℕ := 2*(n*n)

/-- Includes the actual supplied cutoff padding. -/
def boundWidth (n : ℕ) (cutoff : Bits) : ℕ := max (n*n) cutoff.length

def callbackBound (n : ℕ) (fuel cutoff : Bits) (S : ℕ) : ℕ :=
  48*(n*n+1)^2+48+
    drawBudget n*stepBound S (drawBudget n) (boundWidth n cutoff) fuel

@[simp] theorem width_charge (k : ℕ) (s : Ledger) :
    ledgerWidth (charge k s)=ledgerWidth s := rfl

@[simp] theorem operations_charge (k : ℕ) (s : Ledger) :
    (charge k s).operations=s.operations+k := rfl

@[simp] theorem width_reset (s : Ledger) (k : ℕ) :
    ledgerWidth {s with operations := k}=ledgerWidth s := rfl

private theorem instruction_le (bound fuel : Bits) (B : ℕ)
    (hb : bound.length ≤ B) :
    BinarySamplerCost.instructionBound bound fuel ≤
      2048*(value fuel+1)*(value fuel+B+fuel.length+2)^2 := by
  unfold BinarySamplerCost.instructionBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-- The metadata allowance is evaluated on the reached stored lengths. The
extra delta in the common width also pays the adders' one-bit extensions. -/
theorem updateBound_le (s : Ledger) (bound fuel : Bits) (S Q B q : ℕ)
    (hb : bound.length ≤ B) (hq : q ≤ Q)
    (hs : ledgerWidth s ≤ S+q*delta B fuel) :
    updateBound s bound fuel ≤
      2048*(value fuel+1)*(value fuel+B+fuel.length+2)^2+
        40*(S+(Q+1)*delta B fuel)+20 := by
  have hi := instruction_le bound fuel B hb
  have hqmul := Nat.mul_le_mul_right (delta B fuel) hq
  have ht : s.trials.length ≤ ledgerWidth s := le_max_left _ _
  have hc : s.consumed.length ≤ ledgerWidth s :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hd : s.draws.length ≤ ledgerWidth s :=
    (le_max_right _ _).trans (le_max_right _ _)
  have ht' : max s.trials.length (value fuel)+1 ≤
      S+(Q+1)*delta B fuel := by
    rw [Nat.add_mul,one_mul]
    unfold delta at hs hqmul ⊢
    omega
  have hc' : max s.consumed.length (value fuel+bound.length+1)+1 ≤
      S+(Q+1)*delta B fuel := by
    rw [Nat.add_mul,one_mul]
    unfold delta at hs hqmul ⊢
    omega
  have hd' : s.draws.length+1 ≤ S+(Q+1)*delta B fuel := by
    rw [Nat.add_mul,one_mul]
    unfold delta at hs hqmul ⊢
    omega
  unfold updateBound
  omega

noncomputable section

/-- The actual local width and charge bound, at any supported reached draw.
The remaining 32(B+1)+16 pays predecessor and both loop constructors. -/
theorem drawIndex_bounds (bit : PMF Bool) (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) (S Q B q : ℕ)
    (hbound : bound.length ≤ B) (hq : q ≤ Q)
    (hs : ledgerWidth s ≤ S+q*delta B fuel) {out : Fin N × Ledger}
    (hout : out ∈ (drawIndex bit fuel bound hb hN s).support) :
    ledgerWidth out.2 ≤ S+(q+1)*delta B fuel ∧
      out.2.operations+32*(B+1)+16 ≤ s.operations+stepBound S Q B fuel := by
  have hw := drawIndex_width bit fuel bound hb hN s hout
  have hc := drawIndex_charge bit fuel bound hb hN s hout
  have hu := updateBound_le s bound fuel S Q B q hbound hq hs
  refine ⟨?_,?_⟩
  · rw [Nat.add_mul,one_mul]
    unfold delta at hs ⊢
    omega
  · unfold stepBound
    omega

/-- List-prefix invariant for the shrinking permutation bounds. No callback
work is replaced by a generic allowance: drawIndex_bounds is applied to each
actual supported draw and predecessor_length to its actual retained word. -/
theorem permutation_bounds (bit : PMF Bool) (fuel : Bits) {A : Type}
    (xs : List A) (bound : Bits) (hb : value bound=xs.length)
    (S Q B q : ℕ) (s : Ledger) (hbound : bound.length ≤ B)
    (hq : q+xs.length ≤ Q) (hs : ledgerWidth s ≤ S+q*delta B fuel)
    {out : FinitePermutationSampler.Tape xs.length × Ledger}
    (hout : out ∈ (permutation bit fuel xs bound hb s).support) :
    ledgerWidth out.2 ≤ S+(q+xs.length)*delta B fuel ∧
      out.2.operations ≤ s.operations+xs.length*stepBound S Q B fuel+4 := by
  induction xs generalizing bound q s with
  | nil =>
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      simpa only [List.length_nil,Nat.add_zero,zero_mul,width_charge,
        operations_charge] using And.intro hs (Nat.le_refl (s.operations+4))
  | cons x xs ih =>
      rw [permutation] at hout
      obtain ⟨j,hj,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨t,ht,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      have hfirst := drawIndex_bounds bit fuel bound hb (by simp) s S Q B q
        hbound (by simp only [List.length_cons] at hq; omega) hs hj
      have hp := (BinarySamplerCost.predecessor_length bound).trans hbound
      have hquota : q+1+xs.length ≤ Q := by
        simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq
      have hwidth : ledgerWidth (charge ((predecessor bound).2+8) j.2) ≤
          S+(q+1)*delta B fuel := by simpa only [width_charge] using hfirst.1
      have htail := ih (bound := (predecessor bound).1)
        (hb := by rw [(predecessor_spec bound).1,hb]; simp)
        (q := q+1) (s := charge ((predecessor bound).2+8) j.2)
        hp hquota hwidth ht
      have hpred : (predecessor bound).2 ≤ 32*(B+1) :=
        (predecessor_spec bound).2.2.trans (Nat.mul_le_mul_left 32 (by omega))
      refine ⟨?_,?_⟩
      · simpa only [width_charge,List.length_cons,Nat.add_assoc,Nat.add_comm,
          Nat.add_left_comm] using htail.1
      · simp only [operations_charge] at htail ⊢
        rw [List.length_cons,Nat.add_mul,one_mul]
        omega

/-- The same prefix invariant for the fixed-cutoff cell loop. -/
theorem cells_bounds (bit : PMF Bool) (fuel cutoff : Bits) {L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) {A : Type} (xs : List A)
    (S Q B q : ℕ) (s : Ledger) (hbound : cutoff.length ≤ B)
    (hq : q+xs.length ≤ Q) (hs : ledgerWidth s ≤ S+q*delta B fuel)
    {out : FiniteGridSampler.Cells L xs.length × Ledger}
    (hout : out ∈ (cells bit fuel cutoff hcut hL xs s).support) :
    ledgerWidth out.2 ≤ S+(q+xs.length)*delta B fuel ∧
      out.2.operations ≤ s.operations+xs.length*stepBound S Q B fuel+4 := by
  induction xs generalizing q s with
  | nil =>
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      simpa only [List.length_nil,Nat.add_zero,zero_mul,width_charge,
        operations_charge] using And.intro hs (Nat.le_refl (s.operations+4))
  | cons x xs ih =>
      rw [cells] at hout
      obtain ⟨j,hj,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨t,ht,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      have hfirst := drawIndex_bounds bit fuel cutoff hcut hL s S Q B q
        hbound (by simp only [List.length_cons] at hq; omega) hs hj
      have hquota : q+1+xs.length ≤ Q := by
        simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq
      have htail := ih (q := q+1) (s := j.2) hquota hfirst.1 ht
      refine ⟨?_,?_⟩
      · simpa only [width_charge,List.length_cons,Nat.add_assoc,Nat.add_comm,
          Nat.add_left_comm] using htail.1
      · simp only [operations_charge]
        rw [List.length_cons,Nat.add_mul,one_mul]
        omega

/-- Sequential composition uses the reached permutation ledger as the cell
loop's entering ledger. Both loops share the same common allowance. -/
theorem tape_bounds (bit : PMF Bool) (fuel cutoff : Bits) {L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) {A : Type}
    (xs : List A) (bound : Bits) (hb : value bound=xs.length)
    (S Q B q : ℕ) (s : Ledger) (hbound : bound.length ≤ B)
    (hcutlen : cutoff.length ≤ B) (hq : q+2*xs.length ≤ Q)
    (hs : ledgerWidth s ≤ S+q*delta B fuel)
    {out : (FinitePermutationSampler.Tape xs.length × FiniteGridSampler.Cells L xs.length) × Ledger}
    (hout : out ∈ (tape bit fuel cutoff hcut hL xs bound hb s).support) :
    ledgerWidth out.2 ≤ S+(q+2*xs.length)*delta B fuel ∧
      out.2.operations ≤ s.operations+2*xs.length*stepBound S Q B fuel+16 := by
  rw [tape] at hout
  obtain ⟨p,hp,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨c,hc,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  have hp' := permutation_bounds bit fuel xs bound hb S Q B q s hbound
    (by omega) hs hp
  have hc' := cells_bounds bit fuel cutoff hcut hL xs S Q B (q+xs.length) p.2
    hcutlen (by omega) hp'.1 hc
  refine ⟨?_,?_⟩
  · simp only [width_charge]
    have hsum : q+2*xs.length=q+xs.length+xs.length := by omega
    rw [hsum]
    exact hc'.1
  · simp only [operations_charge]
    have heq : 2*xs.length*stepBound S Q B fuel =
        xs.length*stepBound S Q B fuel+xs.length*stepBound S Q B fuel := by ring
    rw [heq]
    omega

/-- The actual active dictionary/count setup is included. In particular,
materializing the tape later does not make this scan free. -/
theorem sampleTape_bounds (bit : PMF Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger)
    (S : ℕ) (hs : ledgerWidth s ≤ S)
    {out : RetainedTapeInput.Tape L a × Ledger}
    (hout : out ∈ (sampleTape bit fuel cutoff hcut hL a s).support) :
    ledgerWidth out.2 ≤ S+drawBudget n*delta (boundWidth n cutoff) fuel ∧
      out.2.operations ≤ s.operations+48*(n*n+1)^2+40+
        drawBudget n*stepBound S (drawBudget n) (boundWidth n cutoff) fuel := by
  rw [sampleTape] at hout
  obtain ⟨r,hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  have hm : (RetainedTapeInput.activeList a).length ≤ n*n := by
    rw [RetainedTapeInput.activeList_length]
    exact RetainedDrawTrees.active_card_le a
  have hb : (count (RetainedTapeInput.activeList a)).1.length ≤ boundWidth n cutoff :=
    (count_spec _).2.1.trans (hm.trans (le_max_left _ _))
  have hq : 2*(RetainedTapeInput.activeList a).length ≤ drawBudget n :=
    Nat.mul_le_mul_left 2 hm
  have ht := tape_bounds bit fuel cutoff hcut hL (RetainedTapeInput.activeList a)
    (count (RetainedTapeInput.activeList a)).1 (count_spec _).1
    S (drawBudget n) (boundWidth n cutoff) 0
    (charge (EncodedTapeMaterialization.dictionaryBound n+
      (count (RetainedTapeInput.activeList a)).2+16) s)
    hb (le_max_right _ _) (by simpa only [Nat.zero_add] using hq)
    (by simpa only [width_charge,zero_mul,Nat.add_zero] using hs) hr
  have hwidth := Nat.mul_le_mul_right (delta (boundWidth n cutoff) fuel) hq
  have hwork := Nat.mul_le_mul_right
    (stepBound S (drawBudget n) (boundWidth n cutoff) fuel) hq
  have hsetup := setup_bound a
  simp only [Nat.zero_add,operations_charge] at ht
  simp only [width_charge,operations_charge]
  exact ⟨by omega,by omega⟩

/-- The supported actual callback returns this incremental charge. The cost
depends on entering physical padding via S, never entering cumulative work. -/
theorem callback_bounds (bit : PMF Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger)
    (S : ℕ) (hs : ledgerWidth s ≤ S)
    {out : (RetainedTapeInput.Tape L a × ℕ) × Ledger}
    (hout : out ∈ ((callback bit fuel cutoff hcut hL a).run s).support) :
    ledgerWidth out.2 ≤ S+drawBudget n*delta (boundWidth n cutoff) fuel ∧
      out.1.2 ≤ callbackBound n fuel cutoff S ∧
      out.2.operations=s.operations+out.1.2 ∧
      value out.2.draws=value s.draws+2*Fintype.card ↥(remainingSet a) ∧
      value out.2.draws ≤ value s.draws+drawBudget n := by
  have hinc := callback_increment bit fuel cutoff hcut hL a s hout
  have hdraw := callback_draw_bound bit fuel cutoff hcut hL a s hout
  change out ∈ (sampleTape bit fuel cutoff hcut hL a {s with operations := 0} >>= _).support at hout
  obtain ⟨r,hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  have h := sampleTape_bounds bit fuel cutoff hcut hL a {s with operations := 0}
    S (by simpa only [width_reset] using hs) hr
  refine ⟨?_,?_,hinc.1,hinc.2,?_⟩
  · simpa only [width_reset] using h.1
  · have hc : r.2.operations ≤ 48*(n*n+1)^2+40+
        drawBudget n*stepBound S (drawBudget n) (boundWidth n cutoff) fuel := by
      simpa only [Nat.zero_add] using h.2
    change r.2.operations+8 ≤ callbackBound n fuel cutoff S
    unfold callbackBound
    omega
  · simpa only [drawBudget,Nat.mul_assoc] using hdraw

/-- No initial-ledger restriction: arbitrary incoming stored padding is
included in the concrete bound. This is the direct one-call specialization. -/
theorem callback_charge (bit : PMF Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger)
    {out : (RetainedTapeInput.Tape L a × ℕ) × Ledger}
    (hout : out ∈ ((callback bit fuel cutoff hcut hL a).run s).support) :
    out.1.2 ≤ callbackBound n fuel cutoff (ledgerWidth s) :=
  (callback_bounds bit fuel cutoff hcut hL a s (ledgerWidth s) le_rfl hout).2.1

end
end DirectedFlowCutGap.BinaryRetainedTapeCost
