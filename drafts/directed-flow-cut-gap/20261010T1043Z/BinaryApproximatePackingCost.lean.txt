import DirectedFlowCutGap.BinaryApproximatePackingWidths

/-!
# Charges on supported outputs of the actual monadic controller

The theorem concerns PMF support of the displayed wrapper, not arbitrary
InputResult records. Provider operations are retained as an explicit sum and
are bounded only after a concrete provider theorem is supplied. Current stored
widths follow the varying-choice recurrence in the companion module. This is a
charged-body bound; fixed-body implementation substitution and representation
overhead remain separate from these annotations.
-/
namespace DirectedFlowCutGap.BinaryApproximatePackingCost
open BinaryApproximatePacking BinaryApproximatePackingWidths
open BinaryArithmetic BinaryRational BinaryFractionalRows BinaryFractionalWidths
open BinaryFractionalStepCost BinaryFractionalLoopCost BinaryFractionalEntryCost
open EncodedRoundingInput

variable {m : ℕ}

def answersCharge (xs : List (Answer m)) : ℕ := (xs.map Answer.operations).sum

lemma answersCharge_append (xs ys : List (Answer m)) :
    answersCharge (xs++ys)=answersCharge xs+answersCharge ys := by
  simp [answersCharge]

/-- The actual provider's support is retained, including the actual stored query
row and all metadata of its answer. No probability/cost bound is assumed here. -/
def QuerySupported {c : Row m} {columns : Set (FractionalCover.Column m)}
    (draw : Oracle PMF c columns) (S : ℕ) (a : Answer m) : Prop :=
  ∃ y : Row m, RowStored y S ∧ ∃ q ∈ (draw y).support, q.1=a

def guardBound (m S : ℕ) : ℕ :=
  objectiveBound m S+2048*(scalarWidth m S+1)^2+4

lemma guard_charge (c : Row m) (s : State m) (S : ℕ)
    (hc : RowStored c S) (hs : StateStored s S) :
    (guard c s).2 ≤ guardBound m S := by
  have hobj := objective_charge c s.weights S hc hs.weights
  have hstored := objective_stored c s.weights S hc hs.weights
  have hw := scalar_width_bounds m S
  have hone : StoredBounded one (scalarWidth m S) :=
    stored_mono (by simp [StoredBounded,one] : StoredBounded one 1) hw.2.1
  have hle := le_charge hone (stored_mono hstored hw.2.2.1)
  unfold BinaryApproximatePacking.guard guardBound
  dsimp only
  omega

lemma advance_facts {c : Row m} {columns : Set (FractionalCover.Column m)}
    (draw : Oracle PMF c columns) {p : Pending c columns} {s : State m}
    (S : ℕ) (hc : RowStored c S) (hs : StateStored s S)
    {r : Round c columns p s} (hr : r ∈ (advance c columns draw p s).support) :
    r.operations ≤ guardBound m S+stepBound m S 1+8+answersCharge r.answer.toList ∧
      ∀ a ∈ r.answer.toList, QuerySupported draw S a := by
  have hg := guard_charge c s S hc hs
  rw [advance] at hr
  split at hr
  next hstop =>
    have he := (PMF.mem_support_pure_iff _ _).mp hr
    subst r
    constructor
    · dsimp only
      simp only [answersCharge,Option.toList_none,List.map_nil,List.sum_nil]
      omega
    · simp
  next hactive =>
    cases p with
    | some q =>
        have he := (PMF.mem_support_pure_iff _ _).mp hr
        subst r
        have hstep := step_charge c (cached q.1) s S 1 hc hs le_rfl
        constructor
        · dsimp only
          simp only [answersCharge,Option.toList_none,List.map_nil,List.sum_nil]
          omega
        · simp
    | none =>
        obtain ⟨a,ha,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
        have he := (PMF.mem_support_pure_iff _ _).mp hr
        subst r
        have hstep := step_charge c (cached a.1.choice) s S 1 hc hs le_rfl
        constructor
        · dsimp only
          simp only [answersCharge,Option.toList_some,List.map_cons,List.map_nil,
            List.sum_cons,List.sum_nil,Nat.add_zero]
          omega
        · intro b hb
          have he : b=a.1 := by simpa using hb
          subst b
          exact ⟨s.weights,hs.weights,a,ha,rfl⟩

def loopOverhead (m B T F t : ℕ) : ℕ :=
  t*(guardBound m (stateWidth m B T)+stepBound m (stateWidth m B T) 1+
    36*(F+1)+16)+4*(F+1)+4

/-- Exact body support prevents arbitrary operation fields from being smuggled
into a claimed runtime theorem. Bad-cost answers remain included in the sum. -/
theorem runFrom_facts {c : Row m} {columns : Set (FractionalCover.Column m)}
    (draw : Oracle PMF c columns) (B T F : ℕ) (hc : RowStored c B)
    (fuel : Bits) {p : Pending c columns} {s : State m} (k : ℕ)
    (hs : Reached c B k s) (hT : k+value fuel ≤ T) (hF : fuel.length ≤ F)
    {r : RunResult c columns p s (value fuel)}
    (hr : r ∈ (runFromM c columns draw fuel p s).support) :
    r.operations ≤ loopOverhead m B T F (value fuel)+answersCharge r.answers ∧
      ∀ a ∈ r.answers, QuerySupported draw (stateWidth m B T) a := by
  have aux : ∀ t, ∀ f : Bits, value f=t → ∀ p s k,
      Reached c B k s → k+value f ≤ T → f.length ≤ F →
      ∀ r : RunResult c columns p s (value f),
      r ∈ (runFromM c columns draw f p s).support →
      r.operations ≤ loopOverhead m B T F (value f)+answersCharge r.answers ∧
        ∀ a ∈ r.answers, QuerySupported draw (stateWidth m B T) a := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro f hf p s k hs hT hF r hr
      have hz := (isZero_spec f).2
      rw [runFromM] at hr
      split at hr
      next hzero =>
        have he := (PMF.mem_support_pure_iff _ _).mp hr
        subst r
        have hv := (isZero_spec f).1.mp hzero
        constructor
        · dsimp only
          simp only [loopOverhead,hv,zero_mul,zero_add,answersCharge,List.map_nil,List.sum_nil,
            Nat.add_zero]
          nlinarith
        · simp
      next hnonzero =>
        have hv : 0<value f := Nat.pos_of_ne_zero
          (fun h => hnonzero ((isZero_spec f).1.mpr h))
        have hp := predecessor_spec f
        obtain ⟨next,hnext,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
        obtain ⟨tail,htail,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
        have he := (PMF.mem_support_pure_iff _ _).mp hr
        subst r
        have hswide := reached_stored_at hs hc (by omega : k ≤ T)
        have hcwide := rowStored_mono hc (width_bounds m B T).2.2.2.2
        have hn := advance_facts draw (stateWidth m B T) hcwide hswide hnext
        have ht := ih (value (predecessor f).1) (by rw [hp.1,← hf];omega)
          (predecessor f).1 rfl next.pending next.state (k+1)
          (link_reached next.link hc hs) (by rw [hp.1];omega)
          ((predecessor_length f).trans hF) tail htail
        constructor
        · dsimp only
          rw [answersCharge_append]
          have hbody := hn.1
          have htailcost := ht.1
          unfold loopOverhead at htailcost ⊢
          conv at htailcost => rhs; lhs; rw [hp.1]
          have heq : value f=(value f-1)+1 := by omega
          rw [heq,Nat.add_mul]
          nlinarith [hp.2.2]
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hn.2 a ha
          · exact ht.2 a ha
  exact aux _ fuel rfl p s k hs hT hF r hr

def initialBound (m B : ℕ) : ℕ :=
  m*(2048*(B+2*m+5)^2+4)+arrayBound m

def runOverhead (m B T F t : ℕ) : ℕ :=
  initialBound m B+startBound m B T 1+loopOverhead m B T F t+12

lemma initial_charge_input (c : Row m) (delta : Fraction) (B : ℕ)
    (hc : RowStored c B) (hd : StoredBounded delta (2*m+4)) :
    (initial c delta).2 ≤ initialBound m B := by
  have h := initial_charge c delta (B+2*m+4)
    (rowStored_mono hc (by omega)) (stored_mono hd (by omega))
  simpa only [initialBound,show B+2*m+4+1=B+2*m+5 by omega] using h

theorem run_facts {c : Row m} {columns : Set (FractionalCover.Column m)}
    (draw : Oracle PMF c columns) (delta : Fraction) (fuel : Bits)
    (B T F : ℕ) (hc : RowStored c B)
    (hd : decode delta=FractionalCoverRawCore.deltaCode m)
    (hds : StoredBounded delta (2*m+4)) (hT : value fuel ≤ T) (hF : fuel.length ≤ F)
    {r : StartedResult c columns delta fuel}
    (hr : r ∈ (runM c columns draw delta fuel).support) :
    r.operations ≤ runOverhead m B T F (value fuel)+answersCharge r.answers ∧
      ∀ a ∈ r.answers, QuerySupported draw (stateWidth m B T) a := by
  rw [runM] at hr
  obtain ⟨first,hfirst,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨rest,hrest,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  have he := (PMF.mem_support_pure_iff _ _).mp hr
  subst r
  have hs := start_reached c delta first.1.choice B hc hd
  have ht := runFrom_facts draw B T F hc fuel 0 hs (by simpa using hT) hF hrest
  have hi := initial_charge_input c delta B hc hds
  have hj := start_charge c delta (cached first.1.choice)
    (fun _ => BinaryFractionalCore.decodeChoice first.1.choice) (fun _ => rfl)
    hd B T 1 hc hds (fun _ _ => le_rfl)
  constructor
  · dsimp only
    simp only [StartedResult.answers,answersCharge,List.map_cons,List.sum_cons]
    unfold runOverhead
    have htcost := ht.1
    unfold answersCharge at htcost
    omega
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨(initial c delta).1,(reached_stored_at hs hc (Nat.zero_le T)).weights,
        first,hfirst,rfl⟩
    · exact ht.2 a ha

def entryOverhead (m B : ℕ) : ℕ :=
  32*(m+1)^2+parameterBound (m+1)+runOverhead m B (3*m^2) (3*m+9) (3*m^2)+8

/-- Provider charges are left as the sum of precisely the actual retained
answers, including the shared startup answer once. -/
theorem solveInput_facts {c : Row m} {columns : Set (FractionalCover.Column m)}
    (draw : Oracle PMF c columns) (B : ℕ) (hc : RowStored c B)
    {r : InputResult c columns} (hr : r ∈ (solveInputM c columns draw).support) :
    r.operations ≤ entryOverhead m B+answersCharge r.answers ∧
      ∀ a ∈ r.answers, QuerySupported draw (stateWidth m B (3*m^2)) a := by
  let dim := (BinaryFractionalCore.dimension c).1
  let p := BinaryFractionalCore.parameters dim
  have hdim := BinaryFractionalCore.dimension_spec c
  have hp := BinaryFractionalCore.parameters_spec dim
  rw [hdim.1] at hp
  have hlen := (BinaryCounters.lengthBits_spec (c.toList.map (fun _ => false))).2.1
  simp only [List.length_map,Vector.length_toList] at hlen
  have hdimlen : dim.length ≤ m+1 := hlen
  have hpcharge := parameters_charge dim (m+1) hdimlen
  have hdelta := parameters_delta_stored dim hdim.1
  rw [solveInputM] at hr
  obtain ⟨r0,hr0,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  have he := (PMF.mem_support_pure_iff _ _).mp hr
  subst r
  have hrun := run_facts draw p.delta p.fuel B (3*m^2) (3*m+9) hc hp.2 hdelta
    (by simpa only [FractionalCover.fuel] using hp.1.le) (by dsimp [p];omega) hr0
  have hf : value p.fuel=3*m^2 := hp.1
  rw [hf] at hrun
  constructor
  · change (BinaryFractionalCore.dimension c).2+
        (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).operations+
        r0.operations+8 ≤ entryOverhead m B+answersCharge r0.answers
    unfold entryOverhead
    have hpc :
        (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).operations ≤
          parameterBound (m+1) := hpcharge.1
    omega
  · exact hrun.2

lemma answersCharge_le {c : Row m} {columns : Set (FractionalCover.Column m)}
    (draw : Oracle PMF c columns) (xs : List (Answer m)) (S R : ℕ)
    (hs : ∀ a ∈ xs, QuerySupported draw S a)
    (hR : ∀ y, RowStored y S → ∀ a ∈ (draw y).support, a.1.operations ≤ R) :
    answersCharge xs ≤ xs.length*R := by
  induction xs with
  | nil => simp [answersCharge]
  | cons a xs ih =>
      obtain ⟨y,hy,q,hq,he⟩ := hs a List.mem_cons_self
      have ha := hR y hy q hq
      rw [he] at ha
      have ht := ih (fun b hb => hs b (List.mem_cons_of_mem a hb))
      simp only [answersCharge,List.map_cons,List.sum_cons,List.length_cons]
      unfold answersCharge at ht
      nlinarith

/-- This corollary requires a concrete all-branch provider bound on every
actually reachable stored query, including failed/fallback answers. -/
theorem solveInput_charge {c : Row m} {columns : Set (FractionalCover.Column m)}
    (draw : Oracle PMF c columns) (B R : ℕ) (hc : RowStored c B)
    (hR : ∀ y, RowStored y (stateWidth m B (3*m^2)) →
      ∀ a ∈ (draw y).support, a.1.operations ≤ R)
    (hm : 0 < m) (hpos : ∀ i, 0 < FractionalCover.value (capacities c) i)
    {r : InputResult c columns} (hr : r ∈ (solveInputM c columns draw).support) :
    r.operations ≤ entryOverhead m B+(3*m^2)*R := by
  have h := solveInput_facts draw B hc hr
  have hcq := answersCharge_le draw r.answers _ R h.2 hR
  have hcount := (r.events B hc).1
  rw [← r.calls_eq_events hm hpos] at hcount
  exact h.1.trans (Nat.add_le_add_left
    (hcq.trans (Nat.mul_le_mul_right R hcount)) _)

end DirectedFlowCutGap.BinaryApproximatePackingCost
