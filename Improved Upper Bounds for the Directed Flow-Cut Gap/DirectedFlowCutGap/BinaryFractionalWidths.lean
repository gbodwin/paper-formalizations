import DirectedFlowCutGap.BinaryFractionalCanonical

/-!
# Actual stored widths along the binary covering execution

These bounds concern the Boolean lists in the retained state, including input
padding. They use the exact raw-state refinement and the independently proved
unreduced raw-field bounds. Canonicality is proved for computed state fields;
it is not assumed of the input. Oracle execution charges and physical heap
addresses are separate obligations.
-/
namespace DirectedFlowCutGap.BinaryFractionalWidths
open BinaryRational BinaryFractionalRows BinaryFractionalCore BinaryFractionalCanonical

variable {m : ℕ}

def RowStored (y : Row m) (B : ℕ) : Prop := ∀ i, StoredBounded (get y i) B

theorem rowStored_mono {y : Row m} {A B : ℕ} (h : RowStored y A) (hab : A ≤ B) :
    RowStored y B := fun i => ⟨(h i).1.trans hab,(h i).2.trans hab⟩

theorem row_raw {y : Row m} {B : ℕ} (hy : RowStored y B) :
    FractionalCoverRawCore.RowBounded (decodeRow y) B := by
  intro i
  rw [decode_get]
  exact stored_raw_bound (hy i)

structure StateStored (s : State m) (B : ℕ) : Prop where
  weights : RowStored s.weights B
  best : RowStored s.best B
  bestCost : StoredBounded s.bestCost B
  total : StoredBounded s.total B
  loads : RowStored s.loads B

/-- A single polynomial envelope for every computed field after `k` scans.
`Nat.size m` is bounded by `m`, so the displayed envelope is polynomial in the
resource dimension and the supplied maximum input length. -/
def stateWidth (m B k : ℕ) : ℕ :=
  (m+1)^2*(B+2*m+4+k*(2*B+2))+k*(B+1)+B+2

theorem stateWidth_mono (m B : ℕ) {k t : ℕ} (h : k ≤ t) :
    stateWidth m B k ≤ stateWidth m B t := by
  unfold stateWidth
  gcongr

theorem width_bounds (m B k : ℕ) :
    FractionalCoverRawCore.weightWidth m B k+1 ≤ stateWidth m B k ∧
    FractionalCoverRawCore.normalWidth m
      (FractionalCoverRawCore.weightWidth m B k)+1 ≤ stateWidth m B k ∧
    m*(B+FractionalCoverRawCore.normalWidth m
      (FractionalCoverRawCore.weightWidth m B k)+1)+1 ≤ stateWidth m B k ∧
    k*(B+1)+1 ≤ stateWidth m B k ∧ B ≤ stateWidth m B k := by
  have hsize : Nat.size m ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  let A := B+2*m+4+k*(2*B+2)
  have hw : FractionalCoverRawCore.weightWidth m B k+1 ≤ A := by
    unfold FractionalCoverRawCore.weightWidth FractionalCoverRawCore.initialWidth
      FractionalCoverRawCore.factorWidth
    dsimp [A]
    omega
  have hBA : B ≤ A := by dsimp [A];omega
  have hfactor : 1 ≤ (m+1)^2 := Nat.one_le_pow 2 (m+1) (Nat.succ_pos m)
  have hfactor' : m+1 ≤ (m+1)^2 := Nat.le_self_pow (by decide) _
  have hA : A ≤ (m+1)^2*A := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right A hfactor
  have hA' : (m+1)*A ≤ (m+1)^2*A := Nat.mul_le_mul_right A hfactor'
  have hsuper : (m+1)^2*A+1 ≤ stateWidth m B k := by
    dsimp [stateWidth,A]
    omega
  have hnormal : FractionalCoverRawCore.normalWidth m
      (FractionalCoverRawCore.weightWidth m B k)+1 ≤ (m+1)*A := by
    calc
      _ = (m+1)*(FractionalCoverRawCore.weightWidth m B k+1) := by
        unfold FractionalCoverRawCore.normalWidth
        ring
      _ ≤ _ := Nat.mul_le_mul_left (m+1) hw
  have hcost : m*(B+FractionalCoverRawCore.normalWidth m
      (FractionalCoverRawCore.weightWidth m B k)+1)+1 ≤ (m+1)^2*A+1 := by
    calc
      _ = m*(B+(FractionalCoverRawCore.normalWidth m
          (FractionalCoverRawCore.weightWidth m B k)+1))+1 := by ring
      _ ≤ m*(A+(m+1)*A)+1 := by gcongr
      _ = (m*(m+2))*A+1 := by ring
      _ ≤ _ := Nat.add_le_add_right
        (Nat.mul_le_mul_right A (by nlinarith : m*(m+2) ≤ (m+1)^2)) 1
  refine ⟨hw.trans (hA.trans ((Nat.le_succ _).trans hsuper)),
    hnormal.trans (hA'.trans ((Nat.le_succ _).trans hsuper)),hcost.trans hsuper,?_,
    hBA.trans (hA.trans ((Nat.le_succ _).trans hsuper))⟩
  unfold stateWidth
  omega

theorem state_stored_of_raw (c : Row m) (r : FractionalCoverRawCore.RawOracle m)
    (s : State m) (B k : ℕ) (hc : RowStored c B) (hs : StateCanonical s)
    (hr : decodeState s = FractionalCoverRawCore.run (decodeRow c) r k) :
    StateStored s (stateWidth m B k) := by
  have hraw := row_raw hc
  have hw := width_bounds m B k
  have hew := congrArg FractionalCoverRawCore.RawState.weights hr
  have heb := congrArg FractionalCoverRawCore.RawState.best hr
  have hed := congrArg FractionalCoverRawCore.RawState.bestCost hr
  have het := congrArg FractionalCoverRawCore.RawState.total hr
  have hel := congrArg FractionalCoverRawCore.RawState.loads hr
  change decodeRow s.weights = _ at hew
  change decodeRow s.best = _ at heb
  change decode s.bestCost = _ at hed
  change decode s.total = _ at het
  change decodeRow s.loads = _ at hel
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := FractionalCoverRawCore.run_weights_bounded hraw r k
    rw [← hew] at h
    apply rowStored_mono (B := stateWidth m B k) _ hw.1
    intro i
    apply stored_of_raw (hs.weights i)
    simpa only [decode_get] using h i
  · have h := FractionalCoverRawCore.run_best_bounded hraw r k
    rw [← heb] at h
    apply rowStored_mono (B := stateWidth m B k) _ hw.2.1
    intro i
    apply stored_of_raw (hs.best i)
    simpa only [decode_get] using h i
  · have h := FractionalCoverRawCore.run_bestCost_bounded hraw r k
    rw [← hed] at h
    have hb := stored_of_raw hs.bestCost h
    exact ⟨hb.1.trans hw.2.2.1,hb.2.trans hw.2.2.1⟩
  · have h := FractionalCoverRawCore.run_total_bounded hraw r k
    rw [← het] at h
    have hb := stored_of_raw hs.total h
    exact ⟨hb.1.trans hw.2.2.2.1,hb.2.trans hw.2.2.2.1⟩
  · have h := FractionalCoverRawCore.run_loads_bounded hraw r k
    rw [← hel] at h
    apply rowStored_mono (B := stateWidth m B k) _ hw.2.2.2.1
    intro i
    apply stored_of_raw (hs.loads i)
    simpa only [decode_get] using h i

theorem run_stored (c : Row m) (delta : Fraction) (b : Oracle m)
    (r : FractionalCoverRawCore.RawOracle m) (ho : Refines b r)
    (hd : decode delta = FractionalCoverRawCore.deltaCode m)
    (fuel : BinaryArithmetic.Bits) (B : ℕ) (hc : RowStored c B) :
    StateStored (run c delta b fuel).state
      (stateWidth m B (BinaryArithmetic.value fuel)) :=
  state_stored_of_raw c r _ B _ hc (run_canonical c delta b fuel)
    (run_refines c delta b r ho hd fuel).1

theorem solveInput_stored (c : Row m) (b : Oracle m)
    (r : FractionalCoverRawCore.RawOracle m) (ho : Refines b r)
    (B : ℕ) (hc : RowStored c B) :
    StateStored (solveInput c b).state (stateWidth m B (3*m^2)) :=
  state_stored_of_raw c r _ B _ hc (solveInput_canonical c b)
    (solveInput_refines c b r ho).1

/-- Event amounts are references to supplied cost fields, including their
accepted padding. They are not covered by the computed-field canonicality. -/
def EventInputs (c : Row m) (s : State m) : Prop :=
  ∀ e ∈ s.events, ∃ i : Fin m, e.amount=get c i

theorem start_event_inputs (c : Row m) (delta : Fraction) (b : Oracle m) :
    EventInputs c (start c delta b).1 := by
  simp [EventInputs,start]

theorem step_events (c : Row m) (b : Oracle m) (s : State m) (h : EventInputs c s) :
    EventInputs c (step c b s).1 ∧
      (step c b s).1.events.length ≤ s.events.length+1 := by
  unfold step
  dsimp only
  split
  · exact ⟨h,Nat.le_succ _⟩
  · constructor
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨(b s.weights).1.bottleneck,rfl⟩
      · exact h e he
    · simp only [List.length_cons]
      rfl

theorem runFrom_events (c : Row m) (b : Oracle m) (fuel : BinaryArithmetic.Bits)
    (s : State m) (hs : EventInputs c s) :
    EventInputs c (runFrom c b fuel s).state ∧
      (runFrom c b fuel s).state.events.length ≤ s.events.length+BinaryArithmetic.value fuel := by
  have aux : ∀ k, ∀ f : BinaryArithmetic.Bits, BinaryArithmetic.value f=k →
      ∀ s : State m, EventInputs c s →
      EventInputs c (runFrom c b f s).state ∧
        (runFrom c b f s).state.events.length ≤ s.events.length+BinaryArithmetic.value f := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro f hf s hinput
      rw [runFrom]
      split_ifs with hz
      · have hv := (BinaryArithmetic.isZero_spec f).1.mp hz
        exact ⟨hinput,by simp only [hv,Nat.add_zero];rfl⟩
      · have hv : 0<BinaryArithmetic.value f := Nat.pos_of_ne_zero
          (fun he => hz ((BinaryArithmetic.isZero_spec f).1.mpr he))
        have hp := BinaryArithmetic.predecessor_spec f
        have hstep := step_events c b s hinput
        have hh := ih _ (by rw [hp.1,← hf];omega) _ rfl _ hstep.1
        refine ⟨hh.1,?_⟩
        dsimp only
        rw [hp.1] at hh
        omega
  exact aux _ fuel rfl s hs

theorem solveInput_events (c : Row m) (b : Oracle m) (B : ℕ) (hc : RowStored c B) :
    (solveInput c b).state.events.length ≤ 3*m^2 ∧
      ∀ e ∈ (solveInput c b).state.events, StoredBounded e.amount B := by
  let p := parameters (dimension c).1
  have h := runFrom_events c b p.fuel (start c p.delta b).1 (start_event_inputs c p.delta b)
  have hf := (parameters_spec (dimension c).1).1
  rw [(dimension_spec c).1] at hf
  change BinaryArithmetic.value p.fuel=3*m^2 at hf
  have hzero : (start c p.delta b).1.events.length=0 := rfl
  constructor
  · change (runFrom c b p.fuel (start c p.delta b).1).state.events.length ≤ _
    simpa only [hzero,Nat.zero_add,hf] using h.2
  · intro e he
    obtain ⟨i,hi⟩ := h.1 e he
    rw [hi]
    exact hc i

end DirectedFlowCutGap.BinaryFractionalWidths
