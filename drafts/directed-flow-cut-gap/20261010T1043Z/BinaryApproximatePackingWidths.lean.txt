import DirectedFlowCutGap.BinaryApproximatePacking
import DirectedFlowCutGap.BinaryFractionalEntryCost

/-!
# Stored widths along arbitrary reached packing choices

The induction is local to each actual step. No fixed raw oracle, minimum-column
selection, alpha budget, or supplied final-field bound is assumed. Every newly
computed field retains canonical binary length; event fields are handled by the
separate original-input invariant in BinaryApproximatePackingZeros.
-/
namespace DirectedFlowCutGap.BinaryApproximatePackingWidths
variable {m : ℕ}

namespace Raw
open FractionalCoverRawCore RawNonnegativeRational

structure Bounds (c : RawRow m) (B k : ℕ) (s : RawState m) : Prop where
  weights : RowBounded s.weights (weightWidth m B k)
  best : RowBounded s.best (normalWidth m (weightWidth m B k))
  bestCost_eq : s.bestCost=objectiveCode c s.best
  total : s.total.Bounded (k*(B+1))
  loads : RowBounded s.loads (k*(B+1))

lemma weight_mono (B : ℕ) {k t : ℕ} (h : k ≤ t) : weightWidth m B k ≤ weightWidth m B t := by
  unfold weightWidth
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (factorWidth B) h) _

lemma Bounds.mono {c : RawRow m} {B k t : ℕ} {s : RawState m}
    (h : Bounds c B k s) (hkt : k ≤ t) : Bounds c B t s := by
  exact ⟨rowBounded_mono h.weights (weight_mono B hkt),
    rowBounded_mono h.best (normalWidth_mono (weight_mono B hkt)),h.bestCost_eq,
    Code.bounded_mono h.total (Nat.mul_le_mul_right (B+1) hkt),
    rowBounded_mono h.loads (Nat.mul_le_mul_right (B+1) hkt)⟩

lemma start_bounds {c : RawRow m} {B : ℕ} (hc : RowBounded c B) (r : RawOracle m) :
    Bounds c B 0 (start c r) := by
  exact ⟨run_weights_bounded hc r 0,run_best_bounded hc r 0,
    run_bestCost_eq c r 0,run_total_bounded hc r 0,run_loads_bounded hc r 0⟩

lemma step_bounds {c : RawRow m} {B k : ℕ} (hc : RowBounded c B)
    (r : RawOracle m) {s : RawState m} (hs : Bounds c B k s) :
    Bounds c B (k+1) (step c r s) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := step_weights_bounded r s hc hs.weights
    simpa only [weightWidth,Nat.succ_mul,Nat.add_assoc] using h
  · exact rowBounded_mono (step_best_bounded c r s hs.weights hs.best)
      (normalWidth_mono (weight_mono B (Nat.le_succ k)))
  · simp only [step]
    split
    · exact hs.bestCost_eq
    · dsimp only
      split
      · rfl
      · exact hs.bestCost_eq
  · simp only [step]
    split
    · exact Code.bounded_mono hs.total (Nat.mul_le_mul_right (B+1) (Nat.le_succ k))
    · dsimp only
      have h := Code.bounded_add hs.total (hc (r s.weights).bottleneck)
      simpa only [show k*(B+1)+B+1=(k+1)*(B+1) by ring] using h
  · intro i
    simp only [step]
    split
    · exact Code.bounded_mono (hs.loads i) (Nat.mul_le_mul_right (B+1) (Nat.le_succ k))
    · dsimp only
      simp only [get_ofFn]
      have hterm : (if i ∈ (r s.weights).column then get c (r s.weights).bottleneck
          else Code.zero).Bounded B := by
        split_ifs
        · exact hc _
        · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le B)
      have h := Code.bounded_add (hs.loads i) hterm
      simpa only [show k*(B+1)+B+1=(k+1)*(B+1) by ring] using h

end Raw

open BinaryApproximatePacking BinaryFractionalRows BinaryRational
open BinaryFractionalCanonical BinaryFractionalWidths BinaryFractionalStepCost

/-- Bounds the actual unreduced state together with its stored canonicality. -/
structure Reached (c : Row m) (B k : ℕ) (s : State m) : Prop where
  canonical : StateCanonical s
  raw : Raw.Bounds (decodeRow c) B k (BinaryFractionalCore.decodeState s)

lemma Reached.mono {c : Row m} {B k t : ℕ} {s : State m}
    (h : Reached c B k s) (hkt : k ≤ t) : Reached c B t s :=
  ⟨h.canonical,h.raw.mono hkt⟩

lemma start_reached (c : Row m) (delta : Fraction) (q : Choice m) (B : ℕ)
    (hc : RowStored c B) (hd : decode delta=FractionalCoverRawCore.deltaCode m) :
    Reached c B 0 (BinaryFractionalCore.start c delta (cached q)).1 := by
  refine ⟨start_canonical c delta (cached q),?_⟩
  rw [BinaryFractionalCore.start_refines c delta (cached q)
    (fun _ => BinaryFractionalCore.decodeChoice q) (fun _ => rfl) hd]
  exact Raw.start_bounds (row_raw hc) _

lemma cached_step_reached {c : Row m} {B k : ℕ} {s : State m}
    (q : Choice m) (hc : RowStored c B) (hs : Reached c B k s) :
    Reached c B (k+1) (BinaryFractionalCore.step c (cached q) s).1 := by
  refine ⟨step_canonical c (cached q) s hs.canonical,?_⟩
  rw [BinaryFractionalCore.step_refines c (cached q)
    (fun _ => BinaryFractionalCore.decodeChoice q) (fun _ => rfl) s]
  exact Raw.step_bounds (row_raw hc) _ hs.raw

lemma link_reached {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {a : Option (Answer m)}
    (h : Link c columns p s p' t a) {B k : ℕ} (hc : RowStored c B)
    (hs : Reached c B k s) : Reached c B (k+1) t := by
  cases h with
  | stopped => exact hs.mono (Nat.le_succ k)
  | cached q s h => exact cached_step_reached q.1 hc hs
  | fresh a s h => exact cached_step_reached a.1.choice hc hs

lemma trace_reached {c : Row m} {columns : Set (FractionalCover.Column m)}
    {p p' : Pending c columns} {s t : State m} {a : List (Answer m)} {n : ℕ}
    (h : Trace c columns n p s p' t a) {B k : ℕ} (hc : RowStored c B)
    (hs : Reached c B k s) : Reached c B (k+n) t := by
  induction h generalizing k with
  | zero => simpa using hs
  | succ head tail ih =>
      have hh := ih (link_reached head hc hs)
      simpa only [Nat.add_assoc,Nat.add_comm 1] using hh

/-- Computed field lengths follow the actual reached recurrence; they are not
assumptions about a conveniently re-encoded final mathematical solution. -/
theorem Reached.stored {c : Row m} {B k : ℕ} {s : State m}
    (h : Reached c B k s) (hc : RowStored c B) :
    StateStored s (stateWidth m B k) := by
  have hw := width_bounds m B k
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply rowStored_mono (B := stateWidth m B k) _ hw.1
    intro i
    apply stored_of_raw (h.canonical.weights i)
    simpa only [BinaryFractionalCore.decodeState,decode_get] using h.raw.weights i
  · apply rowStored_mono (B := stateWidth m B k) _ hw.2.1
    intro i
    apply stored_of_raw (h.canonical.best i)
    simpa only [BinaryFractionalCore.decodeState,decode_get] using h.raw.best i
  · have hr := h.raw.bestCost_eq
    have hb := FractionalCoverRawCore.objectiveCode_bounded (row_raw hc) h.raw.best
    rw [← hr] at hb
    have hs := stored_of_raw h.canonical.bestCost hb
    exact ⟨hs.1.trans hw.2.2.1,hs.2.trans hw.2.2.1⟩
  · have hs := stored_of_raw h.canonical.total h.raw.total
    exact ⟨hs.1.trans hw.2.2.2.1,hs.2.trans hw.2.2.2.1⟩
  · apply rowStored_mono (B := stateWidth m B k) _ hw.2.2.2.1
    intro i
    apply stored_of_raw (h.canonical.loads i)
    simpa only [BinaryFractionalCore.decodeState,decode_get] using h.raw.loads i

lemma reached_stored_at {c : Row m} {B k T : ℕ} {s : State m}
    (hs : Reached c B k s) (hc : RowStored c B) (hk : k ≤ T) :
    StateStored s (stateWidth m B T) := (hs.mono hk).stored hc

lemma input_reached {c : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult c columns) (B : ℕ) (hc : RowStored c B) :
    Reached c B (3*m^2) r.rest.state := by
  have hp := BinaryFractionalCore.parameters_spec (BinaryFractionalCore.dimension c).1
  rw [(BinaryFractionalCore.dimension_spec c).1] at hp
  have hs := start_reached c _ r.first.1.choice B hc hp.2
  have h := trace_reached r.rest.trace hc hs
  simpa only [Nat.zero_add,hp.1,FractionalCover.fuel] using h

end DirectedFlowCutGap.BinaryApproximatePackingWidths
