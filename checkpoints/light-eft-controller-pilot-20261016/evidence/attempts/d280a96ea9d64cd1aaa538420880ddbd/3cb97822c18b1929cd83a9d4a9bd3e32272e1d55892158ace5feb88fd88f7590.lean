import LightEFTSpanners.SampleMatrixTrace

/-! The caller executes materialization and the distance submachine one step
at a time, then accumulates literal success/failure counts. No transition
invokes a whole subroutine, list length, finite enumeration or graph oracle. -/
namespace LightEFTSpanners.SampleVote
open Controller SampleRecords
inductive State where
  | samples : List Records → ℕ → ℕ → State
  | materialize : List Records → ℕ → ℕ → SampleRecords.State → State
  | distance : List Records → ℕ → ℕ → LinkedDistance.Matrix → LinkedDistance.State → State
  | halt : Bool → State
  deriving DecidableEq, Repr
 def finish (failures count : ℕ) : Bool := decide (0<count ∧ 3*count≤8*failures)
 def transition (n u v : ℕ) (budget : ℚ) : State → Option State
  | .samples [] failures count => some (.halt (finish failures count))
  | .samples (R::rs) failures count => some (.materialize rs failures count (.row 0 R []))
  | .materialize rs failures count s =>
      match SampleRecords.transition s with
      | some t => some (.materialize rs failures count t)
      | none => match s with
        | .halt M => some (.distance rs failures count M (.init n 0 []))
        | _ => some (.halt false)
  | .distance rs failures count M s =>
      match LinkedDistance.transition n M u v budget s with
      | some t => some (.distance rs failures count M t)
      | none => match s with
        | .halt b => some (.samples rs (failures+(if b then 0 else 1)) (count+1))
        | _ => some (.halt false)
  | .halt _ => none
 theorem materialize_lift (n u v : ℕ) (budget : ℚ) (rs : List Records) (f c : ℕ)
    {k : ℕ} {s t : SampleRecords.State} (h : Trace SampleRecords.transition k s t) :
    Trace (transition n u v budget) k (.materialize rs f c s) (.materialize rs f c t) := by
  induction h with
  | refl => exact .refl _
  | cons he _ ih => exact .cons (by simp only [transition,he]) ih
 theorem distance_lift (n u v : ℕ) (budget : ℚ) (rs : List Records) (f c : ℕ)
    (M : LinkedDistance.Matrix) {k : ℕ} {s t : LinkedDistance.State}
    (h : LinkedDistance.Executes (LinkedDistance.transition n M u v budget) k s t) :
    Trace (transition n u v budget) k (.distance rs f c M s) (.distance rs f c M t) := by
  induction h with
  | refl => exact .refl _
  | cons he _ ih => exact .cons (by simp only [transition,he]) ih
 def perSample (n : ℕ) : ℕ := 2*n*n+4*n+LinkedDistance.bound n+5
 def encoded {n : ℕ} (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (draws : List (Finset (Sym2 (Fin n)))) : List Records := draws.map (fun S => SampleRecords.encode Q E T S w)
end LightEFTSpanners.SampleVote
