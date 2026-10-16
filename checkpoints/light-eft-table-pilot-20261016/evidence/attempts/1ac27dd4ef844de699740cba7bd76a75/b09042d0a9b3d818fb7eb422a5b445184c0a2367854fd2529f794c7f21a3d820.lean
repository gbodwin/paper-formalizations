import LightEFTSpanners.BernoulliTestConcentration
import LightEFTSpanners.FreshVotingTapes
import LightEFTSpanners.AdaptiveFiniteLaw

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset FiniteProbability
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
attribute [local instance] Classical.propDecidable

/-- Finite independent fresh batches along the exact tail-first execution.
Every stage samples anew; the updated assignment becomes the original Tape. -/
noncomputable def executionLaw (f : ℕ) (hf : 0<f) (m : ℕ) :
    List (Sym2 V) → Law (Assignment V J m)
  | [] => Law.pure (fun _ _ _ => ∅)
  | e::es => (executionLaw f hf m es).bind (fun a =>
      (freshBatchLaw f hf m).map (Function.update a e))

/-- Accuracy is obtained with an explicit adaptive union bound. There is no
assumed accurate trace and no union over unvisited graph states. -/
theorem execution_inaccurate_probability (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f : ℕ) (hf : 0<f) (m : ℕ) (hm : 0<m)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (h : ℕ)
    (l : List (Sym2 V)) (hl : l.Nodup) :
    (executionLaw (V:=V) (J:=J) f hf m l).prob (fun a =>
      ¬AccurateTrace Q w t f eligible host (assignmentTape a) h l) ≤
      ((l.map (fun e => (eligible e).card)).sum:ℝ)*(2*Real.exp (-(m:ℝ)/32)) := by
  induction l with
  | nil => simp [executionLaw,Law.prob_pure,AccurateTrace]
  | cons e es ih =>
    have he : e∉es := (List.nodup_cons.mp hl).1
    have hes := (List.nodup_cons.mp hl).2
    let oldGood := fun a : Assignment V J m =>
      AccurateTrace Q w t f eligible host (assignmentTape a) h es
    let newGood := fun a : Assignment V J m =>
      AccurateTrace Q w t f eligible host (assignmentTape a) h (e::es)
    let bad := fun (a : Assignment V J m) (b : J → Fin m → Finset (Sym2 V)) =>
      ∃ j∈eligible e, 1/8 <
        |estimate Q (edges Q w t eligible host (assignmentTape a) h es) (host j) w t e
          (List.ofFn (b j))-
          testProbability Q (edges Q w t eligible host (assignmentTape a) h es) (host j) w t f e|
    have hnew : ∀ a b, ¬newGood (Function.update a e b) → ¬oldGood a ∨ bad a b := by
      intro a b hn
      by_contra hfail
      have ho : oldGood a := by tauto
      have hb : ¬bad a b := fun hh => hfail (Or.inr hh)
      have hp := assignment_update_prefix Q w t f eligible host a e b h es he
      apply hn
      refine ⟨hp.2.mpr ho,?_⟩
      intro j hj
      have hh : |estimate Q (edges Q w t eligible host (assignmentTape a) h es) (host j) w t e
          (List.ofFn (b j))-
          testProbability Q (edges Q w t eligible host (assignmentTape a) h es) (host j) w t f e|≤1/8 :=
        le_of_not_gt (fun hlt => hb ⟨j,hj,hlt⟩)
      simpa only [hp.1,assignmentTape,Function.update_self] using hh
    have hs := Law.fresh_step_failure (executionLaw f hf m es) (freshBatchLaw f hf m)
      (fun a b => Function.update a e b) oldGood newGood bad
      ((eligible e).card*(2*Real.exp (-(m:ℝ)/32))) hnew
      (fun a => fresh_batch_bad_le Q (edges Q w t eligible host (assignmentTape a) h es)
        w t f hf e m hm (eligible e) host)
    change _ ≤ _ at hs
    have hi := ih hes
    change (executionLaw f hf m es).prob (fun a => ¬oldGood a)≤_ at hi
    change (executionLaw f hf m (e::es)).prob (fun a => ¬newGood a)≤_
    exact hs.trans (by simpa only [List.map_cons,List.sum_cons,Nat.cast_add,add_mul,add_comm]
      using add_le_add_right hi ((eligible e).card*(2*Real.exp (-(m:ℝ)/32))))
end LightEFTSpanners.SampledGreedy
