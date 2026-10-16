import LightEFTSpanners.StoredComponentOriginal

namespace LightEFTSpanners.StoredReachability
open Controller

def test {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : Bool := RationalDistance.shortTest G (fun _ => 0) u v 0

theorem test_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : test G u v=true ↔ G.Reachable u v := by
  rw [test,RationalDistance.shortTest_iff G (fun _ => 0) (fun _ => le_rfl)]
  constructor
  · rintro ⟨p,_⟩;exact ⟨p⟩
  · rintro ⟨p⟩
    refine ⟨p,?_⟩
    have hz : LightSpanners.walkWeight (fun _ : Sym2 (Fin n) => (0:ℝ)) p=0 := by
      induction p with
      | nil => rfl
      | cons h p ih => simp [LightSpanners.walkWeight]
    simpa using hz.le

inductive State where
  | scan : List ℕ → List ℕ → State
  | distance : ℕ → List ℕ → List ℕ → LinkedDistance.State → State
  | reverse : List ℕ → List ℕ → State
  | halt : List ℕ → State
  deriving DecidableEq, Repr

def transition (n : ℕ) (M : LinkedDistance.Matrix) (root : ℕ) : State → Option State
  | .scan [] acc => some (.reverse acc [])
  | .scan (v::vs) acc => some (.distance v vs acc (.init n 0 []))
  | .distance v vs acc (.halt b) => some (.scan vs (if b then v::acc else acc))
  | .distance v vs acc s => (LinkedDistance.transition n M root v 0 s).map (.distance v vs acc)
  | .reverse [] out => some (.halt out)
  | .reverse (v::vs) out => some (.reverse vs (v::out))
  | .halt _ => none

theorem distance_lift (n : ℕ) (M : LinkedDistance.Matrix) (root v : ℕ)
    (vs acc : List ℕ) {k : ℕ} {s t : LinkedDistance.State}
    (h : LinkedDistance.Executes (LinkedDistance.transition n M root v 0) k s t) :
    Trace (transition n M root) k (.distance v vs acc s) (.distance v vs acc t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [LinkedDistance.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map (State.distance v vs acc)) he

theorem reverse_trace (n : ℕ) (M : LinkedDistance.Matrix) (root : ℕ) (vs out : List ℕ) :
    Trace (transition n M root) (vs.length+1) (.reverse vs out) (.halt (vs.reverse++out)) := by
  induction vs generalizing out with
  | nil => exact Trace.one rfl
  | cons v vs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n M root (.reverse (v::vs) out)=some (.reverse vs (v::out)) from rfl)
        (ih (v::out))
end LightEFTSpanners.StoredReachability
