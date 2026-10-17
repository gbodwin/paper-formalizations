import LightEFTSpanners.StoredWeightedForestExecution

namespace LightEFTSpanners.StoredWeightComparison
open Controller
inductive State where
  | first : StoredOriginalWeightLookup.State → State
  | second : ℚ → StoredOriginalWeightLookup.State → State
  | compare : ℚ → ℚ → State
  | halt : Bool → State
  deriving DecidableEq, Repr

def transition (bank : StoredOriginalWeightLookup.Bank) (x y : StoredEdges.Edge) : State → Option State
  | .first (.halt a) => some (.second a (.scan bank))
  | .first s => (StoredOriginalWeightLookup.transition x s).map State.first
  | .second a (.halt b) => some (.compare a b)
  | .second a s => (StoredOriginalWeightLookup.transition y s).map (State.second a)
  | .compare a b => some (.halt (decide (b≤a)))
  | .halt _ => none

def result (bank : StoredOriginalWeightLookup.Bank) (x y : StoredEdges.Edge) : Bool :=
  decide (StoredOriginalWeightLookup.value y bank≤StoredOriginalWeightLookup.value x bank)

def steps (bank : StoredOriginalWeightLookup.Bank) (x y : StoredEdges.Edge) : ℕ :=
  StoredOriginalWeightLookup.steps x bank+StoredOriginalWeightLookup.steps y bank+3

theorem first_lift (bank : StoredOriginalWeightLookup.Bank) (x y : StoredEdges.Edge)
    {k : ℕ} {s u : StoredOriginalWeightLookup.State}
    (ht : Trace (StoredOriginalWeightLookup.transition x) k s u) :
    Trace (transition bank x y) k (.first s) (.first u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt a => simp [StoredOriginalWeightLookup.transition] at he
    | scan rs => simpa only [transition,Option.map_some] using congrArg (Option.map State.first) he

theorem second_lift (bank : StoredOriginalWeightLookup.Bank) (x y : StoredEdges.Edge) (a : ℚ)
    {k : ℕ} {s u : StoredOriginalWeightLookup.State}
    (ht : Trace (StoredOriginalWeightLookup.transition y) k s u) :
    Trace (transition bank x y) k (.second a s) (.second a u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt b => simp [StoredOriginalWeightLookup.transition] at he
    | scan rs => simpa only [transition,Option.map_some] using congrArg (Option.map (State.second a)) he

theorem full_trace (bank : StoredOriginalWeightLookup.Bank) (x y : StoredEdges.Edge) :
    Trace (transition bank x y) (steps bank x y) (.first (.scan bank)) (.halt (result bank x y)) := by
  have a := first_lift bank x y (StoredOriginalWeightLookup.lookup_trace x bank)
  have b := Trace.one (show transition bank x y (.first (.halt (StoredOriginalWeightLookup.value x bank)))=
    some (.second (StoredOriginalWeightLookup.value x bank) (.scan bank)) from rfl)
  have c := second_lift bank x y (StoredOriginalWeightLookup.value x bank) (StoredOriginalWeightLookup.lookup_trace y bank)
  have d := Trace.cons (show transition bank x y
      (.second (StoredOriginalWeightLookup.value x bank) (.halt (StoredOriginalWeightLookup.value y bank)))=
      some (.compare (StoredOriginalWeightLookup.value x bank) (StoredOriginalWeightLookup.value y bank)) from rfl)
    (Trace.one (show transition bank x y (.compare (StoredOriginalWeightLookup.value x bank) (StoredOriginalWeightLookup.value y bank))=
      some (.halt (result bank x y)) from rfl))
  have hc : steps bank x y=StoredOriginalWeightLookup.steps x bank+(1+(StoredOriginalWeightLookup.steps y bank+(1+1))) := by unfold steps;omega
  rw [hc]
  exact a.trans (b.trans (c.trans d))

theorem steps_le (bank : StoredOriginalWeightLookup.Bank) (x y : StoredEdges.Edge) :
    steps bank x y≤2*bank.length+5 := by
  have a := StoredOriginalWeightLookup.steps_le x bank
  have b := StoredOriginalWeightLookup.steps_le y bank
  unfold steps
  omega
end LightEFTSpanners.StoredWeightComparison
