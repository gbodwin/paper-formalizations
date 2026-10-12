import GreedyShortcuts.FiniteThresholdGreedy

/-! Computable finite argmin with a deterministic list-order tie rule.
The supplied score is evaluated on actual insertions, not a proxy potential. -/
namespace GreedyShortcuts.FiniteExecutableGreedy
variable {α : Type*}

def select (score : α → ℕ) : List α → Option α
  | [] => none
  | a::xs => match select score xs with
    | none => some a
    | some b => some (if score a≤score b then a else b)

theorem select_none_iff (score : α → ℕ) (xs : List α) :
    select score xs=none ↔ xs=[] := by
  cases xs with
  | nil => simp [select]
  | cons a xs => simp only [select]; split <;> simp

theorem select_spec (score : α → ℕ) (xs : List α) {a : α}
    (ha : select score xs=some a) : a∈xs ∧ ∀b∈xs,score a≤score b := by
  induction xs generalizing a with
  | nil => simp [select] at ha
  | cons b xs ih =>
    cases hs : select score xs with
    | none =>
      have he : xs=[] := (select_none_iff score xs).mp hs
      subst xs
      simp only [select,Option.some.injEq] at ha
      subst a
      simp
    | some c =>
      have hc := ih hs
      simp only [select,hs,Option.some.injEq] at ha
      by_cases hbc : score b≤score c
      · simp only [ite_eq_left hbc] at ha
        subst a
        refine ⟨List.mem_cons_self,?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact hbc.trans (hc.2 x hx)
      · simp only [ite_eq_right hbc] at ha
        subst a
        refine ⟨List.mem_cons_of_mem _ hc.1,?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact hc.2 x hx

variable [DecidableEq α]

def step (choices : List α) (score : Finset α → ℕ)
    (stopped : Finset α → Bool) (H : Finset α) : Finset α :=
  if stopped H then H else
    match select (fun e => score (insert e H)) choices with
    | none => H
    | some e => insert e H

def run (choices : List α) (score : Finset α → ℕ)
    (stopped : Finset α → Bool) : ℕ → Finset α
  | 0 => ∅
  | k+1 => step choices score stopped (run choices score stopped k)

/-- A computational implementation is linked to the original system only
through exact candidates, exact raw scores and the unchanged stopping rule. -/
structure Represents (A : FiniteThresholdGreedy.System α) (choices : List α)
    (score : Finset α → ℕ) (stopped : Finset α → Bool) : Prop where
  choices_iff : ∀e,e∈choices ↔ e∈A.candidates
  score_eq : ∀H,H⊆A.candidates → score H=A.potential H
  stopped_iff : ∀H,H⊆A.candidates → (stopped H=true ↔ A.stopped H)

namespace Represents

variable {A : FiniteThresholdGreedy.System α} {choices : List α}
    {score : Finset α → ℕ} {stopped : Finset α → Bool}
    (R : Represents A choices score stopped)
include R

theorem step_of_stopped (H : Finset α) (hH : H⊆A.candidates) (hs : A.stopped H) :
    step choices score stopped H=H := by
  simp [step,(R.stopped_iff H hH).mpr hs]

theorem step_minimizes (H : Finset α) (hH : H⊆A.candidates) (hs : ¬A.stopped H) :
    ∃e∈A.candidates, step choices score stopped H=insert e H ∧
      ∀f∈A.candidates,A.potential (insert e H)≤A.potential (insert f H) := by
  have hb : stopped H≠true := fun h => hs ((R.stopped_iff H hH).mp h)
  obtain ⟨f,hf,_⟩ := A.progress H hH hs
  cases he : select (fun e => score (insert e H)) choices with
  | none =>
    have hempty := (select_none_iff _ choices).mp he
    have hf' := (R.choices_iff f).mpr hf
    simp [hempty] at hf'
  | some e =>
    have hh := select_spec _ choices he
    have hE := (R.choices_iff e).mp hh.1
    refine ⟨e,hE,by simp [step,hb,he],?_⟩
    intro f hf
    have hm := hh.2 f ((R.choices_iff f).mpr hf)
    simpa only [R.score_eq _ (Finset.insert_subset hE hH),
      R.score_eq _ (Finset.insert_subset hf hH)] using hm

theorem step_legal (H : Finset α) (hH : H⊆A.candidates) :
    step choices score stopped H⊆A.candidates := by
  by_cases hs : A.stopped H
  · simpa only [R.step_of_stopped H hH hs] using hH
  · obtain ⟨e,he,hstep,_⟩ := R.step_minimizes H hH hs
    rw [hstep]
    exact Finset.insert_subset he hH

theorem step_card_active (H : Finset α) (hH : H⊆A.candidates) (hs : ¬A.stopped H) :
    (step choices score stopped H).card=H.card+1 := by
  obtain ⟨e,he,hstep,hm⟩ := R.step_minimizes H hH hs
  obtain ⟨f,hf,hfdrop⟩ := A.progress H hH hs
  have hdrop := (hm f hf).trans_lt hfdrop
  have hfresh : e∉H := by
    intro hmem
    simp only [Finset.insert_eq_of_mem hmem] at hdrop
    omega
  rw [hstep,Finset.card_insert_of_notMem hfresh]

theorem run_legal (k : ℕ) : run choices score stopped k⊆A.candidates := by
  induction k with
  | zero => exact Finset.empty_subset _
  | succ k ih => exact R.step_legal _ ih

theorem run_card_or_stopped (k : ℕ) :
    (run choices score stopped k).card=k ∨ A.stopped (run choices score stopped k) := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    by_cases hs : A.stopped (run choices score stopped k)
    · exact Or.inr (by simpa only [run,R.step_of_stopped _ (R.run_legal k) hs] using hs)
    · have hc := ih.resolve_right hs
      exact Or.inl (by rw [run,R.step_card_active _ (R.run_legal k) hs,hc])

theorem run_terminates : A.stopped (run choices score stopped choices.toFinset.card) := by
  have hchoices : choices.toFinset=A.candidates := by
    ext e
    simp [R.choices_iff]
  rw [hchoices]
  by_contra hs
  have hc := (R.run_card_or_stopped A.candidates.card).resolve_right hs
  have hn := R.step_card_active _ (R.run_legal A.candidates.card) hs
  have hb := Finset.card_le_card (R.run_legal (A.candidates.card+1))
  change (step choices score stopped (run choices score stopped A.candidates.card)).card≤_ at hb
  omega

end Represents
end GreedyShortcuts.FiniteExecutableGreedy
