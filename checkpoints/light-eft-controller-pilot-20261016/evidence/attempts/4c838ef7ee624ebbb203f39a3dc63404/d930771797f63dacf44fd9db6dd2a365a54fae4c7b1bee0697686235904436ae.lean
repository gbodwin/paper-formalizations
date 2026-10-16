import LightEFTSpanners.LinkedDistanceExecutable

/-! Indexed successful transitions for finite caller controllers. -/
namespace LightEFTSpanners.Controller
inductive Trace {S : Type*} (step : S → Option S) : ℕ → S → S → Prop
  | refl (s) : Trace step 0 s s
  | cons {n s t u} : step s=some t → Trace step n t u → Trace step (n+1) s u
namespace Trace
 theorem trans {S : Type*} {step : S → Option S} {a b c : S} {n m : ℕ}
    (h : Trace step n a b) (g : Trace step m b c) : Trace step (n+m) a c := by
  induction h with
  | refl => simpa using g
  | cons hs _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cons hs (ih g)
 theorem one {S : Type*} {step : S → Option S} {a b : S} (h : step a=some b) :
    Trace step 1 a b := .cons h (.refl b)
end Trace
 /-- Explicit total recursion: preserves the finite controller equations without
 introducing a recursive predefinition and its partial implementation companion. -/
 def run {S : Type*} (step : S → Option S) : ℕ → S → S :=
  Nat.rec (motive := fun _ => S → S) (fun s => s)
    (fun _ previous s => match step s with | none => s | some t => previous t)
 theorem run_zero {S : Type*} (step : S → Option S) (s : S) : run step 0 s = s := rfl
 theorem run_succ {S : Type*} (step : S → Option S) (k : ℕ) (s : S) :
    run step (k+1) s = (match step s with | none => s | some t => run step k t) := rfl
 /-- The historical zero/successor equations uniquely characterize this function. -/
 theorem run_eq_of_equations {S : Type*} (step : S → Option S) (f : ℕ → S → S)
    (hzero : ∀ s, f 0 s = s)
    (hsucc : ∀ k s, f (k+1) s = (match step s with | none => s | some t => f k t)) :
    run step = f := by
  funext k s
  induction k generalizing s with
  | zero => exact (hzero s).symm
  | succ k ih =>
    rw [run_succ, hsucc]
    cases step s with
    | none => rfl
    | some t => exact ih t
 theorem Trace.run_eq {S : Type*} {step : S → Option S} {k : ℕ} {s t : S}
    (h : Trace step k s t) : run step k s=t := by
  induction h with
  | refl => rfl
  | cons he _ ih => simp only [run_succ,he,ih]
 theorem run_terminal {S : Type*} (step : S → Option S) (s : S)
    (hs : step s=none) (k : ℕ) : run step k s=s := by
  cases k <;> simp [run_zero,run_succ,hs]
 theorem run_add {S : Type*} (step : S → Option S) (k m : ℕ) (s : S) :
    run step (k+m) s=run step m (run step k s) := by
  induction k generalizing s with
  | zero => simp [run_zero]
  | succ k ih =>
    cases h : step s with
    | none => simp [run_succ,h,run_terminal step s h]
    | some t => simpa only [Nat.succ_add,run_succ,h] using ih t
end LightEFTSpanners.Controller
