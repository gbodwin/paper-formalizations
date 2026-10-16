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
 def run {S : Type*} (step : S → Option S) : ℕ → S → S
  | 0,s => s
  | k+1,s => match step s with | none => s | some t => run step k t
 theorem Trace.run_eq {S : Type*} {step : S → Option S} {k : ℕ} {s t : S}
    (h : Trace step k s t) : run step k s=t := by
  induction h with
  | refl => rfl
  | cons he _ ih => simp only [run,he,ih]
 theorem run_terminal {S : Type*} (step : S → Option S) (s : S)
    (hs : step s=none) (k : ℕ) : run step k s=s := by
  cases k <;> simp [run,hs]
 theorem run_add {S : Type*} (step : S → Option S) (k m : ℕ) (s : S) :
    run step (k+m) s=run step m (run step k s) := by
  induction k generalizing s with
  | zero => simp [run]
  | succ k ih =>
    cases h : step s with
    | none => simp [run,h,run_terminal step s h]
    | some t => simpa only [Nat.succ_add,run,h] using ih t
end LightEFTSpanners.Controller
