import DirectedFlowCutGap.ImmutableReferenceSimulation

/-! Literal successful-run preservation under an added saved caller stack.
The proof checks every actual instruction and is used for concrete call joins. -/
namespace DirectedFlowCutGap.ReferenceProgramStack
open ImmutableReferenceSimulation

def state {C : ℕ} (extra : List (Frame ℕ C)) (s : NaturalState C) : NaturalState C :=
  {s with stack := s.stack++extra}
def result {C : ℕ} (extra : List (Frame ℕ C)) (r : Result ℕ C) : Result ℕ C :=
  {r with state := state extra r.state}

theorem tick {C : ℕ} (p : Program C) (extra : List (Frame ℕ C))
    {s : NaturalState C} {r : Result ℕ C} (h : tickNatural p s=some r) :
    tickNatural p (state extra s)=some (result extra r) := by
  cases hp : p s.pc with
  | halt => simp [tickNatural,hp] at h
  | move dst src pc =>
      simp only [tickNatural,hp,Option.some.injEq] at h
      cases h
      simp [tickNatural,state,hp,result]
  | make dst recipe pc =>
      simp only [tickNatural,hp,Option.some.injEq] at h
      cases h
      simp [tickNatural,state,hp,result,allocateNatural]
  | branch src n z o pair =>
      simp only [tickNatural,hp] at h
      cases hc : s.heap[s.registers.get src]? with
      | none => simp [hc] at h
      | some c =>
          simp only [hc,Option.some.injEq] at h
          cases h
          simp [tickNatural,state,hp,result,hc]
  | field dst src right pc =>
      simp only [tickNatural,hp] at h
      split at h
      · simp only [Option.some.injEq] at h
        cases h
        simp_all [tickNatural,state,result]
      · simp at h
  | call entry continuation dst =>
      simp only [tickNatural,hp,Option.some.injEq] at h
      cases h
      simp [tickNatural,state,hp,result]
  | ret reg =>
      simp only [tickNatural,hp] at h
      cases hs : s.stack with
      | nil => simp [hs] at h
      | cons hd tl =>
          simp only [hs,Option.some.injEq] at h
          cases h
          simp [tickNatural,state,hp,result,hs]
  | request dst pc =>
      simp only [tickNatural,hp,Option.some.injEq] at h
      cases h
      simp [tickNatural,state,hp,result,allocateNatural]
  | emit src pc =>
      simp only [tickNatural,hp] at h
      split at h
      · simp only [Option.some.injEq] at h
        cases h
        simp_all [tickNatural,state,result]
      · simp at h

theorem run {C : ℕ} (p : Program C) (extra : List (Frame ℕ C))
    {t : ℕ} {s u : NaturalState C} {events : List Event}
    (h : NaturalRun p t s events u) :
    NaturalRun p t (state extra s) events (state extra u) := by
  induction h with
  | done s => exact .done _
  | step ht _ ih => simpa only [result] using NaturalRun.step (tick p extra ht) ih

end DirectedFlowCutGap.ReferenceProgramStack
