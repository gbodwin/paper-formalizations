import DirectedFlowCutGap.ImmutableReferenceSimulation

/-! Exact control-label relocation for successful runs. Heap data, register
values, events, source and stack shape are preserved. Terminal slots may be
replaced by a continuation: the premise is required only at non-halt slots. -/
namespace DirectedFlowCutGap.ReferenceProgramLabels
open ImmutableReferenceSimulation

def instruction {C D : ℕ} (f : Fin C → Fin D) : Instruction C → Instruction D
  | .move d s p => .move d s (f p)
  | .make d r p => .make d r (f p)
  | .branch s n z o p => .branch s (f n) (f z) (f o) (f p)
  | .field d s b p => .field d s b (f p)
  | .call e c d => .call (f e) (f c) d
  | .ret r => .ret r
  | .request d p => .request d (f p)
  | .emit s p => .emit s (f p)
  | .halt => .halt

def frame {C D : ℕ} (f : Fin C → Fin D) (r : Frame ℕ C) : Frame ℕ D :=
  ⟨f r.continuation,r.destination,r.saved⟩
def state {C D : ℕ} (f : Fin C → Fin D) (s : NaturalState C) : NaturalState D :=
  ⟨s.heap,s.next,s.registers,s.stack.map (frame f),f s.pc,s.source⟩
def result {C D : ℕ} (f : Fin C → Fin D) (r : Result ℕ C) : Result ℕ D :=
  ⟨state f r.state,r.events,r.cost⟩

theorem tag {C D : ℕ} (f : Fin C → Fin D) (n z o p : Fin C) (c : Cell ℕ) :
    tagBranch (f n) (f z) (f o) (f p) c = f (tagBranch n z o p c) := by
  cases c with
  | nil => rfl
  | flag b => cases b <;> rfl
  | pair a b => rfl

/-- The successful-step equation is proved for every actual instruction,
including caller frames; no external interpreter-correctness premise is used. -/
theorem tick {C D : ℕ} (f : Fin C → Fin D) (p : Program C) (q : Program D)
    (agree : ∀ pc, p pc ≠ .halt → q (f pc) = instruction f (p pc))
    {s : NaturalState C} {r : Result ℕ C} (h : tickNatural p s = some r) :
    tickNatural q (state f s) = some (result f r) := by
  have hn : p s.pc ≠ .halt := by intro he; simp [tickNatural,he] at h
  have ha := agree s.pc hn
  cases hp : p s.pc with
  | halt => exact (hn hp).elim
  | move dst src pc =>
      simp only [tickNatural,hp,Option.some.injEq] at h
      cases h
      simp [tickNatural,state,ha,hp,instruction,result]
  | make dst recipe pc =>
      simp [tickNatural,hp,ha,instruction,state,allocateNatural] at h ⊢
      cases h
      rfl
  | branch src n z o pair =>
      simp only [tickNatural,hp] at h
      cases hc : s.heap[s.registers.get src]? with
      | none => simp [hc] at h
      | some c =>
          simp only [hc,Option.some.injEq] at h
          cases h
          simp [tickNatural,state,ha,hp,instruction,result,tag,hc]
  | field dst src right pc =>
      simp only [tickNatural,hp] at h
      split at h
      · simp only [Option.some.injEq] at h
        cases h
        simp_all [tickNatural,state,result,instruction]
      · simp at h
  | call entry continuation dst =>
      simp [tickNatural,hp] at h
      cases h
      simp [tickNatural,state,ha,hp,instruction,result,frame]
  | ret reg =>
      simp only [tickNatural,hp] at h
      cases hs : s.stack with
      | nil => simp [hs] at h
      | cons hd tl =>
          simp only [hs,Option.some.injEq] at h
          cases h
          simp [tickNatural,state,ha,hp,instruction,result,frame,hs]
  | request dst pc =>
      simp [tickNatural,hp] at h
      cases h
      simp [tickNatural,state,ha,hp,instruction,result,allocateNatural]
  | emit src pc =>
      simp only [tickNatural,hp] at h
      split at h
      · simp only [Option.some.injEq] at h
        cases h
        simp_all [tickNatural,state,result,instruction]
      · simp at h

theorem run {C D : ℕ} (f : Fin C → Fin D) (p : Program C) (q : Program D)
    (agree : ∀ pc, p pc ≠ .halt → q (f pc) = instruction f (p pc))
    {t : ℕ} {s u : NaturalState C} {events : List Event}
    (h : NaturalRun p t s events u) :
    NaturalRun q t (state f s) events (state f u) := by
  induction h with
  | done s => exact .done _
  | step ht _ ih => exact .step (tick f p q agree ht) ih

end DirectedFlowCutGap.ReferenceProgramLabels
