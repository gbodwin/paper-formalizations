import DirectedFlowCutGap.ImmutableReferenceSimulation

/-! Retarget the physical interpreter from an explicitly zero-extended
source to its original input. An exhausted request has the same false value
as a request to the witness extension. Heap, control, events and charges
are identical. The original input can still detect exhaustion by counting
requests. -/
namespace DirectedFlowCutGap.ReferenceSourcePadding

open BinaryArithmetic ImmutableReferenceSimulation

def requests (events : List Event) : ℕ := events.countP fun e =>
  match e with | .request _ => true | .emit _ => false

theorem requests_append (left right : List Event) :
    requests (left ++ right) = requests left + requests right := by
  simp [requests,List.countP_append]

@[simp] theorem requests_literal (bits : Bits) : requests (bits.map Event.request) = bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [requests] at ih ⊢

def withSource {C : ℕ} (s : BitState C) (source : Bits) : BitState C := { s with source := source }

private theorem head_padding (source : Bits) (k : ℕ) :
    (source ++ List.replicate k false).headD false = source.headD false := by
  cases source with
  | nil => cases k <;> rfl
  | cons x xs => rfl

private theorem drop_padding (source : Bits) (k n : ℕ) :
    (source ++ List.replicate k false).drop n =
      source.drop n ++ List.replicate (k-(n-source.length)) false := by
  induction source generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n => simpa only [List.cons_append,List.drop_succ_cons,List.length_cons,Nat.succ_sub_succ_eq_sub] using ih n

private theorem retarget_step {C : ℕ} (p : Program C) (s : BitState C) (source : Bits)
    (head : source.headD false = s.source.headD false) :
    tick p (withSource s source) = (tick p s).map fun r =>
      {r with state := withSource r.state (source.drop (requests r.events))} := by
  cases op : p s.pc <;> simp only [tick,withSource,op]
  all_goals try rfl
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · simp only [head,Option.map_some,requests]
    cases source <;> rfl
  · split <;> rfl

private theorem source_step {C : ℕ} {p : Program C} {s : BitState C} {r : Result Bits C}
    (ran : tick p s = some r) : r.state.source = s.source.drop (requests r.events) := by
  have self : withSource s s.source = s := by cases s; rfl
  have h := retarget_step p s s.source rfl
  rw [self,ran,Option.map_some] at h
  exact congrArg (fun x : Result Bits C => x.state.source) (Option.some.inj h)

theorem trim {C steps paid : ℕ} {p : Program C} {s out : BitState C} {events : List Event}
    (ran : Run p steps paid s events out) (source : Bits) (k : ℕ)
    (padded : s.source = source ++ List.replicate k false) :
    Run p steps paid (withSource s source) events
      (withSource out (source.drop (requests events))) := by
  induction ran generalizing source k with
  | done s => exact Run.done _
  | @step s mid r steps paid es step tail ih =>
    have hhead : source.headD false = s.source.headD false := by rw [padded,head_padding]
    have first := retarget_step p s source hhead
    rw [step,Option.map_some] at first
    have follows : r.state.source = source.drop (requests r.events) ++
        List.replicate (k-(requests r.events-source.length)) false := by
      rw [source_step step,padded,drop_padding]
    have rest := ih _ _ follows
    simpa only [requests_append,List.drop_drop] using Run.step first rest

end DirectedFlowCutGap.ReferenceSourcePadding
