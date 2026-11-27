import OnlineReachabilityPreservers.SteinerBinaryWordSession

/-! Replay a stream of binary arrival words against one initialized session. -/

namespace OnlineReachabilityPreservers

/-- Request the next state using one demand at a time. Stop at the first
rejected input and keep a separate tally of the input work. -/
def finSteinerBinaryWordSessionServe {n height : ℕ} :
    FinSteinerBinaryWordSession n height → List (List Bool × List Bool) →
      Option (FinSteinerBinaryWordSession n height) × ℕ
  | session, [] => (some session,2)
  | session, word::rest =>
    let step := finSteinerBinaryWordSessionStep session word
    match step.1 with
    | none => (none,step.2+2)
    | some next =>
      let suffix := finSteinerBinaryWordSessionServe next rest
      (suffix.1,step.2+suffix.2+4)

/-- The typed solver and the encoded solver have the same final state
on a canonical encoding of any list of finite demands. -/
theorem finSteinerBinaryWordSessionServe_refines {n height : ℕ} (session : FinSteinerBinaryWordSession n height)
    (fits : n ≤ 2^session.width) (demands : List (Fin n × Fin n)) :
    (finSteinerBinaryWordSessionServe session (binaryEncodeArcs (binaryFinLabel session.width) demands)).1 =
      some { session with
        state := demands.foldl (finSteinerBinaryArrivalStepFromSeed session.graph session.raw session.graphExact
          height session.seed) session.state } := by
  induction demands generalizing session with
  | nil => rfl
  | cons demand rest ih =>
    simp only [binaryEncodeArcs,List.map_cons,finSteinerBinaryWordSessionServe]
    rw [finSteinerBinaryWordSessionStep_refines session fits demand]
    dsimp only
    let advanced := { session with
      state := finSteinerBinaryArrivalStepFromSeed session.graph session.raw session.graphExact
        height session.seed session.state demand }
    simpa only [advanced,binaryEncodeArcs,List.foldl_cons] using ih advanced fits

/-- The guarded graph decoder accepts a canonical encoding with exactly
its original arc order and multiplicities. -/
theorem decodeCheckedBinaryFinArcRowsWithWork_encoded {n : ℕ} (width : ℕ) (fits : n ≤ 2^width)
    (arcs : List (Fin n × Fin n)) :
    (decodeCheckedBinaryFinArcRowsWithWork width (binaryEncodeArcs (binaryFinLabel width) arcs)).1 = some arcs := by
  apply (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff width _ arcs).mpr
  refine ⟨?_, (decodeBinaryFinArcRowsWithWork_eq_some_iff width _ arcs).mp
    (decodeBinaryFinArcRowsWithWork_spec width fits arcs).1⟩
  intro words present
  obtain ⟨arc, _, rfl⟩ := List.mem_map.mp present
  exact ⟨(binaryFinLabel_spec width fits arc.1).2.le, (binaryFinLabel_spec width fits arc.2).2.le⟩

/-- The trace input charge consists of the total raw bit count and a
fixed one-row allowance at the declared width. -/
def binaryWordSessionTraceInputWorkBudget (width : ℕ) (words : List (List Bool × List Bool)) : ℕ :=
  2 + binaryEndpointBits words + words.length*(2+4*(width+1)+7+binaryFinArcDecodingWorkBudget 1 width+14)

private theorem binaryWordSessionTraceInputWorkBudget_cons (width : ℕ) (word : List Bool × List Bool)
    (rest : List (List Bool × List Bool)) :
    binaryWordSessionTraceInputWorkBudget width (word::rest) =
      binaryWordSessionTraceInputWorkBudget width rest + binaryEndpointWidthCheckBudget width [word] +
        binaryFinArcDecodingWorkBudget 1 width + 14 := by
  simp only [binaryWordSessionTraceInputWorkBudget,binaryEndpointWidthCheckBudget,binaryEndpointBits,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
    Nat.add_mul,Nat.one_mul]
  omega

/-- The raw trace work bound covers all accepted steps and bounds the
work of stopping on malformed input as well. -/
theorem finSteinerBinaryWordSessionServe_work_le {n height : ℕ} (session : FinSteinerBinaryWordSession n height)
    (words : List (List Bool × List Bool)) : (finSteinerBinaryWordSessionServe session words).2 ≤
      binaryWordSessionTraceInputWorkBudget session.width words := by
  induction words generalizing session with
  | nil => simp [finSteinerBinaryWordSessionServe,binaryWordSessionTraceInputWorkBudget,binaryEndpointBits]
  | cons word rest ih =>
    let step := finSteinerBinaryWordSessionStep session word
    have charge := finSteinerBinaryWordSessionStep_work_le session word
    change step.2 ≤ _ at charge
    rw [binaryWordSessionTraceInputWorkBudget_cons]
    change (match step.1 with
      | none => (none,step.2+2)
      | some next =>
        let suffix := finSteinerBinaryWordSessionServe next rest
        (suffix.1,step.2+suffix.2+4) : Option (FinSteinerBinaryWordSession n height) × ℕ).2 ≤ _
    cases resultEq : step.1 with
    | none =>
      change step.2+2 ≤ _
      omega
    | some next =>
      have widthExact : next.width = session.width := by
        unfold step finSteinerBinaryWordSessionStep at resultEq
        obtain ⟨state,_,found⟩ := Option.map_eq_some_iff.mp resultEq
        exact (congrArg FinSteinerBinaryWordSession.width found).symm
      have suffix := ih next
      rw [widthExact] at suffix
      change step.2+(finSteinerBinaryWordSessionServe next rest).2+4 ≤ _
      omega

end OnlineReachabilityPreservers
