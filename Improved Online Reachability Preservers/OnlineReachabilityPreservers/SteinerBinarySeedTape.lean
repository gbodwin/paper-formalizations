import OnlineReachabilityPreservers.SteinerBinaryCompactWordOnline

/-! A finite sequential tape for the compact sampled solver. -/

namespace OnlineReachabilityPreservers

/-- Inspect the next bit and keep the remaining tape. An empty tape
cannot provide another bit. -/
def steinerBitTapeSource : StateT (List Bool) Option Bool := fun
  | [] => none
  | bit :: tail => some (bit,tail)

private theorem steiner_tape_draws_prefix {size : ℕ} (bits : Fin size → Bool) (tail : List Bool) :
    (Vector.ofFnM (fun _ : Fin size => steinerBitTapeSource)).run (List.ofFn bits ++ tail) =
      some (Vector.ofFn bits,tail) := by
  induction size generalizing tail with
  | zero =>
    have empty : Vector.ofFn bits = #v[] := by
      ext i inside
      omega
    rw [Vector.ofFnM_zero,List.ofFn_zero,List.nil_append,empty]
    rfl
  | succ size ih =>
    rw [Vector.ofFnM_succ,List.ofFn_succ',List.concat_eq_append,List.append_assoc,StateT.run_bind,ih]
    rw [Vector.ofFn_succ]
    rfl

private theorem steiner_tape_draws_none (size : ℕ) (tape : List Bool) (short : tape.length < size) :
    (Vector.ofFnM (fun _ : Fin size => steinerBitTapeSource)).run tape = none := by
  induction size with
  | zero => omega
  | succ size ih =>
    rw [Vector.ofFnM_succ,StateT.run_bind]
    by_cases smaller : tape.length < size
    · rw [ih smaller]
      rfl
    · have count : size = tape.length := by omega
      subst size
      have draws := steiner_tape_draws_prefix tape.get []
      rw [List.ofFn_get,List.append_nil] at draws
      rw [draws]
      rfl

/-- The seed sampler consumes the supplied seed prefix in order and
leaves any additional bits untouched. It keeps the exact recorded tally. -/
theorem readSteinerSeedWithWork_tape_prefix {size : ℕ} (count : {b : ℕ // b = size})
    (bits : Fin size → Bool) (tail : List Bool) :
    (readSteinerSeedWithWork count steinerBitTapeSource).run (List.ofFn bits ++ tail) =
      some ((Vector.ofFn bits,6*size+5),tail) := by
  obtain ⟨count,rfl⟩ := count
  rw [readSteinerSeedWithWork,StateT.run_bind,steiner_tape_draws_prefix]
  rfl

theorem readSteinerSeedWithWork_tape_none {size : ℕ} (count : {b : ℕ // b = size})
    (tape : List Bool) (short : tape.length < size) :
    (readSteinerSeedWithWork count steinerBitTapeSource).run tape = none := by
  obtain ⟨count,rfl⟩ := count
  rw [readSteinerSeedWithWork,StateT.run_bind,steiner_tape_draws_none count tape short]
  rfl

private theorem finSteinerBinaryArrivalStartFromBitSource_tape_prefix {n : ℕ}
    (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height : ℕ)
    (stream : ℕ → Bool) (start : ℕ) (tail : List Bool) :
    let bits (i : Fin (steinerBitBudget G height)) := stream (start+i.val)
    (finSteinerBinaryArrivalStartFromBitSource G raw same height steinerBitTapeSource).run
        (List.ofFn bits ++ tail) =
      some (((finSteinerBinaryArrivalStartFromBitSource G raw same height (steinerBitStreamSource stream)).run start).1,tail) := by
  simp only [finSteinerBinaryArrivalStartFromBitSource,StateT.run_bind,readSteinerSeedWithWork_tape_prefix,
    readSteinerSeedWithWork_stream,StateT.run_pure]
  rfl

private theorem finSteinerBinaryStartFromWords_tape_prefix {n : ℕ} (words : List (List Bool × List Bool))
    (height width : ℕ) (stream : ℕ → Bool) (start : ℕ) (tail : List Bool) (raw : List (Fin n × Fin n))
    (good : (decodeCheckedBinaryFinArcRowsWithWork width words).1 = some raw) :
    let bits (i : Fin (steinerBitBudget raw.toFinset height)) := stream (start+i.val)
    (finSteinerBinaryStartFromWords (n := n) words height width steinerBitTapeSource).run (List.ofFn bits ++ tail) =
      some (((finSteinerBinaryStartFromWords (n := n) words height width (steinerBitStreamSource stream)).run start).1,tail) := by
  let prepared := prepareSteinerBinaryArcRowsWithWork raw
  let same := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
  have count := congrArg (fun G => steinerBitBudget G height) (show raw.toFinset = prepared.1 from same)
  have bitsEq : (List.ofFn fun i : Fin (steinerBitBudget raw.toFinset height) => stream (start+i.val)) =
      (List.ofFn fun i : Fin (steinerBitBudget prepared.1 height) => stream (start+i.val)) :=
    List.ofFn_congr count (fun i => stream (start+i.val))
  dsimp only
  rw [bitsEq,finSteinerBinaryStartFromWords_accepts words height width stream start raw good]
  unfold finSteinerBinaryStartFromWords
  dsimp only
  rw [good,StateT.run_bind,finSteinerBinaryArrivalStartFromBitSource_tape_prefix prepared.1 raw same height stream start tail]
  rfl

/-- If the fixed graph is valid, the whole finite-tape run reads only
the seed prefix and returns the same result and tally as the stream run.
Demand decoding and service do not read additional bits. -/
theorem finSteinerBinaryServeCompactFromVariableWords_tape_prefix {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ)
    (stream : ℕ → Bool) (start : ℕ) (tail : List Bool) (raw : List (Fin n × Fin n))
    (good : (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw) :
    let bits (i : Fin (steinerBitBudget raw.toFinset height)) := stream (start+i.val)
    (finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height steinerBitTapeSource).run
        (List.ofFn bits ++ tail) =
      some (((finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height
        (steinerBitStreamSource stream)).run start).1,tail) := by
  have guarded := (decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits arcWords raw).mpr good
  simp only [finSteinerBinaryServeCompactFromVariableWords,finSteinerBinaryCompactWordStart,
    finSteinerBinaryStartFromVariableWords,StateT.run_bind,StateT.run_pure,
    finSteinerBinaryStartFromWords_tape_prefix arcWords height _ stream start tail raw guarded]
  generalize (finSteinerBinaryStartFromWords (n := n) arcWords height (n+binaryEndpointBits arcWords)
    (steinerBitStreamSource stream)).run start = started
  rcases started with ⟨⟨session,charge⟩,position⟩
  cases session <;> rfl

/-- Invalid graph words are rejected before reading the finite tape. -/
theorem finSteinerBinaryServeCompactFromVariableWords_tape_rejects_graph {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (tape : List Bool)
    (bad : (decodeBinaryFinArcRowsWithWork (n := n) 0 arcWords).1 = none) :
    ∃ work, (finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height steinerBitTapeSource).run tape =
      some ((none,work),tape) := by
  let width := n+binaryEndpointBits arcWords
  have rejected : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 = none := by
    cases found : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 with
    | none => rfl
    | some raw =>
      have valid := (decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits arcWords raw).mp found
      rw [bad] at valid
      exact nomatch valid
  refine ⟨(decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).2+2+
    binaryEndpointBits arcWords+8*arcWords.length+7+2+2,?_⟩
  dsimp only [width] at rejected
  simp only [finSteinerBinaryServeCompactFromVariableWords,finSteinerBinaryCompactWordStart,
    finSteinerBinaryStartFromVariableWords,finSteinerBinaryStartFromWords,StateT.run_bind,rejected,StateT.run_pure]
  rfl

/-- A valid graph with fewer supplied bits than its seed budget exhausts
the finite tape during initialization. -/
theorem finSteinerBinaryServeCompactFromVariableWords_tape_exhausted {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (tape : List Bool)
    (raw : List (Fin n × Fin n)) (good : (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw)
    (short : tape.length < steinerBitBudget raw.toFinset height) :
    (finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height steinerBitTapeSource).run tape = none := by
  let prepared := prepareSteinerBinaryArcRowsWithWork raw
  let same := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
  have short' : tape.length < steinerBitBudget prepared.1 height :=
    (congrArg (fun G => steinerBitBudget G height) (show raw.toFinset = prepared.1 from same)) ▸ short
  have guarded := (decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits arcWords raw).mpr good
  simp only [finSteinerBinaryServeCompactFromVariableWords,finSteinerBinaryCompactWordStart,
    finSteinerBinaryStartFromVariableWords,finSteinerBinaryStartFromWords,finSteinerBinaryArrivalStartFromBitSource,
    StateT.run_bind,guarded,readSteinerSeedWithWork_tape_none _ tape short']
  rfl

/-- On a valid graph, initialization succeeds exactly when the supplied
tape covers the seed budget. Success reads that prefix and preserves
the unused suffix, even if a demand word is rejected during service. -/
theorem finSteinerBinaryServeCompactFromVariableWords_tape_result {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (tape : List Bool)
    (raw : List (Fin n × Fin n)) (good : (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw) :
    let budget := steinerBitBudget raw.toFinset height
    let stream (i : ℕ) := tape[i]?.getD false
    (finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height steinerBitTapeSource).run tape =
      if budget ≤ tape.length then
        some (((finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height
          (steinerBitStreamSource stream)).run 0).1,tape.drop budget)
      else none := by
  let budget := steinerBitBudget raw.toFinset height
  let stream (i : ℕ) := tape[i]?.getD false
  change _ = if budget ≤ tape.length then
    some (((finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height
      (steinerBitStreamSource stream)).run 0).1,tape.drop budget) else none
  by_cases enough : budget ≤ tape.length
  · rw [ite_eq_left enough]
    have word : (List.ofFn fun i : Fin budget => stream (0+i.val)) = tape.take budget := by
      apply List.ext_getElem
      · simp [List.length_take,Nat.min_eq_left enough]
      · intro i left right
        have fit : i < tape.length := (List.length_take_le _ _ |> lt_of_lt_of_le right).trans_le enough
        simp only [List.getElem_ofFn,List.getElem_take,stream,Nat.zero_add,List.getElem?_eq_getElem fit,Option.getD_some]
    have run := finSteinerBinaryServeCompactFromVariableWords_tape_prefix
      arcWords demands height stream 0 (tape.drop budget) raw good
    dsimp only at run
    rw [word,List.take_append_drop] at run
    exact run
  · rw [ite_eq_right enough]
    exact finSteinerBinaryServeCompactFromVariableWords_tape_exhausted arcWords demands height tape raw good (lt_of_not_ge enough)

/-- On each accepted feasible trace with enough seed bits, the finite
tape run keeps the compact history and the polynomial recorded bound.
Unused bits do not enter the bound. -/
theorem finSteinerBinaryServeCompactFromVariableWords_tape_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (arcWords demands : List (List Bool × List Bool)) (tape : List Bool)
      (raw D : List (Fin n × Fin n)),
      (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw →
      (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D →
      (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
      let budget := steinerBitBudget raw.toFinset height
      budget ≤ tape.length →
      ∃ state work, (finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height
        steinerBitTapeSource).run tape = some ((some state,work),tape.drop budget) ∧
        state.history.reverse = distinctNonselfTrace D ∧
        work ≤ C*(binaryVariableWordInputSize n arcWords demands)^k := by
  obtain ⟨C,k,bounded⟩ := finSteinerBinaryServeCompactFromVariableWords_polynomial height
  refine ⟨C,k,?_⟩
  intro n arcWords demands tape raw D goodGraph goodDemands feasible budget enough
  let stream (i : ℕ) := tape[i]?.getD false
  let result := (finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height
    (steinerBitStreamSource stream)).run 0
  obtain ⟨state,present,history,_,_⟩ := finSteinerBinaryServeCompactFromVariableWords_refines
    arcWords demands height stream 0 raw D goodGraph goodDemands feasible
  refine ⟨state,result.1.2,?_,history,bounded arcWords demands raw D stream 0 goodGraph goodDemands feasible⟩
  have known := finSteinerBinaryServeCompactFromVariableWords_tape_result arcWords demands height tape raw goodGraph
  dsimp only at known
  rw [ite_eq_left enough] at known
  refine known.trans ?_
  change some (result.1,_) = some ((some state,result.1.2),_)
  rw [← present,Prod.eta]

end OnlineReachabilityPreservers
