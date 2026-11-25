import OnlineReachabilityPreservers.SteinerBitReader

/-! Read a finite word through an index into the supplied bit function. -/

namespace OnlineReachabilityPreservers

/-- A position in a fixed finite word, including the position after its last bit. -/
structure BitCursor (budget : ℕ) where
  position : ℕ
  bounded : position ≤ budget

/-- The specification view of the unread suffix. -/
def cursorSuffix {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) : List Bool :=
  (List.ofFn bits).drop cursor.position

private def cursorSlice {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget)
    {width : ℕ} (enough : cursor.position + width ≤ budget) : Fin width → Bool :=
  fun i => bits ⟨cursor.position + i.val,by have inWidth := i.isLt; omega⟩

private def cursorWordAccum {budget : ℕ} (bits : Fin budget → Bool) :
    (width : ℕ) → (cursor : BitCursor budget) → ℕ → (cursor.position + width ≤ budget) → ℕ
  | 0, _, word, _ => word
  | width+1, cursor, word, enough =>
    let bit := bits ⟨cursor.position,by omega⟩
    let next : BitCursor budget := ⟨cursor.position+1,by omega⟩
    cursorWordAccum bits width next (2*word + if bit then 1 else 0) (by dsimp [next]; omega)

private theorem uniformBitsEquiv_cons_val {w : ℕ} (bits : Fin (w+1) → Bool) :
    (uniformBitsEquiv (w+1) bits).val = (if bits 0 then 2^w else 0) +
      (uniformBitsEquiv w (fun i => bits i.succ)).val := by
  let head := finTwoEquiv.symm (bits 0)
  change (uniformBitsEquiv w (fun i => bits i.succ)).val + (2^w)*head.val = _
  cases first : bits 0 <;> simp [head, first, finTwoEquiv, Nat.add_comm]

private theorem cursorWordAccum_eq {budget : ℕ} (bits : Fin budget → Bool) (width : ℕ)
    (cursor : BitCursor budget) (word : ℕ) (enough : cursor.position + width ≤ budget) :
    cursorWordAccum bits width cursor word enough = word*2^width +
      (uniformBitsEquiv width (cursorSlice bits cursor enough)).val := by
  induction width generalizing cursor word with
  | zero => simp [cursorWordAccum, uniformBitsEquiv]
  | succ width ih =>
    rw [cursorWordAccum, ih, uniformBitsEquiv_cons_val]
    let next : BitCursor budget := ⟨cursor.position+1,by omega⟩
    have fits : next.position+width ≤ budget := by dsimp [next]; omega
    have same : cursorSlice bits next fits = fun i : Fin width => (cursorSlice bits cursor enough) i.succ := by
      funext i
      apply congrArg bits
      apply Fin.ext
      change cursor.position+1+i.val = cursor.position+i.succ.val
      simp only [Fin.val_succ]
      omega
    change (2*word + if bits ⟨cursor.position,?_⟩ then 1 else 0)*2^width +
      (uniformBitsEquiv width (cursorSlice bits next fits)).val = _
    rw [same]
    have head : (cursorSlice bits cursor enough) 0 = bits ⟨cursor.position,by omega⟩ := by
      unfold cursorSlice
      exact congrArg bits (Fin.ext (Nat.add_zero _))
    rw [head]
    cases bits ⟨cursor.position,by omega⟩ <;> simp [pow_succ] <;> ring

/-- Read a word directly by position, without materializing the unused bits. -/
def consumeCursorWord {budget : ℕ} (bits : Fin budget → Bool) (width : ℕ)
    (cursor : BitCursor budget) : Option (Fin (2^width) × BitCursor budget) :=
  if enough : cursor.position + width ≤ budget then
    let word := cursorWordAccum bits width cursor 0 enough
    have same : word = (uniformBitsEquiv width (cursorSlice bits cursor enough)).val := by
      simpa only [Nat.zero_mul, Nat.zero_add] using cursorWordAccum_eq bits width cursor 0 enough
    some (⟨word,same.symm ▸ (uniformBitsEquiv width (cursorSlice bits cursor enough)).isLt⟩,
      ⟨cursor.position+width,enough⟩)
  else none

private theorem cursor_take_eq {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget)
    {width : ℕ} (enough : cursor.position + width ≤ budget) :
    (cursorSuffix bits cursor).take width = List.ofFn (cursorSlice bits cursor enough) := by
  apply List.ext_getElem
  · simp only [cursorSuffix, List.length_take, List.length_drop, List.length_ofFn]
    have fit : width ≤ budget-cursor.position := by omega
    exact Nat.min_eq_left fit
  · intro i hi hj
    simp only [cursorSuffix, List.getElem_take, List.getElem_drop, List.getElem_ofFn, cursorSlice]

/-- The cursor reader agrees with the original reader and with its unread suffix. -/
theorem consumeCursorWord_spec {budget : ℕ} (bits : Fin budget → Bool) (width : ℕ)
    (cursor : BitCursor budget) :
    (consumeCursorWord bits width cursor).map (fun (word,next) => (word,cursorSuffix bits next)) =
      consumeFairWord width (cursorSuffix bits cursor) := by
  by_cases enough : cursor.position + width ≤ budget
  · have dropRest : (cursorSuffix bits cursor).drop width = cursorSuffix bits ⟨cursor.position+width,enough⟩ := by
      simp only [cursorSuffix, List.drop_drop]
    have split := List.take_append_drop width (cursorSuffix bits cursor)
    rw [cursor_take_eq bits cursor enough, dropRest] at split
    rw [consumeCursorWord, dite_eq_left enough]
    rw [← split, consumeFairWord_ofFn]
    simp only [Option.map_some]
    apply congrArg some
    refine Prod.ext (Fin.ext ?_) rfl
    simpa only [Nat.zero_mul, Nat.zero_add] using cursorWordAccum_eq bits width cursor 0 enough
  · rw [consumeCursorWord, dite_eq_right enough]
    cases found : consumeFairWord width (cursorSuffix bits cursor) with
    | none => rfl
    | some pair =>
      obtain ⟨word,rest⟩ := pair
      have count := (consumeFairWord_suffix found).1
      simp only [cursorSuffix, List.length_drop, List.length_ofFn] at count
      have valid := cursor.bounded
      omega

private theorem consumeCursorWord_position {budget : ℕ} (bits : Fin budget → Bool) (width : ℕ)
    (cursor next : BitCursor budget) (word : Fin (2^width))
    (used : consumeCursorWord bits width cursor = some (word,next)) :
    next.position = cursor.position+width := by
  unfold consumeCursorWord at used
  split at used
  · cases used
    rfl
  · contradiction

private def consumeCursorIndexLoop {budget : ℕ} (bits : Fin budget → Bool) (N width : ℕ)
    (positive : 0 < width) (cursor : BitCursor budget) (rejected : ℕ) :
    Option ((Fin N × ℕ) × BitCursor budget) :=
  match used : consumeCursorWord bits width cursor with
  | none => none
  | some (word,next) =>
    if good : word.val < N then some ((⟨word.val,good⟩,rejected),next)
    else consumeCursorIndexLoop bits N width positive next (rejected+1)
termination_by budget-cursor.position
decreasing_by
  have usedWidth := consumeCursorWord_position bits width cursor next word used
  have fits := next.bounded
  omega

private theorem consumeCursorIndexLoop_spec {budget : ℕ} (bits : Fin budget → Bool) (N : ℕ)
    (width : 0 < uniformProposalWidth N) (cursor : BitCursor budget) (rejected : ℕ) :
    (consumeCursorIndexLoop bits N (uniformProposalWidth N) width cursor rejected).map
      (fun (output,next) => (output,cursorSuffix bits next)) =
    (consumeFairIndex N (cursorSuffix bits cursor)).map (fun ((index,k),rest) => ((index,k+rejected),rest)) := by
  induction cursor using (measure (fun c : BitCursor budget => budget-c.position)).wf.induction generalizing rejected with
  | h cursor ih =>
    have agrees := consumeCursorWord_spec bits (uniformProposalWidth N) cursor
    rw [consumeCursorIndexLoop, consumeFairIndex, dite_eq_left width]
    cases used : consumeCursorWord bits (uniformProposalWidth N) cursor with
    | none =>
      simp only [used, Option.map_none] at agrees
      rw [← agrees]
      rfl
    | some result =>
      obtain ⟨word,next⟩ := result
      simp only [used, Option.map_some] at agrees
      rw [← agrees]
      by_cases accepted : word.val < N
      · simp [accepted]
      · simp only [dite_eq_right accepted]
        have usedWidth := consumeCursorWord_position bits (uniformProposalWidth N) cursor next word used
        have fits := next.bounded
        have smaller : budget-next.position < budget-cursor.position := by omega
        rw [ih next smaller (rejected+1)]
        cases answer : consumeFairIndex N (cursorSuffix bits next) with
        | none => rfl
        | some output =>
          rcases output with ⟨⟨index,count⟩,rest⟩
          simp [Nat.add_comm, Nat.add_left_comm]

/-- Read a rejection sample from a finite bit cursor, preserving the rejection count. -/
def consumeCursorIndex {budget : ℕ} (bits : Fin budget → Bool) (N : ℕ) (cursor : BitCursor budget) :
    Option ((Fin N × ℕ) × BitCursor budget) :=
  if width : 0 < uniformProposalWidth N then consumeCursorIndexLoop bits N _ width cursor 0
  else if positive : 0 < N then some ((⟨0,positive⟩,0),cursor) else none

/-- The cursor and list rejection samplers agree, including on exhaustion. -/
theorem consumeCursorIndex_spec {budget : ℕ} (bits : Fin budget → Bool) (N : ℕ)
    (cursor : BitCursor budget) :
    (consumeCursorIndex bits N cursor).map (fun (value,next) => (value,cursorSuffix bits next)) =
      consumeFairIndex N (cursorSuffix bits cursor) := by
  by_cases width : 0 < uniformProposalWidth N
  · rw [consumeCursorIndex, dite_eq_left width, consumeCursorIndexLoop_spec]
    cases consumeFairIndex N (cursorSuffix bits cursor) with
    | none => rfl
    | some value => rcases value with ⟨⟨i,k⟩,r⟩; simp
  · rw [consumeCursorIndex, dite_eq_right width, consumeFairIndex, dite_eq_right width]
    by_cases positive : 0 < N <;> simp [positive]

/-- A successful rejection draw advances one full proposal per rejection,
then one more for the accepted proposal. -/
theorem consumeCursorIndex_position {budget : ℕ} (bits : Fin budget → Bool) (N : ℕ)
    {cursor next : BitCursor budget} {index : Fin N} {rejected : ℕ}
    (success : consumeCursorIndex bits N cursor = some ((index,rejected),next)) :
    next.position = cursor.position + uniformProposalWidth N*(rejected+1) := by
  have same := consumeCursorIndex_spec bits N cursor
  rw [success, Option.map_some] at same
  have lengths := (consumeFairIndex_suffix same.symm).1
  simp only [cursorSuffix, List.length_drop, List.length_ofFn] at lengths
  have start := cursor.bounded
  have finish := next.bounded
  omega

private def consumeCursorIndexLoopWithEnd {budget : ℕ} (bits : Fin budget → Bool) (N width : ℕ)
    (positive : 0 < width) (cursor : BitCursor budget) (rejected : ℕ) :
    Option (Fin N × ℕ) × BitCursor budget :=
  match used : consumeCursorWord bits width cursor with
  | none => (none,cursor)
  | some (word,next) =>
    if good : word.val < N then (some (⟨word.val,good⟩,rejected),next)
    else consumeCursorIndexLoopWithEnd bits N width positive next (rejected+1)
termination_by budget-cursor.position
decreasing_by
  have usedWidth := consumeCursorWord_position bits width cursor next word used
  have fits := next.bounded
  omega

private theorem consumeCursorIndexLoopWithEnd_spec {budget : ℕ} (bits : Fin budget → Bool)
    (N width : ℕ) (positive : 0 < width) (cursor : BitCursor budget) (rejected : ℕ) :
    let out := consumeCursorIndexLoopWithEnd bits N width positive cursor rejected
    out.1.map (·,out.2) = consumeCursorIndexLoop bits N width positive cursor rejected ∧
      (∃ k, out.2.position = cursor.position + width*k) ∧
      (out.1 = none → budget-out.2.position < width) := by
  induction cursor using (measure (fun c : BitCursor budget => budget-c.position)).wf.induction generalizing rejected with
  | h cursor ih =>
    dsimp only
    rw [consumeCursorIndexLoopWithEnd, consumeCursorIndexLoop]
    cases read : consumeCursorWord bits width cursor with
    | none =>
      have short : ¬cursor.position + width ≤ budget := by
        intro enough
        simp [consumeCursorWord, enough] at read
      have left := cursor.bounded
      simp only [Option.map_none, true_and, forall_const]
      exact ⟨⟨0,by simp⟩,by omega⟩
    | some answer =>
      obtain ⟨word,next⟩ := answer
      have widthUsed := consumeCursorWord_position bits width cursor next word read
      by_cases accepted : word.val < N
      · simp only [dite_eq_left accepted, Option.map_some, true_and, reduceCtorEq, false_implies, and_true]
        exact ⟨1,by simpa using widthUsed⟩
      · simp only [dite_eq_right accepted]
        have bounded := next.bounded
        have smaller : budget-next.position < budget-cursor.position := by omega
        obtain ⟨result,⟨k,position⟩,short⟩ := ih next smaller (rejected+1)
        refine ⟨result,⟨k+1,?_⟩,short⟩
        rw [position,widthUsed,Nat.mul_succ]
        omega

/-- A reference rejection sampler reports its final cursor even when it runs
out of complete proposal words. -/
def consumeCursorIndexWithEnd {budget : ℕ} (bits : Fin budget → Bool) (N : ℕ) (cursor : BitCursor budget) :
    Option (Fin N × ℕ) × BitCursor budget :=
  if width : 0 < uniformProposalWidth N then consumeCursorIndexLoopWithEnd bits N _ width cursor 0
  else if positive : 0 < N then (some (⟨0,positive⟩,0),cursor) else (none,cursor)

theorem consumeCursorIndexWithEnd_spec {budget : ℕ} (bits : Fin budget → Bool) (N : ℕ)
    (cursor : BitCursor budget) :
    let out := consumeCursorIndexWithEnd bits N cursor
    out.1.map (·,out.2) = consumeCursorIndex bits N cursor ∧
      (∃ k, out.2.position = cursor.position + uniformProposalWidth N*k) ∧
      (0 < uniformProposalWidth N → out.1 = none → budget-out.2.position < uniformProposalWidth N) := by
  by_cases width : 0 < uniformProposalWidth N
  · have spec := consumeCursorIndexLoopWithEnd_spec bits N _ width cursor 0
    dsimp only
    rw [consumeCursorIndexWithEnd, dite_eq_left width, consumeCursorIndex, dite_eq_left width]
    exact ⟨spec.1,spec.2.1,fun _ => spec.2.2⟩
  · by_cases positive : 0 < N
    · simp [consumeCursorIndexWithEnd, consumeCursorIndex, width, positive]
    · simp [consumeCursorIndexWithEnd, consumeCursorIndex, width, positive]

/-- When a positive-width sampler runs out, it has consumed every whole
proposal that fits, with fewer than one proposal's worth of bits left. -/
theorem consumeCursorIndexWithEnd_exhaustion_position {budget : ℕ} (bits : Fin budget → Bool)
    (N : ℕ) (cursor : BitCursor budget) (width : 0 < uniformProposalWidth N)
    (failure : consumeCursorIndex bits N cursor = none) :
    let out := consumeCursorIndexWithEnd bits N cursor
    out.2.position = cursor.position + uniformProposalWidth N*((budget-cursor.position)/uniformProposalWidth N) := by
  let out := consumeCursorIndexWithEnd bits N cursor
  obtain ⟨replay,⟨k,position⟩,endShort⟩ := consumeCursorIndexWithEnd_spec bits N cursor
  change out.1.map (·,out.2) = _ at replay
  change out.2.position = _ at position
  have failed : out.1 = none := by
    rw [failure] at replay
    cases answer : out.1 with
    | none => rfl
    | some value => simp [answer] at replay
  have short : budget-out.2.position < uniformProposalWidth N := endShort width failed
  have bounded := out.2.bounded
  have total : budget-cursor.position = (budget-out.2.position) + uniformProposalWidth N*k := by omega
  have words : (budget-cursor.position)/uniformProposalWidth N = k := by
    rw [total,Nat.add_mul_div_left _ _ width,Nat.div_eq_of_lt short,Nat.zero_add]
  change out.2.position = _
  rw [words]
  exact position

/-- On a word failure, the reader stops before using a partial word. -/
def consumeCursorWordWithEnd {budget : ℕ} (bits : Fin budget → Bool) (width : ℕ)
    (cursor : BitCursor budget) : Option (Fin (2^width)) × BitCursor budget :=
  match consumeCursorWord bits width cursor with
  | none => (none,cursor)
  | some (word,next) => (some word,next)

theorem consumeCursorWordWithEnd_spec {budget : ℕ} (bits : Fin budget → Bool) (width : ℕ)
    (cursor : BitCursor budget) :
    let out := consumeCursorWordWithEnd bits width cursor
    out.1.map (·,out.2) = consumeCursorWord bits width cursor ∧
      out.2.position = cursor.position + if out.1.isSome then width else 0 := by
  unfold consumeCursorWordWithEnd
  cases word : consumeCursorWord bits width cursor with
  | none => simp
  | some answer =>
    obtain ⟨value,next⟩ := answer
    exact ⟨rfl,consumeCursorWord_position bits width cursor next value word⟩

private def cursorWordAccumWithWork {budget : ℕ} (bits : Fin budget → Bool) :
    (width : ℕ) → (cursor : BitCursor budget) → ℕ → ℕ →
      (cursor.position + width ≤ budget) → ℕ × ℕ
  | 0, _, word, work, _ => (word,work+1)
  | width+1, cursor, word, work, enough =>
    let bit := bits ⟨cursor.position,by omega⟩
    let next : BitCursor budget := ⟨cursor.position+1,by omega⟩
    cursorWordAccumWithWork bits width next (2*word + if bit then 1 else 0) (work+8)
      (by dsimp [next]; omega)

private theorem cursorWordAccumWithWork_spec {budget : ℕ} (bits : Fin budget → Bool)
    (width : ℕ) (cursor : BitCursor budget) (word work : ℕ) (enough : cursor.position + width ≤ budget) :
    cursorWordAccumWithWork bits width cursor word work enough =
      (cursorWordAccum bits width cursor word enough,work+8*width+1) := by
  induction width generalizing cursor word work with
  | zero => simp [cursorWordAccumWithWork,cursorWordAccum]
  | succ width ih =>
    rw [cursorWordAccumWithWork,cursorWordAccum,ih]
    congr 1
    omega

/-- The cursor word reader with a unit work tally for bit reads, arithmetic,
branches, record construction, and loop steps. Its tally excludes maintenance of the tally itself. -/
def consumeCursorWordWithWork {budget : ℕ} (bits : Fin budget → Bool) (width : ℕ)
    (cursor : BitCursor budget) : (Option (Fin (2^width)) × BitCursor budget) × ℕ :=
  if enough : cursor.position + width ≤ budget then
    let read := cursorWordAccumWithWork bits width cursor 0 0 enough
    have bounded : read.1 < 2^width := by
      dsimp only [read]
      rw [cursorWordAccumWithWork_spec]
      simpa only [cursorWordAccum_eq, Nat.zero_mul, Nat.zero_add] using
        (uniformBitsEquiv width (cursorSlice bits cursor enough)).isLt
    ((some ⟨read.1,bounded⟩,⟨cursor.position+width,enough⟩),read.2+8)
  else ((none,cursor),5)

theorem consumeCursorWordWithWork_spec {budget : ℕ} (bits : Fin budget → Bool) (width : ℕ)
    (cursor : BitCursor budget) :
    let out := consumeCursorWordWithWork bits width cursor
    out.1 = consumeCursorWordWithEnd bits width cursor ∧
      out.1.2.position = cursor.position + (if out.1.1.isSome then width else 0) ∧
      out.2 ≤ 8*(out.1.2.position-cursor.position)+9 := by
  by_cases enough : cursor.position+width ≤ budget
  · simp [consumeCursorWordWithWork, consumeCursorWordWithEnd, consumeCursorWord, enough,
      cursorWordAccumWithWork_spec]
  · simp [consumeCursorWordWithWork, consumeCursorWordWithEnd, consumeCursorWord, enough]

private def consumeCursorIndexLoopWithWork {budget : ℕ} (bits : Fin budget → Bool) (N width : ℕ) :
    ℕ → BitCursor budget → ℕ → ℕ → (Option (Fin N × ℕ) × BitCursor budget) × ℕ
  | 0, cursor, _, work => ((none,cursor),work+3)
  | fuel+1, cursor, rejected, work =>
    let read := consumeCursorWordWithWork bits width cursor
    match read.1.1 with
    | none => ((none,read.1.2),work+read.2+5)
    | some word =>
      if good : word.val < N then ((some (⟨word.val,good⟩,rejected),read.1.2),work+read.2+5)
      else consumeCursorIndexLoopWithWork bits N width fuel read.1.2 (rejected+1) (work+read.2+7)

private theorem consumeCursorIndexLoopWithWork_spec {budget : ℕ} (bits : Fin budget → Bool)
    (N width : ℕ) (positive : 0 < width) (fuel : ℕ) (cursor : BitCursor budget) (rejected work : ℕ)
    (enough : budget-cursor.position < fuel) :
    let out := consumeCursorIndexLoopWithWork bits N width fuel cursor rejected work
    out.1 = consumeCursorIndexLoopWithEnd bits N width positive cursor rejected ∧
      cursor.position ≤ out.1.2.position ∧ out.2 ≤ work+24*(out.1.2.position-cursor.position)+14 := by
  induction fuel generalizing cursor rejected work with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨same,position,readWork⟩ := consumeCursorWordWithWork_spec bits width cursor
    dsimp only
    rw [consumeCursorIndexLoopWithWork, consumeCursorIndexLoopWithEnd]
    cases got : consumeCursorWord bits width cursor with
    | none =>
      have eq : (consumeCursorWordWithWork bits width cursor).1 = (none,cursor) := by
        simpa only [consumeCursorWordWithEnd, got] using same
      have wordEq : (consumeCursorWordWithWork bits width cursor).1.1 = none := congrArg Prod.fst eq
      have cursorEq : (consumeCursorWordWithWork bits width cursor).1.2 = cursor := congrArg Prod.snd eq
      simp only [wordEq, cursorEq, Nat.sub_self, Nat.mul_zero, Nat.zero_add] at readWork ⊢
      exact ⟨trivial,le_rfl,by omega⟩
    | some parsed =>
      obtain ⟨word,next⟩ := parsed
      have eq : (consumeCursorWordWithWork bits width cursor).1 = (some word,next) := by
        simpa only [consumeCursorWordWithEnd, got] using same
      have wordEq : (consumeCursorWordWithWork bits width cursor).1.1 = some word := congrArg Prod.fst eq
      have cursorEq : (consumeCursorWordWithWork bits width cursor).1.2 = next := congrArg Prod.snd eq
      simp only [wordEq, cursorEq, Option.isSome_some] at position readWork ⊢
      change next.position = cursor.position+width at position
      by_cases good : word.val < N
      · simp only [dite_eq_left good]
        exact ⟨trivial,by omega,by omega⟩
      · simp only [dite_eq_right good]
        have bounded := next.bounded
        have smaller : budget-next.position < fuel := by omega
        obtain ⟨agrees,progress,restWork⟩ := ih next (rejected+1) _ smaller
        exact ⟨agrees,by omega,by omega⟩

/-- Sample a finite index with the precomputed proposal width. Positive-width
retries each charge a complete word. A zero-width draw uses no bits. -/
def consumeCursorIndexAtWidthWithWork {budget : ℕ} (bits : Fin budget → Bool) (N width : ℕ)
    (cursor : BitCursor budget) : (Option (Fin N × ℕ) × BitCursor budget) × ℕ :=
  if 0 < width then
    let read := consumeCursorIndexLoopWithWork bits N width (budget-cursor.position+1) cursor 0 0
    (read.1,read.2+8)
  else if valid : 0 < N then ((some (⟨0,valid⟩,0),cursor),7) else ((none,cursor),6)

theorem consumeCursorIndexAtWidthWithWork_spec {budget : ℕ} (bits : Fin budget → Bool) (N width : ℕ)
    (cursor : BitCursor budget) (width_eq : width = uniformProposalWidth N) :
    let out := consumeCursorIndexAtWidthWithWork bits N width cursor
    out.1 = consumeCursorIndexWithEnd bits N cursor ∧
      cursor.position ≤ out.1.2.position ∧ out.2 ≤ 24*(out.1.2.position-cursor.position)+22 := by
  subst width
  by_cases positive : 0 < uniformProposalWidth N
  · obtain ⟨agrees,progress,work⟩ := consumeCursorIndexLoopWithWork_spec bits N _ positive
      (budget-cursor.position+1) cursor 0 0 (by omega)
    simp only [consumeCursorIndexAtWidthWithWork, consumeCursorIndexWithEnd, ite_eq_left positive, dite_eq_left positive]
    exact ⟨agrees,progress,by omega⟩
  · by_cases valid : 0 < N <;> simp [consumeCursorIndexAtWidthWithWork, consumeCursorIndexWithEnd, positive, valid]

end OnlineReachabilityPreservers
