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

end OnlineReachabilityPreservers
