import Mathlib.Data.List.OfFn
import OnlineReachabilityPreservers.SteinerRetry

/-! Decoding fixed-width fair words and rejection samples from a finite bit list. -/

namespace OnlineReachabilityPreservers

/-- Consume one big-endian fair bit word, returning the unread suffix. -/
def consumeFairWord : (w : ℕ) → List Bool → Option (Fin (2^w) × List Bool)
  | 0, bits => some (0,bits)
  | _+1, [] => none
  | w+1, bit::bits => (consumeFairWord w bits).map fun (word,rest) =>
      (finCongr (pow_succ' 2 w).symm (finProdFinEquiv (finTwoEquiv.symm bit,word)), rest)

private def consumeWordAccum : ℕ → ℕ → List Bool → Option (ℕ × List Bool)
  | 0, word, bits => some (word,bits)
  | _+1, _, [] => none
  | n+1, word, b::rest => consumeWordAccum n (2*word + if b then 1 else 0) rest

private theorem consumeWordAccum_eq (n word : ℕ) (bits : List Bool) :
    consumeWordAccum n word bits = (consumeFairWord n bits).map (fun (suffix,rest) => (word*2^n + suffix.val,rest)) := by
  induction n generalizing word bits with
  | zero => simp [consumeWordAccum, consumeFairWord]
  | succ n ih =>
    cases bits with
    | nil => rfl
    | cons b rest =>
      simp only [consumeWordAccum, consumeFairWord, ih]
      cases consumeFairWord n rest with
      | none => rfl
      | some output =>
        obtain ⟨suffix,remaining⟩ := output
        cases b <;> simp [finProdFinEquiv, finTwoEquiv, pow_succ] <;> ring

/-- Run the same big-endian word reader using shift and add. -/
def consumeFairWordTail (width : ℕ) (bits : List Bool) : Option (Fin (2^width) × List Bool) :=
  match consumed : consumeWordAccum width 0 bits with
  | none => none
  | some (word,rest) => some (⟨word, by
      have eq := consumeWordAccum_eq width 0 bits
      rw [consumed] at eq
      cases read : consumeFairWord width bits with
      | none => simp [read] at eq
      | some output =>
        obtain ⟨value,suffix⟩ := output
        simp [read] at eq
        simp [eq.1]⟩,rest)

@[csimp] theorem consumeFairWord_eq_tail : consumeFairWord = consumeFairWordTail := by
  funext width bits
  unfold consumeFairWordTail
  have eq := consumeWordAccum_eq width 0 bits
  split
  · rename_i consumed
    rw [consumed] at eq
    cases read : consumeFairWord width bits <;> simp [read] at eq ⊢
  · rename_i word rest consumed
    rw [consumed] at eq
    cases read : consumeFairWord width bits with
    | none => simp [read] at eq
    | some output =>
      obtain ⟨value,suffix⟩ := output
      simp [read] at eq
      apply congrArg some
      exact Prod.ext (Fin.ext eq.1.symm) eq.2.symm

theorem consumeFairWord_ofFn {w : ℕ} (word : Fin w → Bool) (rest : List Bool) :
    consumeFairWord w (List.ofFn word ++ rest) = some (uniformBitsEquiv w word, rest) := by
  induction w with
  | zero => simp [consumeFairWord, uniformBitsEquiv]
  | succ w ih =>
    rw [List.ofFn_succ, List.cons_append, consumeFairWord, ih]
    rfl

theorem consumeFairWord_suffix {w : ℕ} {bits rest : List Bool} {word : Fin (2^w)}
    (reads : consumeFairWord w bits = some (word,rest)) :
    rest.length + w = bits.length ∧ bits.drop w = rest := by
  induction w generalizing bits rest with
  | zero =>
    simp [consumeFairWord] at reads
    simp [← reads.2]
  | succ w ih =>
    cases bits with
    | nil => simp [consumeFairWord] at reads
    | cons b bits =>
      cases h : consumeFairWord w bits with
      | none => simp [consumeFairWord,h] at reads
      | some output =>
        rcases output with ⟨value,suffix⟩
        simp [consumeFairWord,h] at reads
        obtain ⟨len,drop⟩ := ih h
        constructor
        · simp [← reads.2]
          omega
        · simpa only [List.drop_succ_cons, ← reads.2] using drop

/-- Sequential rejection sampling for a finite supplied prefix. Return the
index, the number of rejections, and the unread suffix. Missing bits or an
empty range give no result. A singleton needs no bits. -/
def consumeFairIndex (N : ℕ) (bits : List Bool) : Option ((Fin N × ℕ) × List Bool) :=
  if _width : 0 < uniformProposalWidth N then
    match _consumed : consumeFairWord (uniformProposalWidth N) bits with
    | none => none
    | some (word,rest) =>
        if bound : word.val < N then some ((⟨word.val,bound⟩,0),rest)
        else (consumeFairIndex N rest).map fun ((i,k),rest) => ((i,k+1),rest)
  else if positive : 0 < N then some ((⟨0,positive⟩,0),bits) else none
termination_by bits.length
decreasing_by
  have length := (consumeFairWord_suffix _consumed).1
  omega

private def consumeFairIndexLoop (N width : ℕ) (positive : 0 < width) (bits : List Bool) (rejected : ℕ) :
    Option ((Fin N × ℕ) × List Bool) :=
  match consumed : consumeFairWord width bits with
  | none => none
  | some (word,rest) =>
    if bound : word.val < N then some ((⟨word.val,bound⟩,rejected),rest)
    else consumeFairIndexLoop N width positive rest (rejected+1)
termination_by bits.length
decreasing_by
  have length := (consumeFairWord_suffix consumed).1
  omega

private theorem consumeFairIndexLoop_eq (N : ℕ) (positive : 0 < uniformProposalWidth N) (bits : List Bool)
    (rejected : ℕ) :
    consumeFairIndexLoop N (uniformProposalWidth N) positive bits rejected =
      (consumeFairIndex N bits).map (fun ((index,count),rest) => ((index,count+rejected),rest)) := by
  induction bits using (measure List.length).wf.induction generalizing rejected with
  | h bits ih =>
    rw [consumeFairIndexLoop, consumeFairIndex, dite_eq_left positive]
    cases read : consumeFairWord (uniformProposalWidth N) bits with
    | none => simp
    | some result =>
      obtain ⟨word, rest⟩ := result
      by_cases accepted : word.val < N
      · simp [accepted]
      · simp only [dite_eq_right accepted]
        have length := (consumeFairWord_suffix read).1
        rw [ih rest (by change rest.length < bits.length; omega) (rejected+1)]
        cases consumeFairIndex N rest with
        | none => rfl
        | some output =>
          rcases output with ⟨⟨index,count⟩,suffix⟩
          simp [Nat.add_left_comm, Nat.add_comm]

/-- The rejection loop threads its count as an accumulator. -/
def consumeFairIndexTail (N : ℕ) (bits : List Bool) : Option ((Fin N × ℕ) × List Bool) :=
  if positive : 0 < uniformProposalWidth N then consumeFairIndexLoop N _ positive bits 0
  else if positive : 0 < N then some ((⟨0,positive⟩,0),bits) else none

@[csimp] theorem consumeFairIndex_eq_tail : consumeFairIndex = consumeFairIndexTail := by
  funext N bits
  unfold consumeFairIndexTail
  by_cases positive : 0 < uniformProposalWidth N
  · rw [dite_eq_left positive, consumeFairIndexLoop_eq]
    cases consumeFairIndex N bits with
    | none => rfl
    | some result => rcases result with ⟨⟨index,count⟩,suffix⟩; simp
  · rw [dite_eq_right positive, consumeFairIndex, dite_eq_right positive]

theorem consumeFairIndex_ofFn {N : ℕ} (positive : 0 < N)
    (word : Fin (uniformProposalWidth N) → Bool) (rest : List Bool) :
    consumeFairIndex N (List.ofFn word ++ rest) =
      let index := uniformBitsEquiv (uniformProposalWidth N) word
      if bound : index.val < N then some ((⟨index.val,bound⟩,0),rest)
      else (consumeFairIndex N rest).map fun ((i,k),s) => ((i,k+1),s) := by
  rw [consumeFairIndex]
  by_cases width : 0 < uniformProposalWidth N
  · rw [dite_eq_left width]
    split
    · rename_i bad
      rw [consumeFairWord_ofFn] at bad
      contradiction
    · rename_i value suffix eq
      have same := Option.some.inj ((consumeFairWord_ofFn word rest).symm.trans eq)
      cases same
      rfl
  · have zero : uniformProposalWidth N = 0 := by omega
    have nil : List.ofFn word = [] := List.length_eq_zero_iff.mp (by simp [zero])
    have val : (uniformBitsEquiv (uniformProposalWidth N) word).val = 0 := by
      have h := (uniformBitsEquiv (uniformProposalWidth N) word).isLt
      exact Nat.lt_one_iff.mp (h.trans_le (by simp [zero]))
    simp [width, positive, nil, val]

private theorem fairBitRetry_cons {N : ℕ} (word : Fin (uniformProposalWidth N) → Bool)
    (rest : List (Fin (uniformProposalWidth N) → Bool)) :
    fairBitRetry N (word::rest) =
      let index := uniformBitsEquiv (uniformProposalWidth N) word
      if bound : index.val < N then some (⟨index.val,bound⟩,1)
      else (fairBitRetry N rest).map fun (i,k) => (i,k+1) := rfl

/-- Flattening consecutive words and supplying them to the single-bit
reader preserves both the first accepted index and its rejection count. -/
private theorem consumeFairIndex_last {N : ℕ} (positive : 0 < N)
    (words : List (Fin (uniformProposalWidth N) → Bool))
    (last : Fin (uniformProposalWidth N) → Bool) (target : Fin N) (rest : List Bool) :
    consumeFairIndex N ((words++[last]).flatMap List.ofFn ++ rest) =
      some ((target,words.length),rest) ↔
      fairBitRetry N (words++[last]) = some (target,words.length+1) := by
  induction words with
  | nil =>
    rw [List.nil_append, List.flatMap_singleton, consumeFairIndex_ofFn positive, fairBitRetry_cons]
    have empty : fairBitRetry N [] = none := rfl
    by_cases passes : (uniformBitsEquiv _ last).val < N
    · simp [passes]
    · cases consumeFairIndex N rest <;> simp [passes, empty]
  | cons word words ih =>
    rw [List.cons_append, List.flatMap_cons, List.append_assoc, consumeFairIndex_ofFn positive,
      fairBitRetry_cons]
    dsimp only
    by_cases passes : (uniformBitsEquiv _ word).val < N
    · simp [passes]
    · rw [dite_eq_right passes, dite_eq_right passes]
      have decoded : ((consumeFairIndex N ((words++[last]).flatMap List.ofFn ++ rest)).map
            fun ((i,k),s) => ((i,k+1),s)) = some ((target,words.length+1),rest) ↔
          consumeFairIndex N ((words++[last]).flatMap List.ofFn ++ rest) =
            some ((target,words.length),rest) := by
        cases consumeFairIndex N ((words++[last]).flatMap List.ofFn ++ rest) with
        | none => simp
        | some value =>
          rcases value with ⟨⟨i,k⟩,s⟩
          simp
      have retried : ((fairBitRetry N (words++[last])).map fun (i,k) => (i,k+1)) =
            some (target,words.length+1+1) ↔
          fairBitRetry N (words++[last]) = some (target,words.length+1) := by
        cases fairBitRetry N (words++[last]) with
        | none => simp
        | some value =>
          rcases value with ⟨i,k⟩
          simp
      rw [List.length_cons, decoded, retried, ih]

private def consecutiveBitWords (m w : ℕ) : (Fin (m*w) → Bool) ≃ (Fin m → Fin w → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

private theorem consecutiveBitWords_flatten {m w : ℕ} (bits : Fin (m*w) → Bool) :
    (List.ofFn (consecutiveBitWords m w bits)).flatMap List.ofFn = List.ofFn bits := by
  rw [List.flatMap_def, List.map_ofFn, List.ofFn_mul bits]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  unfold consecutiveBitWords
  change bits (finProdFinEquiv (i,j)) = _
  congr 1
  apply Fin.ext
  change j.val + w*i.val = i.val*w + j.val
  ac_rfl

/-- On a flat prefix of k+1 words, the stream reader returns on the last
word exactly on the checked independent-word first-success event. -/
private theorem consumeFairIndex_stream_event {N : ℕ} (positive : 0 < N) (k : ℕ) (target : Fin N)
    (bits : Fin ((k+1)*uniformProposalWidth N) → Bool) (rest : List Bool) :
    consumeFairIndex N (List.ofFn bits ++ rest) = some ((target,k),rest) ↔
      consecutiveBitWords (k+1) (uniformProposalWidth N) bits ∈ fairBitRetryLastEvent k target := by
  classical
  let words := consecutiveBitWords (k+1) (uniformProposalWidth N) bits
  change _ ↔ words ∈ fairBitRetryLastEvent k target
  simp only [fairBitRetryLastEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← consecutiveBitWords_flatten bits]
  change consumeFairIndex N ((List.ofFn words).flatMap List.ofFn ++ rest) = some ((target,k),rest) ↔ _
  rw [List.ofFn_succ_last]
  simpa only [List.length_ofFn] using consumeFairIndex_last positive (List.ofFn fun j : Fin k =>
    words j.castSucc) (words (Fin.last k)) target rest

noncomputable def flatBitRetryLastEvent {N : ℕ} (k : ℕ) (target : Fin N) (rest : List Bool) :
    Finset (Fin ((k+1)*uniformProposalWidth N) → Bool) := by
  classical
  exact Finset.univ.filter fun bits =>
    consumeFairIndex N (List.ofFn bits ++ rest) = some ((target,k),rest)

theorem flatBitRetryLastEvent_probability {N : ℕ} (positive : 0 < N)
    (k : ℕ) (target : Fin N) (rest : List Bool) :
    finiteProbability (flatBitRetryLastEvent k target rest) =
      finiteProbability (fairBitRetryLastEvent k target) := by
  classical
  let e := consecutiveBitWords (k+1) (uniformProposalWidth N)
  have same : flatBitRetryLastEvent k target rest =
      (fairBitRetryLastEvent k target).map e.symm.toEmbedding := by
    ext bits
    simp only [flatBitRetryLastEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      consumeFairIndex_stream_event positive]
    exact ⟨fun h => Finset.mem_map.mpr ⟨e bits,h,e.symm_apply_apply _⟩, fun h => by
      obtain ⟨words,member,eq⟩ := Finset.mem_map.mp h
      change e.symm words = bits at eq
      rw [← eq, e.apply_symm_apply]
      exact member⟩
  simp only [same, finiteProbability, Finset.card_map, Fintype.card_congr e]

/-- A first-success event gives the same result and count with any unread suffix. -/
theorem flatBitRetryLastEvent_read {N : ℕ} (positive : 0 < N)
    {k : ℕ} {target : Fin N} {bits : Fin ((k+1)*uniformProposalWidth N) → Bool} (rest : List Bool) :
    consumeFairIndex N (List.ofFn bits ++ rest) = some ((target,k),rest) ↔
      bits ∈ flatBitRetryLastEvent k target [] := by
  classical
  simp only [flatBitRetryLastEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (consumeFairIndex_stream_event positive k target bits rest).trans
    (consumeFairIndex_stream_event positive k target bits []).symm

/-- A flat fair-bit prefix gives the uniform law by summing all of its
disjoint first-success events. The unread suffix is arbitrary. -/
theorem flatBitRetry_uniform {N : ℕ} (positive : 0 < N) (target : Fin N) (rest : List Bool) :
    (∑' k, finiteProbability (flatBitRetryLastEvent k target rest)) = 1/(N:ℝ) := by
  simp_rw [flatBitRetryLastEvent_probability positive]
  exact fairBitRetry_uniform positive target

theorem flatBitRetry_expectedBits_eq {N : ℕ} (positive : 0 < N) (rest : List Bool) :
    (∑' k : ℕ, (uniformProposalWidth N : ℝ)*(k+1)*
      (∑ t : Fin N, finiteProbability (flatBitRetryLastEvent k t rest))) = expectedRejectionBits N := by
  simp_rw [flatBitRetryLastEvent_probability positive]
  exact fairBitRetry_expectedBits_eq positive

/-- On success the reader consumes exactly one full word for each
rejection and one more for its accepted index. -/
theorem consumeFairIndex_suffix {N k : ℕ} {target : Fin N} {bits rest : List Bool}
    (reads : consumeFairIndex N bits = some ((target,k),rest)) :
    rest.length + uniformProposalWidth N * (k+1) = bits.length ∧
      bits.drop (uniformProposalWidth N * (k+1)) = rest := by
  fun_induction consumeFairIndex N bits generalizing target k rest with
  | case1 => simp at reads
  | case2 =>
    rename_i original wide proposal suffix consumed accepted
    simp at reads
    obtain ⟨⟨_,rfl⟩,rfl⟩ := reads
    simpa using consumeFairWord_suffix consumed
  | case3 =>
    rename_i original wide proposal suffix consumed rejected ih
    simp at reads
    obtain ⟨prior,success,rfl⟩ := reads
    obtain ⟨length,drop⟩ := ih success
    obtain ⟨comp,step⟩ := consumeFairWord_suffix consumed
    constructor
    · rw [Nat.mul_succ]
      omega
    · rw [← drop, ← step, List.drop_drop, Nat.mul_succ, Nat.add_comm]
  | case4 =>
    rename_i original width positive
    have zero : uniformProposalWidth N = 0 := by omega
    simp at reads
    obtain ⟨⟨_,rfl⟩,rfl⟩ := reads
    simp [zero]
  | case5 => simp at reads

end OnlineReachabilityPreservers
