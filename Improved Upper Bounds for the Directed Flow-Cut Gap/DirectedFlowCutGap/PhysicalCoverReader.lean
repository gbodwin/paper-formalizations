import DirectedFlowCutGap.OriginalStoreCorrectness
import DirectedFlowCutGap.RetainedGridState

/-!
# Reading the fractional dispatcher's retained output

The rounding controller needs the output tag and, for each cover, its
retained best row. These fields are read from the terminal heap. A proven
proper list has at most as many links as the heap has cells, so a cyclic
or malformed list cannot require unbounded traversal.
-/

namespace DirectedFlowCutGap.PhysicalCoverReader

open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
open FractionalCoverRawCore RetainedGridState

private theorem spine_unique {H : NaturalHeap} {root n m : ℕ}
    (a : IndexSpine H root n) (b : IndexSpine H root m) : n = m := by
  induction a generalizing m with
  | nil h =>
    cases b with
    | nil _ => rfl
    | cons h' _ => rw [h] at h'; cases Option.some.inj h'
  | @cons root first tail n h hs ih =>
    cases b with
    | nil h' => rw [h'] at h; cases Option.some.inj h
    | @cons _ first' tail' m h' hs' =>
      have he := Option.some.inj (h.symm.trans h')
      injection he with _ heq
      subst tail'
      rw [ih hs']

private theorem spine_addresses {H : NaturalHeap} {root k : ℕ} (h : IndexSpine H root k) :
    ∃ S : Finset ℕ, S ⊆ Finset.range H.length ∧ S.card = k + 1 ∧
      ∀ r ∈ S, ∃ i ≤ k, IndexSpine H r i := by
  induction h with
  | @nil root h =>
    refine ⟨{root}, ?_, by simp, ?_⟩
    · intro x hx
      have hx' : x = root := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp h).1
    · intro x hx
      have hx' : x = root := Finset.mem_singleton.mp hx
      subst x
      exact ⟨0, le_rfl, .nil h⟩
  | @cons root top tail k h ht ih =>
    obtain ⟨S, hS, hcard, hpaths⟩ := ih
    have hroot : root ∉ S := by
      intro hm
      obtain ⟨i, hi, hp⟩ := hpaths root hm
      have he := spine_unique (.cons h ht) hp
      omega
    refine ⟨insert root S, ?_, by rw [Finset.card_insert_of_notMem hroot, hcard], ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp h).1
      · exact hS hx
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨k + 1, le_rfl, .cons h ht⟩
      · obtain ⟨i, hi, hp⟩ := hpaths x hx
        exact ⟨i, hi.trans (Nat.le_succ _), hp⟩

theorem spine_short {H : NaturalHeap} {root k : ℕ} (h : IndexSpine H root k) :
    k < H.length := by
  obtain ⟨S, hS, hcard, _⟩ := spine_addresses h
  have hc := Finset.card_le_card hS
  rw [hcard, Finset.card_range] at hc
  exact Nat.lt_of_succ_le hc

def readList {A : Type} (H : NaturalHeap) (read : ℕ → Option A) : ℕ → ℕ → Option (List A)
  | 0, _ => none
  | fuel + 1, root =>
    match H[root]? with
    | some .nil => some []
    | some (.pair head tail) => do
      let a ← read head
      let rest ← readList H read fuel tail
      pure (a :: rest)
    | _ => none

private def readFlag (H : NaturalHeap) (root : ℕ) : Option Bool :=
  match H[root]? with
  | some (.flag b) => some b
  | _ => none

def readWord (H : NaturalHeap) (root : ℕ) : Option Bits :=
  readList H (readFlag H) H.length root

private theorem word_spine {H : NaturalHeap} {root : ℕ} {bs : Bits} (h : BoolList H root bs) :
    IndexSpine H root bs.length := by
  induction h with
  | nil hp => exact .nil hp
  | cons hp _ _ ih => exact .cons hp ih

private theorem word_read {H : NaturalHeap} {root : ℕ} {bs : Bits} (h : BoolList H root bs)
    (fuel : ℕ) (hf : bs.length < fuel) :
    readList H (readFlag H) fuel root = some bs := by
  induction h generalizing fuel with
  | nil hp =>
    cases fuel with
    | zero => simp at hf
    | succ fuel => simp [readList, hp]
  | @cons root head tail b bs hp hb hs ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have h' : bs.length < fuel := by simpa using hf
      simp [readList, hp, readFlag, hb, ih fuel h']

theorem readWord_eq {H : NaturalHeap} {root : ℕ} {bs : Bits} (h : BoolList H root bs) :
    readWord H root = some bs :=
  word_read h _ (spine_short (word_spine h))

def readFraction (H : NaturalHeap) (root : ℕ) : Option BinaryRational.Fraction := do
  let .pair n d ← H[root]? | none
  let num ← readWord H n
  let den ← readWord H d
  (BinaryRational.fromBits num den).1

theorem readFraction_eq {H : NaturalHeap} {root : ℕ} {r : BinaryRational.Fraction}
    (h : RationalComparisonProgram.Stored H root r) :
    readFraction H root = some r := by
  obtain ⟨n, d, hp, hn, hd⟩ := h
  have hz : (isZero r.den).1 ≠ true :=
    fun hh => (Nat.ne_of_gt r.den_pos) ((isZero_spec r.den).1.mp hh)
  cases r
  simp [readFraction, hp, readWord_eq hn, readWord_eq hd, BinaryRational.fromBits, hz]

private theorem row_spine {H : NaturalHeap} {root : ℕ} {xs : List BinaryRational.Fraction}
    (h : CanonicalRationalSum.StoredList H root xs) : IndexSpine H root xs.length := by
  induction h with
  | nil hp => exact .nil hp
  | cons hp _ _ ih => exact .cons hp ih

private theorem row_read {H : NaturalHeap} {root : ℕ} {xs : List BinaryRational.Fraction}
    (h : CanonicalRationalSum.StoredList H root xs) (fuel : ℕ) (hf : xs.length < fuel) :
    readList H (readFraction H) fuel root = some xs := by
  induction h generalizing fuel with
  | nil hp =>
    cases fuel with
    | zero => simp at hf
    | succ fuel => simp [readList, hp]
  | cons hp ha _ ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      simp [readList, hp, readFraction_eq ha, ih fuel (by simpa using hf)]

def readBest (n : ℕ) (H : NaturalHeap) (root : ℕ) : Option (RawRow n) := do
  let .pair _ next ← H[root]? | none
  let .pair best _ ← H[next]? | none
  let xs ← readList H (readFraction H) H.length best
  if h : xs.length = n then
    some (BinaryFractionalRows.decodeRow ⟨xs.toArray, by simpa using h⟩)
  else none

theorem readBest_eq {n : ℕ} {H : NaturalHeap} {root : ℕ} {s : BinaryFractionalCore.State n}
    (h : MinimumGuess.Result H root (some s)) :
    readBest n H root = some (BinaryFractionalRows.decodeRow s.best) := by
  obtain ⟨_, best, _, _, _, _, k1, _, _, _, hp, hb, _, _, _, _, hrow, _⟩ := h
  have hr := row_read hrow _ (spine_short (row_spine hrow))
  simp [readBest, hp, hb, hr]
  rfl

private theorem covers_spine {n : ℕ} {H : NaturalHeap} {root : ℕ}
    {ss : List (Option (BinaryFractionalCore.State n))}
    (h : GridFamily.StateList H root ss) : IndexSpine H root ss.length := by
  induction h with
  | nil hp => exact .nil hp
  | cons hp _ _ ih => exact .cons hp ih

private theorem covers_read {n : ℕ} {H : NaturalHeap} {root : ℕ}
    {ss : List (BinaryFractionalCore.State n)} (h : GridFamily.StateList H root (ss.map some))
    (fuel : ℕ) (hf : ss.length < fuel) :
    readList H (readBest n H) fuel root =
      some (ss.map (fun s => BinaryFractionalRows.decodeRow s.best)) := by
  induction ss generalizing root fuel with
  | nil =>
    cases h with
    | nil hp =>
      cases fuel with
      | zero => simp at hf
      | succ fuel => simp [readList, hp]
  | cons a ss ih =>
    cases h with
    | cons hp ha htail =>
      cases fuel with
      | zero => simp at hf
      | succ fuel =>
        simp [readList, hp, readBest_eq ha, ih htail _ (by simpa using hf)]

inductive Plan (n : ℕ) where
  | infeasible (d : Fin n × Fin n)
  | zero (a : Flags n)
  | covers (rows : List (RawRow n))
  | invalid

def plan {n : ℕ} : BinaryFractionalGuesses.Output n → Plan n
  | .infeasible d => .infeasible d
  | .zero a => .zero a
  | .covers ss => .covers (ss.map (fun s => BinaryFractionalRows.decodeRow s.state.best))
  | .invalid => .invalid

private def readPorts (n : ℕ) (source target : Bits) : Option (Fin n × Fin n) :=
  if h : value source < n ∧ value target < n then
    some (⟨value source, h.1⟩, ⟨value target, h.2⟩)
  else none

private theorem readPorts_label {n : ℕ} (s t : Fin n) :
    readPorts n (RowVertices.vertexLabel s) (RowVertices.vertexLabel t) = some (s, t) := by
  simp [readPorts, RowVertices.label_numeric, s.isLt, t.isLt]

def readPlan (n : ℕ) (H : NaturalHeap) (root : ℕ) : Option (Plan n) := do
  match H[root]? with
  | some .nil => some .invalid
  | some (.pair tag root) =>
    match H[tag]? with
    | some (.flag false) => do
      let .pair s t ← H[root]? | none
      let d ← readPorts n (← readWord H s) (← readWord H t)
      pure (.infeasible d)
    | some (.flag true) => do
      let a ← readWord H root
      if h : a.length = n then
        pure (.zero ⟨a.toArray, by simpa using h⟩)
      else none
    | some .nil => (readList H (readBest n H) H.length root).map Plan.covers
    | _ => none
  | _ => none

theorem readPlan_eq {n : ℕ} {H : NaturalHeap} {root : ℕ} {out : BinaryFractionalGuesses.Output n}
    (h : FinalDispatch.Output H root out) : readPlan n H root = some (plan out) := by
  cases out with
  | invalid =>
    have hv : H[root]? = some Cell.nil := h
    simp [readPlan, plan, hv]
  | infeasible d =>
    obtain ⟨tag, ports, hp, ht, s, t, hd, hs, ht'⟩ := h
    simp [readPlan, plan, hp, ht, hd, readWord_eq hs, readWord_eq ht',
      readPorts_label]
  | zero a =>
    obtain ⟨tag, mask, hp, ht, hm⟩ := h
    simp [readPlan, plan, hp, ht, readWord_eq hm]
    rfl
  | covers results =>
    obtain ⟨tag, states, hp, ht, hstates⟩ := h
    have hs : GridFamily.StateList H states ((results.map (fun r => r.state)).map some) := by
      rw [List.map_map]
      exact hstates
    have hf := spine_short (covers_spine hs)
    rw [List.length_map] at hf
    have hr := covers_read hs _ hf
    simp [readPlan, plan, hp, ht, hr, List.map_map, Function.comp_def]

end DirectedFlowCutGap.PhysicalCoverReader
