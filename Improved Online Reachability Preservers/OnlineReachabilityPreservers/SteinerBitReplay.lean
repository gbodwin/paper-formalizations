import OnlineReachabilityPreservers.SteinerBitSeed
import OnlineReachabilityPreservers.SteinerDistanceReplay

/-! The complete decoder on uniformly chosen bit prefixes and its connection to prefix replay. -/

namespace OnlineReachabilityPreservers

private def concatenateBitRows {n : ℕ} {width : Fin n → ℕ} (words : ∀ i, Fin (width i) → Bool) : List Bool :=
  (List.ofFn fun i => List.ofFn (words i)).flatten

private theorem concatenateBitRows_length {n : ℕ} {width : Fin n → ℕ} (words : ∀ i, Fin (width i) → Bool) :
    (concatenateBitRows words).length = ∑ i, width i := by
  simp only [concatenateBitRows, List.length_flatten, List.map_ofFn, Function.comp_def, List.length_ofFn,
    List.sum_ofFn]

private theorem concatenateBitRows_succ {n : ℕ} {width : Fin (n+1) → ℕ}
    (words : ∀ i, Fin (width i) → Bool) :
    concatenateBitRows words = List.ofFn (words 0) ++ concatenateBitRows (fun i => words i.succ) := by
  rw [concatenateBitRows, List.ofFn_succ, List.flatten_cons]
  rfl

private theorem concatenateBitRows_injective (n : ℕ) (width : Fin n → ℕ) :
    Function.Injective (concatenateBitRows (width := width)) := by
  induction n with
  | zero => exact fun _ _ _ => funext (fun i => i.elim0)
  | succ n ih =>
    intro left right same
    rw [concatenateBitRows_succ, concatenateBitRows_succ] at same
    have take := congrArg (List.take (width 0)) same
    have takeLeft : (List.ofFn (left 0) ++ concatenateBitRows (fun i => left i.succ)).take (width 0) =
        List.ofFn (left 0) := by
      simpa only [List.length_ofFn] using
        (List.take_append_length (l₁ := List.ofFn (left 0)) (l₂ := concatenateBitRows (fun i => left i.succ)))
    have takeRight : (List.ofFn (right 0) ++ concatenateBitRows (fun i => right i.succ)).take (width 0) =
        List.ofFn (right 0) := by
      simpa only [List.length_ofFn] using
        (List.take_append_length (l₁ := List.ofFn (right 0)) (l₂ := concatenateBitRows (fun i => right i.succ)))
    have first := List.ofFn_injective (takeLeft.symm.trans (take.trans takeRight))
    rw [first, List.append_cancel_left_eq] at same
    have rest := ih (fun i => width i.succ) same
    exact funext (Fin.cases first (fun i => congrFun rest i))

private theorem concatenateBitRows_surjective (n : ℕ) (width : Fin n → ℕ) (bits : List Bool)
    (len : bits.length = ∑ i, width i) :
    ∃ words : ∀ i, Fin (width i) → Bool, concatenateBitRows words = bits := by
  induction n generalizing bits with
  | zero =>
    have empty : bits = [] := List.length_eq_zero_iff.mp (by simpa using len)
    exact ⟨fun i => i.elim0, by simp [concatenateBitRows, empty]⟩
  | succ n ih =>
    rw [Fin.sum_univ_succ] at len
    have h : (bits.take (width 0)).length = width 0 := List.length_take_of_le (by omega)
    have d : (bits.drop (width 0)).length = ∑ i : Fin n, width i.succ := by simp [len]
    obtain ⟨rest,matched⟩ := ih (fun i => width i.succ) (bits.drop (width 0)) d
    let first : Fin (width 0) → Bool := fun i => (bits.take (width 0)).get (Fin.cast h.symm i)
    refine ⟨Fin.cases first rest, ?_⟩
    rw [concatenateBitRows_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, matched]
    have chunk : List.ofFn first = bits.take (width 0) := by
      rw [← List.ofFn_get (bits.take (width 0))]
      exact (List.ofFn_congr h _).symm
    rw [chunk, List.take_append_drop]

/-- Fair arrays of consecutive fixed-width rows encode exactly the same
finite prefixes as raw bits of their total length. -/
private noncomputable def bitRowsEquiv (n : ℕ) (width : Fin n → ℕ) :
    (∀ i, Fin (width i) → Bool) ≃ {bits : List Bool // bits.length = ∑ i, width i} :=
  Equiv.ofBijective (fun words => ⟨concatenateBitRows words, concatenateBitRows_length words⟩)
    ⟨fun _ _ pair => concatenateBitRows_injective n width (congrArg Subtype.val pair), fun bits => by
      obtain ⟨words, matched⟩ := concatenateBitRows_surjective n width bits.val bits.property
      exact ⟨words,Subtype.ext matched⟩⟩

private def appendSizedBits (a b : ℕ) :
    {bits : List Bool // bits.length = a} × {bits : List Bool // bits.length = b} ≃
      {bits : List Bool // bits.length = a+b} where
  toFun bits := ⟨bits.1.val ++ bits.2.val, by simp [bits.1.property,bits.2.property]⟩
  invFun bits :=
    (⟨bits.val.take a, List.length_take_of_le (bits.property.symm ▸ Nat.le_add_right a b)⟩,
      ⟨bits.val.drop a, by simp [bits.property]⟩)
  left_inv bits := Prod.ext (Subtype.ext (by
      simpa only [bits.1.property] using List.take_append_length (l₁ := bits.1.val) (l₂ := bits.2.val)))
    (Subtype.ext (by
      simpa only [bits.1.property] using List.drop_append_length (l₁ := bits.1.val) (l₂ := bits.2.val)))
  right_inv bits := Subtype.ext (List.take_append_drop a bits.val)

private def sizedBitsEquiv (n : ℕ) : (Fin n → Bool) ≃ {bits : List Bool // bits.length = n} where
  toFun words := ⟨List.ofFn words,List.length_ofFn⟩
  invFun bits := fun i => bits.val.get (Fin.cast bits.property.symm i)
  left_inv words := funext fun i => List.getElem_ofFn ..
  right_inv bits := Subtype.ext (by
    rw [← List.ofFn_get bits.val]
    exact (List.ofFn_congr bits.property _).symm)

private noncomputable def bitRowsTripleEquiv {n m p : ℕ} (first : Fin n → ℕ) (second : Fin m → ℕ)
    (third : Fin p → ℕ) :
    ((∀ i, Fin (first i) → Bool) × (∀ i, Fin (second i) → Bool) × (∀ i, Fin (third i) → Bool)) ≃
      (Fin ((∑ i, first i) + ((∑ i, second i) + ∑ i, third i)) → Bool) :=
  let a := ∑ i, first i
  let b := ∑ i, second i
  let c := ∑ i, third i
  let rest := (bitRowsEquiv m second).prodCongr (bitRowsEquiv p third)
  ((bitRowsEquiv n first).prodCongr (rest.trans (appendSizedBits b c))).trans
    ((appendSizedBits a (b+c)).trans ((sizedBitsEquiv (a+(b+c))).symm))

private theorem bitRowsTripleEquiv_ofFn {n m p : ℕ} {first : Fin n → ℕ} {second : Fin m → ℕ}
    {third : Fin p → ℕ} (input : (∀ i, Fin (first i) → Bool) × (∀ i, Fin (second i) → Bool) ×
      (∀ i, Fin (third i) → Bool)) :
    List.ofFn (bitRowsTripleEquiv first second third input) =
      concatenateBitRows input.1 ++ (concatenateBitRows input.2.1 ++ concatenateBitRows input.2.2) := by
  let n := (∑ i, first i) + ((∑ i, second i) + ∑ i, third i)
  let list := concatenateBitRows input.1 ++ (concatenateBitRows input.2.1 ++ concatenateBitRows input.2.2)
  have len : list.length = n := by simp [list,n,concatenateBitRows_length]
  exact congrArg Subtype.val ((sizedBitsEquiv n).apply_symm_apply ⟨list,len⟩)

variable {V : Type*} [LinearOrder V] [Fintype V]

def completeSteinerBitSeedWidth (G : Arcs V) (height : ℕ) (arcs : G ≃ Fin G.card)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ) : ℕ :=
  (∑ _ : Fin (Fintype.card (EarlySeedCoordinate G height)), ((forestScale G height).log2+1)) +
    ((∑ i, (hubRejects i+1)*uniformProposalWidth (Fintype.card V)) +
      ∑ i : Fin G.card, (thinRejects (arcs.symm i)+1)*uniformProposalWidth G.card)

/-- The first-success event for the complete decoder, expressed directly
as uniform raw bit prefixes of the length prescribed by the rejection counts. -/
noncomputable def completeSteinerRawSeedEvent (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ) (rest : List Bool) :
    Finset (Fin (completeSteinerBitSeedWidth G height arcs hubRejects thinRejects) → Bool) := by
  classical
  exact Finset.univ.filter fun bits =>
    decodeCompleteSteinerSeed G height coordinates vertices arcs (List.ofFn bits ++ rest) =
      some ((early,hubs,thin),(hubRejects,thinRejects),rest)

private noncomputable def steinerBitSeedPacking (G : Arcs V) (height : ℕ) (arcs : G ≃ Fin G.card)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ) :
    ((Fin (Fintype.card (EarlySeedCoordinate G height)) → Fin ((forestScale G height).log2+1) → Bool) ×
      (∀ i, Fin ((hubRejects i+1)*uniformProposalWidth (Fintype.card V)) → Bool) ×
      (∀ i, Fin ((thinRejects (arcs.symm i)+1)*uniformProposalWidth G.card) → Bool)) ≃
      (Fin (completeSteinerBitSeedWidth G height arcs hubRejects thinRejects) → Bool) :=
  bitRowsTripleEquiv (fun _ : Fin (Fintype.card (EarlySeedCoordinate G height)) =>
    (forestScale G height).log2+1) (fun i => (hubRejects i+1)*uniformProposalWidth (Fintype.card V))
    (fun i => (thinRejects (arcs.symm i)+1)*uniformProposalWidth G.card)

private theorem completeSteinerRawSeedEvent_map (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ) (rest : List Bool) :
    completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin hubRejects thinRejects rest =
      (completeSteinerBitSeedEvent G height coordinates vertices arcs early hubs thin hubRejects thinRejects rest).map
        (steinerBitSeedPacking G height arcs hubRejects thinRejects).toEmbedding := by
  classical
  let e := steinerBitSeedPacking G height arcs hubRejects thinRejects
  let chunked := completeSteinerBitSeedEvent G height coordinates vertices arcs early hubs thin
    hubRejects thinRejects rest
  have member (input) : e input ∈ completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin
      hubRejects thinRejects rest ↔ input ∈ chunked := by
    simp only [completeSteinerRawSeedEvent, chunked, completeSteinerBitSeedEvent, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have flat := bitRowsTripleEquiv_ofFn
      (first := fun _ : Fin (Fintype.card (EarlySeedCoordinate G height)) => (forestScale G height).log2+1)
      (second := fun i => (hubRejects i+1)*uniformProposalWidth (Fintype.card V))
      (third := fun i => (thinRejects (arcs.symm i)+1)*uniformProposalWidth G.card) input
    change List.ofFn (e input) = _ at flat
    rw [flat]
    rcases input with ⟨_,_,_⟩
    simp only [concatenateBitRows, List.append_assoc]
  change _ = chunked.map e.toEmbedding
  ext bits
  refine ⟨fun good => Finset.mem_map.mpr ⟨e.symm bits, (member (e.symm bits)).mp ?_, e.apply_symm_apply _⟩, ?_⟩
  · rw [e.apply_symm_apply]
    exact good
  · intro inMap
    obtain ⟨input, good, eq⟩ := Finset.mem_map.mp inMap
    change e input = bits at eq
    rw [← eq]
    exact (member input).mpr good

theorem completeSteinerRawSeedEvent_probability (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ) (rest : List Bool) :
    finiteProbability (completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin
      hubRejects thinRejects rest) =
    finiteProbability (completeSteinerBitSeedEvent G height coordinates vertices arcs early hubs thin
      hubRejects thinRejects rest) := by
  rw [completeSteinerRawSeedEvent_map]
  simp only [finiteProbability, Finset.card_map,
    ← Fintype.card_congr (steinerBitSeedPacking G height arcs hubRejects thinRejects)]

theorem completeSteinerRawSeedEvent_suffix_eq (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ) (rest tail : List Bool) :
    completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin hubRejects thinRejects rest =
      completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin hubRejects thinRejects tail := by
  rw [completeSteinerRawSeedEvent_map, completeSteinerRawSeedEvent_map,
    completeSteinerBitSeedEvent_suffix_eq G height coordinates vertices arcs early hubs thin hubRejects thinRejects rest tail]

private theorem completeSteinerBitSeedWidth_eq (G : Arcs V) (height : ℕ) (arcs : G ≃ Fin G.card)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ) :
    completeSteinerBitSeedWidth G height arcs hubRejects thinRejects = earlySeedBits G height +
      (∑ i, uniformProposalWidth (Fintype.card V)*(hubRejects i+1)) +
      (∑ e, uniformProposalWidth G.card*(thinRejects e+1)) := by
  have early : (∑ _ : Fin (Fintype.card (EarlySeedCoordinate G height)), ((forestScale G height).log2+1)) =
      earlySeedBits G height := by simp [earlySeedBits]
  have thin : (∑ i : Fin G.card, (thinRejects (arcs.symm i)+1)*uniformProposalWidth G.card) =
      ∑ e, uniformProposalWidth G.card*(thinRejects e+1) :=
    Fintype.sum_equiv arcs.symm _ _ (fun i => Nat.mul_comm _ _)
  rw [completeSteinerBitSeedWidth, early, thin]
  simp only [Nat.mul_comm, Nat.add_assoc]

/-- A successful decoding leaves additional input unread. -/
theorem decodeCompleteSteinerSeed_append (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) {bits rest : List Bool}
    {early : EarlyRoundSample G height} {hubs : Fin (completeSteinerHubCount V) → V} {thin : ThinSample G}
    {hubRejects : Fin (completeSteinerHubCount V) → ℕ} {thinRejects : G → ℕ} (tail : List Bool)
    (done : decodeCompleteSteinerSeed G height coordinates vertices arcs bits =
      some ((early,hubs,thin),(hubRejects,thinRejects),rest)) :
    decodeCompleteSteinerSeed G height coordinates vertices arcs (bits ++ tail) =
      some ((early,hubs,thin),(hubRejects,thinRejects),rest ++ tail) := by
  classical
  have usage := decodeCompleteSteinerSeed_suffix G height coordinates vertices arcs done
  dsimp only at usage
  rw [← completeSteinerBitSeedWidth_eq G height arcs hubRejects thinRejects] at usage
  let n := completeSteinerBitSeedWidth G height arcs hubRejects thinRejects
  have length : (bits.take n).length = n := List.length_take_of_le (by omega)
  let consumed := (sizedBitsEquiv n).symm ⟨bits.take n,length⟩
  have head : List.ofFn consumed = bits.take n :=
    congrArg Subtype.val ((sizedBitsEquiv n).apply_symm_apply ⟨bits.take n,length⟩)
  have split : List.ofFn consumed ++ rest = bits := by
    rw [head, ← usage.2, List.take_append_drop]
  have old : consumed ∈ completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin
      hubRejects thinRejects rest := by
    simp only [completeSteinerRawSeedEvent, Finset.mem_filter, Finset.mem_univ, true_and, split, done]
  have next : consumed ∈ completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin
      hubRejects thinRejects (rest ++ tail) := by
    rwa [← completeSteinerRawSeedEvent_suffix_eq G height coordinates vertices arcs early hubs thin
      hubRejects thinRejects rest (rest ++ tail)]
  simpa only [completeSteinerRawSeedEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    ← List.append_assoc, split] using next

/-- Two successful prefixes that reach their first output exactly at the end
and are comparable in the prefix order must have the same length and bits. -/
theorem decodeCompleteSteinerSeed_prefixFree (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) {bits more : List Bool}
    {early early' : EarlyRoundSample G height} {hubs hubs' : Fin (completeSteinerHubCount V) → V}
    {thin thin' : ThinSample G} {hubRejects hubRejects' : Fin (completeSteinerHubCount V) → ℕ}
    {thinRejects thinRejects' : G → ℕ}
    (first : decodeCompleteSteinerSeed G height coordinates vertices arcs bits =
      some ((early,hubs,thin),(hubRejects,thinRejects),[]))
    (second : decodeCompleteSteinerSeed G height coordinates vertices arcs more =
      some ((early',hubs',thin'),(hubRejects',thinRejects'),[]))
    (prefixOf : bits <+: more) : bits = more := by
  obtain ⟨tail, rfl⟩ := prefixOf
  have consistent := decodeCompleteSteinerSeed_append G height coordinates vertices arcs tail first
  rw [List.nil_append, second] at consistent
  have empty : [] = tail := congrArg (fun r => r.2.2) (Option.some.inj consistent)
  simp [← empty]

/-- Decode a prefix of the bit stream once, then use its seeds in the
checked weighted replay. The unused bits and rejection counts are returned. -/
def completeSteinerReplayFromBits (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (bits : List Bool) (D : List (V × V)) :=
  (decodeCompleteSteinerSeed G height coordinates vertices arcs bits).map fun sample =>
    (completeSteinerPrefixSearchReplayWithWeightWork G height sample.1.1 sample.1.2.1 sample.1.2.2 D, sample.2)

theorem completeSteinerReplayFromBits_of_seed (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (bits : List Bool) (D : List (V × V))
    {early : EarlyRoundSample G height} {hubs : Fin (completeSteinerHubCount V) → V} {thin : ThinSample G}
    {hubRejects : Fin (completeSteinerHubCount V) → ℕ} {thinRejects : G → ℕ} {rest : List Bool}
    (seed : decodeCompleteSteinerSeed G height coordinates vertices arcs bits =
      some ((early,hubs,thin),(hubRejects,thinRejects),rest)) :
    completeSteinerReplayFromBits G height coordinates vertices arcs bits D =
      some (completeSteinerPrefixSearchReplayWithWeightWork G height early hubs thin D, (hubRejects,thinRejects), rest) := by
  simp [completeSteinerReplayFromBits, seed]

/-- Changing bits outside the interval used by a successful decoder
preserves the seed, rejection counts, and final cursor. -/
theorem decodeCompleteSteinerSeedCursorAtWidth_congr_read (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (left right : Fin budget → Bool) {cursor next : BitCursor budget}
    {early : EarlyRoundSample G height} {hubs : Fin (completeSteinerHubCount V) → V} {thin : ThinSample G}
    {hubRejects : Fin (completeSteinerHubCount V) → ℕ} {thinRejects : G → ℕ}
    (success : decodeCompleteSteinerSeedCursorAtWidth G height width width_eq coordinates vertices arcs left cursor =
      some ((early,hubs,thin),(hubRejects,thinRejects),next))
    (agrees : ∀ i : Fin budget, cursor.position ≤ i.val → i.val < next.position → left i = right i) :
    decodeCompleteSteinerSeedCursorAtWidth G height width width_eq coordinates vertices arcs right cursor =
      some ((early,hubs,thin),(hubRejects,thinRejects),next) := by
  have leftSpec := decodeCompleteSteinerSeedCursorAtWidth_spec G height width width_eq coordinates vertices arcs left cursor
  rw [success, Option.map_some, decodeCompleteSteinerSeedAtWidth_eq] at leftSpec
  have used := decodeCompleteSteinerSeed_suffix G height coordinates vertices arcs leftSpec.symm
  dsimp only at used
  rw [← completeSteinerBitSeedWidth_eq G height arcs hubRejects thinRejects] at used
  let count := completeSteinerBitSeedWidth G height arcs hubRejects thinRejects
  have offset : cursor.position + count = next.position := by
    have move := decodeCompleteSteinerSeedCursorAtWidth_position G height width width_eq coordinates vertices arcs left success
    simpa only [count, completeSteinerBitSeedWidth_eq] using move.symm
  have fits : cursor.position + count ≤ budget := offset.trans_le next.bounded
  have length (bits : Fin budget → Bool) : (cursorSuffix bits cursor).length = budget-cursor.position := by
    simp [cursorSuffix]
  have same : (cursorSuffix left cursor).take count = (cursorSuffix right cursor).take count := by
    apply List.ext_getElem
    · simp only [List.length_take, length]
    · intro i hi hj
      have bound : i < count := (show i < min count (cursorSuffix left cursor).length by
        simpa only [List.length_take] using hi).trans_le (Nat.min_le_left _ _)
      have index : cursor.position+i < budget := by omega
      have equal := agrees ⟨cursor.position+i,index⟩ (by simp)
        (by change cursor.position+i < next.position; omega)
      simpa only [cursorSuffix, List.getElem_take, List.getElem_drop, List.getElem_ofFn] using equal
  have headLen : ((cursorSuffix left cursor).take count).length = count :=
    List.length_take_of_le (by rw [length]; omega)
  let read := (sizedBitsEquiv count).symm ⟨(cursorSuffix left cursor).take count,headLen⟩
  have head : List.ofFn read = (cursorSuffix left cursor).take count :=
    congrArg Subtype.val ((sizedBitsEquiv count).apply_symm_apply ⟨(cursorSuffix left cursor).take count,headLen⟩)
  have leftSplit : List.ofFn read ++ cursorSuffix left next = cursorSuffix left cursor := by
    have tail := used.2
    change (cursorSuffix left cursor).drop count = cursorSuffix left next at tail
    rw [head, ← tail, List.take_append_drop]
  have rightSplit : List.ofFn read ++ cursorSuffix right next = cursorSuffix right cursor := by
    have tail : (cursorSuffix right cursor).drop count = cursorSuffix right next := by
      simp only [cursorSuffix, List.drop_drop, offset]
    rw [head, same, ← tail, List.take_append_drop]
  have leftEvent : read ∈ completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin
      hubRejects thinRejects (cursorSuffix left next) := by
    simp only [completeSteinerRawSeedEvent, Finset.mem_filter, Finset.mem_univ, true_and, leftSplit, leftSpec.symm]
  have rightEvent : read ∈ completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin
      hubRejects thinRejects (cursorSuffix right next) := by
    rwa [← completeSteinerRawSeedEvent_suffix_eq G height coordinates vertices arcs early hubs thin hubRejects thinRejects
      (cursorSuffix left next) (cursorSuffix right next)]
  have rightRead : decodeCompleteSteinerSeed G height coordinates vertices arcs (cursorSuffix right cursor) =
      some ((early,hubs,thin),(hubRejects,thinRejects),cursorSuffix right next) := by
    simpa only [completeSteinerRawSeedEvent, Finset.mem_filter, Finset.mem_univ, true_and, rightSplit] using rightEvent
  have rightSpec := decodeCompleteSteinerSeedCursorAtWidth_spec G height width width_eq coordinates vertices arcs right cursor
  rw [decodeCompleteSteinerSeedAtWidth_eq, rightRead] at rightSpec
  cases readAgain : decodeCompleteSteinerSeedCursorAtWidth G height width width_eq coordinates vertices arcs right cursor with
  | none => simp only [readAgain, Option.map_none, reduceCtorEq] at rightSpec
  | some result =>
    obtain ⟨seed, counts, last⟩ := result
    simp only [readAgain, Option.map_some, Option.some.injEq, Prod.mk.injEq] at rightSpec
    obtain ⟨sameSeed, sameCounts, sameSuffix⟩ := rightSpec
    have equalPos := congrArg List.length sameSuffix
    simp only [cursorSuffix, List.length_drop, List.length_ofFn] at equalPos
    have l := last.bounded
    have r := next.bounded
    have fin : last.position = next.position := by omega
    have samePos : last = next := by cases last; cases next; cases fin; rfl
    simp [sameSeed, sameCounts, samePos]

end OnlineReachabilityPreservers
