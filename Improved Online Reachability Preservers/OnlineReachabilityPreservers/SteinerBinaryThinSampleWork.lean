import Mathlib.Data.Nat.Bits
import OnlineReachabilityPreservers.SteinerBinaryThinRoundRunWork
import OnlineReachabilityPreservers.SteinerSeedDecoderWork

/-! Prepare the binary threshold rows from the indexed thin sample. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Extract a bounded natural number into a fixed number of low bits. At
each step the allowance covers parity and halving on a binary operand that
fits the remaining width, followed by writing the low bit. -/
def encodeBoundedNatWithBinaryWork (value : ℕ) : ℕ → List Bool × ℕ
  | 0 => ([],2)
  | width+1 =>
    let tail := encodeBoundedNatWithBinaryWork value.div2 width
    (value.bodd::tail.1,tail.2+2*(width+1)+5)

def boundedNatToBinaryWorkBudget (width : ℕ) : ℕ := 2+width*(2*width+5)

theorem encodeBoundedNatWithBinaryWork_spec (value width : ℕ) (fits : value < 2^width) :
    let out := encodeBoundedNatWithBinaryWork value width
    binaryWordValue out.1 = value ∧ out.1.length = width ∧ out.2 ≤ boundedNatToBinaryWorkBudget width := by
  induction width generalizing value with
  | zero =>
    have zero : value = 0 := by simpa using fits
    simp [encodeBoundedNatWithBinaryWork,boundedNatToBinaryWorkBudget,binaryWordValue,zero]
  | succ width ih =>
    have smaller : value.div2 < 2^width := by
      rw [Nat.div2_val,Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [pow_succ] using fits
    obtain ⟨decoded,stored,work⟩ := ih value.div2 smaller
    let tail := encodeBoundedNatWithBinaryWork value.div2 width
    change binaryWordValue tail.1 = value.div2 at decoded
    change tail.1.length = width at stored
    change tail.2 ≤ 2+width*(2*width+5) at work
    change binaryWordValue (value.bodd::tail.1) = value ∧ tail.1.length+1 = width+1 ∧
      tail.2+2*(width+1)+5 ≤ 2+(width+1)*(2*(width+1)+5)
    refine ⟨?_,by omega,?_⟩
    · rw [binaryWordValue,decoded]
      change (if value.bodd then 1 else 0)+2*value.div2 = value
      have digit : (if value.bodd then 1 else 0) = (value.bodd).toNat := by cases value.bodd <;> rfl
      rw [digit,Nat.bodd_add_div2]
    · have relaxed : tail.2 ≤ 2+width*(2*(width+1)+5) := work.trans (by gcongr; omega)
      rw [Nat.add_mul,Nat.one_mul]
      omega

/-- Attach binary endpoint labels and a padded seed word to each stored row,
in the same order. Cost the two label reads with the same allowance. -/
def encodeBinaryThinThresholdRowsWithWork {n : ℕ} (code : Fin n → List Bool) (width labelRead : ℕ) :
    List ((Fin n × Fin n) × ℕ) → List (BinaryThinThresholdRow n) × ℕ
  | [] => ([],2)
  | row::rows =>
    let word := encodeBoundedNatWithBinaryWork row.2 width
    let tail := encodeBinaryThinThresholdRowsWithWork code width labelRead rows
    (⟨row.1,(code row.1.1,code row.1.2),word.1⟩::tail.1,word.2+tail.2+2*labelRead+6)

def encodeBinaryThinThresholdRowsWorkBudget (rows width labelRead : ℕ) : ℕ :=
  2+rows*(boundedNatToBinaryWorkBudget width+2*labelRead+6)

/-- The encoded rows decode to the entire original list. Each carries the
specified labels and exactly the reserved threshold width. -/
theorem encodeBinaryThinThresholdRowsWithWork_spec {n : ℕ} (code : Fin n → List Bool) (width labelRead : ℕ)
    (source : List ((Fin n × Fin n) × ℕ)) (fits : ∀ row ∈ source, row.2 < 2^width) :
    let out := encodeBinaryThinThresholdRowsWithWork code width labelRead source
    out.1.map BinaryThinThresholdRow.reference = source ∧
    (∀ row ∈ out.1, row.labels = (code row.arc.1,code row.arc.2) ∧ row.sample.length = width) ∧
    out.2 ≤ encodeBinaryThinThresholdRowsWorkBudget source.length width labelRead := by
  induction source with
  | nil => simp [encodeBinaryThinThresholdRowsWithWork,encodeBinaryThinThresholdRowsWorkBudget]
  | cons row rows ih =>
    let word := encodeBoundedNatWithBinaryWork row.2 width
    let tail := encodeBinaryThinThresholdRowsWithWork code width labelRead rows
    let encoded : BinaryThinThresholdRow n := ⟨row.1,(code row.1.1,code row.1.2),word.1⟩
    obtain ⟨value,stored,work⟩ := encodeBoundedNatWithBinaryWork_spec row.2 width (fits row List.mem_cons_self)
    obtain ⟨decoded,bounds,cost⟩ := ih (fun r mem => fits r (List.mem_cons_of_mem _ mem))
    change binaryWordValue word.1 = row.2 at value
    change word.1.length = width at stored
    change word.2 ≤ boundedNatToBinaryWorkBudget width at work
    change tail.1.map BinaryThinThresholdRow.reference = rows at decoded
    change (encoded::tail.1).map BinaryThinThresholdRow.reference = row::rows ∧
      (∀ r ∈ encoded::tail.1, r.labels = (code r.arc.1,code r.arc.2) ∧ r.sample.length = width) ∧
      word.2+tail.2+2*labelRead+6 ≤ encodeBinaryThinThresholdRowsWorkBudget (rows.length+1) width labelRead
    refine ⟨?_,?_,?_⟩
    · simp [encoded,BinaryThinThresholdRow.reference,value,decoded]
    · intro current present
      rcases List.mem_cons.mp present with rfl | mem
      · exact ⟨rfl,stored⟩
      · exact bounds current mem
    · change tail.2 ≤ encodeBinaryThinThresholdRowsWorkBudget rows.length width labelRead at cost
      unfold encodeBinaryThinThresholdRowsWorkBudget at cost ⊢
      rw [Nat.add_mul,Nat.one_mul]
      omega

/-- Read one threshold per original arc from the indexed sample and
construct the binary cache. The arc index is shared with the seed decoder. -/
def prepareBinaryThinSampleRowsWithWork {n : ℕ} (G : Arcs (Fin n)) (m width labelRead : ℕ) (hm : m = G.card)
    (index : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) (code : Fin n → List Bool) :
    List (BinaryThinThresholdRow n) × ℕ :=
  let indexed := prepareThinThresholdListByIndexWithWordWork G m hm index sample
  let encoded := encodeBinaryThinThresholdRowsWithWork code width labelRead indexed.1.val
  (encoded.1,indexed.2+encoded.2+4)

def prepareBinaryThinSampleRowsWorkBudget (arcs width labelRead : ℕ) : ℕ :=
  11*arcs+8+encodeBinaryThinThresholdRowsWorkBudget arcs width labelRead

/-- For the sample and graph using the same index, the constructed cache
matches the fixed reference sample with exactly one row per original arc. -/
theorem prepareBinaryThinSampleRowsWithWork_spec {n labels : ℕ} (G : Arcs (Fin n)) (m width labelRead : ℕ)
    (hm : m = G.card) (fits : G.card ≤ 2^width)
    (index : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) (code : Fin n → List Bool)
    (numeric : ∀ v, binaryWordValue (code v) = v.val) (short : ∀ v, (code v).length ≤ labels) :
    let out := prepareBinaryThinSampleRowsWithWork G m width labelRead hm index sample code
    let reference := fun edge => sample (index edge)
    (out.1.map BinaryThinThresholdRow.reference).toFinset = (prepareThinThresholdRowsWithSeedReads G m reference).1 ∧
    ((out.1.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup ∧ out.1.length = m ∧
    (∀ row ∈ out.1, BinaryThinArcMatches labels row.labels row.arc ∧ row.sample.length = width ∧
      row.labels = (code row.arc.1,code row.arc.2)) ∧ out.2 ≤ prepareBinaryThinSampleRowsWorkBudget m width labelRead := by
  let indexed := prepareThinThresholdListByIndexWithWordWork G m hm index sample
  let source := indexed.1.val
  let encoded := encodeBinaryThinThresholdRowsWithWork code width labelRead source
  let reference := fun edge => sample (index edge)
  obtain ⟨asSet,length,_,setup⟩ := prepareThinThresholdListByIndexWithWordWork_spec G m hm index sample
  change source.toFinset = (prepareThinThresholdRowsByIndex G m hm index sample).1 at asSet
  change source.length = m at length
  change indexed.2 = 11*m+4 at setup
  rw [prepareThinThresholdRowsByIndex_eq] at asSet
  have within : ∀ row ∈ source, row.2 < 2^width := by
    intro row member
    have existsIn : row ∈ (prepareThinThresholdRowsWithSeedReads G m reference).1 := by
      rw [← asSet]
      exact List.mem_toFinset.mpr member
    change row ∈ G.attach.map _ at existsIn
    obtain ⟨e,_,rfl⟩ := mem_map.mp existsIn
    exact (reference e).isLt.trans_le fits
  obtain ⟨decode,valid,cost⟩ := encodeBinaryThinThresholdRowsWithWork_spec code width labelRead source within
  change encoded.1.map BinaryThinThresholdRow.reference = source at decode
  change encoded.2 ≤ encodeBinaryThinThresholdRowsWorkBudget source.length width labelRead at cost
  refine ⟨?_,?_,?_,?_,?_⟩
  · change (encoded.1.map BinaryThinThresholdRow.reference).toFinset = _
    rw [decode,asSet]
  · change ((encoded.1.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup
    rw [decode]
    exact indexed.1.property
  · change encoded.1.length = m
    rw [← List.length_map (f := BinaryThinThresholdRow.reference),decode,length]
  · intro row present
    obtain ⟨word,sampled⟩ := valid row present
    exact ⟨by simpa only [word] using ⟨numeric row.arc.1,numeric row.arc.2,short row.arc.1,short row.arc.2⟩,
      sampled,word⟩
  · change indexed.2+encoded.2+4 ≤ _
    rw [length] at cost
    unfold prepareBinaryThinSampleRowsWorkBudget
    omega

/-- Count the listed cells using a natural counter, charging each step by
the current bound on the counter's bit length. -/
def readBinaryWidthAsNatWithWork : List Bool → ℕ × ℕ
  | [] => (0,2)
  | _::bits =>
    let tail := readBinaryWidthAsNatWithWork bits
    (tail.1+1,tail.2+tail.1+5)

def binaryWidthAsNatWorkBudget (width : ℕ) : ℕ := 2+width*(width+5)

theorem readBinaryWidthAsNatWithWork_spec (bits : List Bool) :
    let out := readBinaryWidthAsNatWithWork bits
    out.1 = bits.length ∧ out.2 ≤ binaryWidthAsNatWorkBudget bits.length := by
  induction bits with
  | nil => simp [readBinaryWidthAsNatWithWork,binaryWidthAsNatWorkBudget]
  | cons bit tail ih =>
    obtain ⟨length,work⟩ := ih
    let input := readBinaryWidthAsNatWithWork tail
    change input.1 = tail.length at length
    change input.2 ≤ 2+tail.length*(tail.length+5) at work
    change input.1+1 = tail.length+1 ∧ input.2+input.1+5 ≤ 2+(tail.length+1)*(tail.length+1+5)
    rw [length,Nat.add_mul,Nat.one_mul]
    have enough : 2+tail.length*(tail.length+5) ≤ 2+tail.length*(tail.length+1+5) := by gcongr; omega
    exact ⟨rfl,by omega⟩

/-- Build the binary cache from the shared sample index, then run the thin
phase. No sample entries are read for an empty request list. -/
def binaryThinRoundFromIndexedSampleWithWork {n : ℕ} (G : Arcs (Fin n))
    (arcs keys : List (List Bool × List Bool)) (base ceiling factor : List Bool)
    (m fuel labelRead : ℕ) (hm : m = G.card) (index : G ≃ Fin G.card)
    (sample : Fin G.card → Fin G.card) (code : Fin n → List Bool) (demands : List (List Bool × List Bool)) :
    List (List Bool × List Bool) × ℕ :=
  if demands.isEmpty then ([],2) else
    let width := readBinaryWidthAsNatWithWork ceiling
    let rows := prepareBinaryThinSampleRowsWithWork G m width.1 labelRead hm index sample code
    let run := binaryThinRoundRunWithWork arcs keys base ceiling factor rows.1 n m fuel demands
    (run.1,width.2+rows.2+run.2+4)

/-- The complete binary thin phase may use the indexed sample directly.
The graph labels, pair enumeration, and numeric controls are supplied. -/
theorem binaryThinRoundFromIndexedSampleWithWork_refines {n labels : ℕ}
    (arcs keys demands : List (Fin n × Fin n)) (simple : arcs.Nodup) (complete : ∀ e, e ∈ keys)
    (reachable : ∀ demand ∈ demands, Reach arcs.toFinset demand.1 demand.2)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labels) (base ceiling factor : List Bool)
    (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = arcs.toFinset.card)
    (index : arcs.toFinset ≃ Fin arcs.toFinset.card) (sample : Fin arcs.toFinset.card → Fin arcs.toFinset.card)
    (labelRead : ℕ) :
    let G := arcs.toFinset
    let fuel := G.card*(G.card.log2+1)+1
    let out := binaryThinRoundFromIndexedSampleWithWork G (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys)
      base ceiling factor G.card fuel labelRead rfl index sample code (binaryEncodeArcs code demands)
    (∃ selected : List (Fin n × Fin n), out.1 = binaryEncodeArcs code selected ∧
      selected.toFinset = thinRoundRun G (binaryWordValue factor) (fun e => sample (index e)) demands) ∧
    out.2 ≤ binaryWidthAsNatWorkBudget ceiling.length+prepareBinaryThinSampleRowsWorkBudget G.card ceiling.length labelRead+
      binaryThinRoundFromEmptyWorkBudget n arcs.length keys.length G.card base.length labels ceiling.length
        ceiling.length factor.length G.card demands.length+4 := by
  let G := arcs.toFinset
  let fuel := G.card*(G.card.log2+1)+1
  let prepared := prepareBinaryThinSampleRowsWithWork G G.card ceiling.length labelRead rfl index sample code
  have fits : G.card ≤ 2^ceiling.length := (supply ▸ binaryWordValue_lt_pow ceiling).le
  obtain ⟨thresholds,unique,count,valid,prepCost⟩ := prepareBinaryThinSampleRowsWithWork_spec G G.card ceiling.length
    labelRead rfl fits index sample code numeric bounded
  have rowsFit : ∀ row ∈ prepared.1, BinaryThinArcMatches labels row.labels row.arc ∧ row.sample.length ≤ ceiling.length :=
    fun row present => ⟨(valid row present).1,(valid row present).2.1.le⟩
  have labelsMatch : ∀ row ∈ prepared.1, row.labels = (code row.arc.1,code row.arc.2) :=
    fun row present => (valid row present).2.2
  obtain ⟨result,work⟩ := binaryThinRoundRunWithWork_refines arcs keys demands simple complete reachable code numeric
    bounded base ceiling factor size supply prepared.1 rowsFit labelsMatch unique (fun e => sample (index e)) thresholds
  let run := binaryThinRoundRunWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys) base ceiling factor
    prepared.1 n G.card fuel (binaryEncodeArcs code demands)
  change run.2 ≤ binaryThinRoundFromEmptyWorkBudget n arcs.length keys.length prepared.1.length base.length labels
    ceiling.length ceiling.length factor.length G.card demands.length at work
  change prepared.1.length = G.card at count
  rw [count] at work
  obtain ⟨width,widthCost⟩ := readBinaryWidthAsNatWithWork_spec ceiling
  cases demands with
  | nil =>
    refine ⟨⟨[],rfl,by simp [thinRoundRun]⟩,?_⟩
    simp [binaryThinRoundFromIndexedSampleWithWork,binaryEncodeArcs]
  | cons first rest =>
    dsimp only [binaryThinRoundFromIndexedSampleWithWork,binaryEncodeArcs,List.map_cons,List.isEmpty_cons,
      Bool.false_eq_true,ite_false]
    rw [width]
    refine ⟨result,?_⟩
    change (readBinaryWidthAsNatWithWork ceiling).2+prepared.2+run.2+4 ≤ _
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add widthCost prepCost) work) 4

/-- The indexed reader retained by a successful fixed-budget decode gives
exactly the thin sample of that same decoded packet at the shared arc indices. -/
theorem decodeSteinerSeedWithArrayViewsFromPreparedScale_thin {n : ℕ} (G : Arcs (Fin n)) (height m : ℕ)
    (hm : m = G.card) (scale : {s : ℕ // s = forestScale G height})
    (indexes : SteinerReplaySeedIndexes G height) (bits : Fin (steinerBitBudget G height) → Bool) :
    let out := decodeSteinerSeedWithArrayViewsFromPreparedScale G height n m (by simp) hm scale indexes bits
    ∀ entry, out.1.2 = some entry → (fun edge => entry.2.thin (indexes.arcs edge)) = entry.1.2.2 := by
  let hn : n = Fintype.card (Fin n) := by simp
  obtain ⟨project,_⟩ := decodeSteinerSeedWithArrayViewsFromPreparedScale_spec G height n m hn hm scale indexes bits
  obtain ⟨_,same⟩ := decodeSteinerSeedWithIndexedThinFromPreparedScale_spec G height n m hn hm scale indexes bits
  intro out entry found
  have seen := congrArg Prod.fst project
  change out.1.2.map (fun p => (p.1,p.2.thin)) = _ at seen
  rw [found,Option.map_some] at seen
  funext edge
  exact same (entry.1,entry.2.thin) seen.symm edge

private theorem encodeBinaryThinThresholdRowsWithWork_length {n : ℕ} (code : Fin n → List Bool) (width labelRead : ℕ)
    (source : List ((Fin n × Fin n) × ℕ)) :
    (encodeBinaryThinThresholdRowsWithWork code width labelRead source).1.length = source.length := by
  induction source with
  | nil => rfl
  | cons first rest ih =>
    simp [encodeBinaryThinThresholdRowsWithWork,ih]

theorem binaryThinRoundFromIndexedSampleWithWork_length_le {n : ℕ} (G : Arcs (Fin n))
    (arcs keys : List (List Bool × List Bool)) (base ceiling factor : List Bool) (m fuel labelRead : ℕ)
    (hm : m = G.card) (index : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) (code : Fin n → List Bool)
    (demands : List (List Bool × List Bool)) :
    (binaryThinRoundFromIndexedSampleWithWork G arcs keys base ceiling factor m fuel labelRead hm index sample code demands).1.length ≤
      max arcs.length m := by
  have prepared (width : ℕ) : (prepareBinaryThinSampleRowsWithWork G m width labelRead hm index sample code).1.length = m := by
    unfold prepareBinaryThinSampleRowsWithWork
    dsimp only
    rw [encodeBinaryThinThresholdRowsWithWork_length]
    exact (prepareThinThresholdListByIndexWithWordWork_spec G m hm index sample).2.1
  unfold binaryThinRoundFromIndexedSampleWithWork
  split
  · exact Nat.zero_le _
  · dsimp only
    let width := (readBinaryWidthAsNatWithWork ceiling).1
    have bound := binaryThinRoundRunWithWork_length_le arcs keys base ceiling factor
      (prepareBinaryThinSampleRowsWithWork G m width labelRead hm index sample code).1 n m fuel demands
    rw [prepared width] at bound
    exact bound

end OnlineReachabilityPreservers
