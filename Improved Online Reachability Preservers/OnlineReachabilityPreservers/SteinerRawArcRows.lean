import OnlineReachabilityPreservers.SteinerBinaryArrivals
import OnlineReachabilityPreservers.SteinerBinaryFinInputWork

/-! Prepare the graph directly from its raw arc list before sampling. -/

namespace OnlineReachabilityPreservers

private def scanArcRowsWithWork {n : ℕ} (needle : Fin n × Fin n) :
    List (Fin n × Fin n) → Bool × ℕ
  | [] => (false, 2)
  | arc::rest =>
    if needle = arc then (true, 5) else
      let tail := scanArcRowsWithWork needle rest
      (tail.1, tail.2+5)

private theorem scanArcRowsWithWork_spec {n : ℕ} (needle : Fin n × Fin n)
    (rows : List (Fin n × Fin n)) :
    let out := scanArcRowsWithWork needle rows
    (out.1 = true ↔ needle ∈ rows) ∧ out.2 ≤ 5*rows.length+2 := by
  induction rows with
  | nil => simp [scanArcRowsWithWork]
  | cons arc rest ih =>
    by_cases equal : needle = arc
    · simp [scanArcRowsWithWork,equal]
      omega
    · rw [scanArcRowsWithWork,ite_eq_right equal]
      refine ⟨?_,?_⟩
      · simpa only [List.mem_cons,equal,false_or] using ih.1
      · have bound := ih.2
        simp only [List.length_cons]
        omega

private def dedupArcRowsUsingScan {A : Type*} (scan : A → List A → Bool × ℕ)
    (sound : ∀ needle rows, (scan needle rows).1 = true ↔ needle ∈ rows) :
    List A → {rows : List A // rows.Nodup} × ℕ
  | [] => (⟨[],by simp⟩,2)
  | arc::rest =>
    let tail := dedupArcRowsUsingScan scan sound rest
    let check := scan arc tail.1.val
    if found : check.1 = true then
      (tail.1,tail.2+check.2+6)
    else
      (⟨arc::tail.1.val,List.nodup_cons.mpr
        ⟨fun member => found ((sound arc tail.1.val).mpr member),tail.1.property⟩⟩,
        tail.2+check.2+8)

private theorem dedupArcRowsUsingScan_spec {A : Type*} (scan : A → List A → Bool × ℕ)
    (sound : ∀ needle rows, (scan needle rows).1 = true ↔ needle ∈ rows)
    (fee : ℕ) (bounded : ∀ needle rows, (scan needle rows).2 ≤ fee*rows.length+2) (rows : List A) :
    let out := dedupArcRowsUsingScan scan sound rows
    (∀ arc, arc ∈ out.1.val ↔ arc ∈ rows) ∧
      out.1.val.length ≤ rows.length ∧ out.2 ≤ (fee+15)*(rows.length+1)^2 := by
  induction rows with
  | nil => simp [dedupArcRowsUsingScan]
  | cons arc rest ih =>
    let tail := dedupArcRowsUsingScan scan sound rest
    let check := scan arc tail.1.val
    have members (e : A) : e ∈ tail.1.val ↔ e ∈ rest := ih.1 e
    have size : tail.1.val.length ≤ rest.length := ih.2.1
    have tailWork : tail.2 ≤ (fee+15)*(rest.length+1)^2 := ih.2.2
    have scanWork : check.2 ≤ fee*rest.length+2 :=
      (bounded arc tail.1.val).trans (Nat.add_le_add_right (Nat.mul_le_mul_left fee size) 2)
    have work : tail.2+check.2+8 ≤ (fee+15)*((arc::rest).length+1)^2 := by
      have growth : (rest.length+1+1)^2 = (rest.length+1)^2+(2*rest.length+3) := by ring
      have inc : fee*rest.length ≤ fee*(2*rest.length+3) := Nat.mul_le_mul_left fee (by omega)
      have room : 10 ≤ 15*(2*rest.length+3) := by omega
      rw [List.length_cons,growth,Nat.mul_add,Nat.add_mul fee 15 (2*rest.length+3)]
      omega
    by_cases found : check.1 = true
    · have built : dedupArcRowsUsingScan scan sound (arc::rest) = (tail.1,tail.2+check.2+6) := by
        rw [dedupArcRowsUsingScan]
        exact dite_eq_left found
      simp only [built]
      have kept := (sound arc tail.1.val).mp found
      refine ⟨?_,size.trans (Nat.le_succ _),by omega⟩
      intro e
      rw [members e,List.mem_cons]
      exact ⟨Or.inr,fun disj => disj.elim (fun eq => eq ▸ (members arc).mp kept) id⟩
    · let row : {rows : List A // rows.Nodup} := ⟨arc::tail.1.val,List.nodup_cons.mpr
        ⟨fun member => found ((sound arc tail.1.val).mpr member),tail.1.property⟩⟩
      have built : dedupArcRowsUsingScan scan sound (arc::rest) = (row,tail.2+check.2+8) := by
        rw [dedupArcRowsUsingScan]
        exact dite_eq_right found
      simp only [built]
      refine ⟨?_,Nat.succ_le_succ size,work⟩
      intro e
      change e ∈ arc::tail.1.val ↔ e ∈ arc::rest
      simp only [List.mem_cons,members e]

private abbrev dedupArcRowsWithWork {n : ℕ} :
    List (Fin n × Fin n) → {rows : List (Fin n × Fin n) // rows.Nodup} × ℕ :=
  dedupArcRowsUsingScan scanArcRowsWithWork (fun a rows => (scanArcRowsWithWork_spec a rows).1)

private theorem dedupArcRowsWithWork_spec {n : ℕ} (rows : List (Fin n × Fin n)) :
    let out := dedupArcRowsWithWork rows
    (∀ arc, arc ∈ out.1.val ↔ arc ∈ rows) ∧
      out.1.val.length ≤ rows.length ∧ out.2 ≤ 20*(rows.length+1)^2 :=
  dedupArcRowsUsingScan_spec scanArcRowsWithWork (fun a rs => (scanArcRowsWithWork_spec a rs).1)
    5 (fun a rs => (scanArcRowsWithWork_spec a rs).2) rows

/-- Build the graph using only the raw arc rows. The tally counts scans,
list construction, and equality tests on finite labels. -/
def prepareSteinerArcRowsWithWork {n : ℕ} (raw : List (Fin n × Fin n)) :
    Arcs (Fin n) × ℕ :=
  let dedup := dedupArcRowsWithWork raw
  (⟨(dedup.1.val : Multiset (Fin n × Fin n)),by simpa using dedup.1.property⟩,dedup.2+3)

theorem prepareSteinerArcRowsWithWork_spec {n : ℕ} (raw : List (Fin n × Fin n)) :
    let out := prepareSteinerArcRowsWithWork raw
    raw.toFinset = out.1 ∧ out.1.card ≤ raw.length ∧ out.2 ≤ 23*(raw.length+1)^2 := by
  let dedup := dedupArcRowsWithWork raw
  obtain ⟨members,size,work⟩ := dedupArcRowsWithWork_spec raw
  have eq : raw.toFinset = (prepareSteinerArcRowsWithWork raw).1 := by
    ext arc
    change arc ∈ raw.toFinset ↔ arc ∈ (dedup.1.val : Multiset (Fin n × Fin n))
    rw [List.mem_toFinset,Multiset.mem_coe]
    exact (members arc).symm
  refine ⟨eq,size,?_⟩
  change dedup.2+3 ≤ 23*(raw.length+1)^2
  have overhead : 3 ≤ 3*(raw.length+1)^2 := by nlinarith
  change dedup.2 ≤ 20*(raw.length+1)^2 at work
  omega

/-- Run the sampled solver from a raw arc list, building its graph once
and adding the ingestion tally to the returned state. -/
def finSteinerBinaryServeFromArcRowsWithWork {n : ℕ} {m : Type → Type} [Monad m]
    (raw : List (Fin n × Fin n)) (height : ℕ) (nextBit : m Bool) (D : List (Fin n × Fin n)) :
    m (FinSteinerBinaryArrivalState n) := do
  let graph := prepareSteinerArcRowsWithWork raw
  let result ← finSteinerBinaryServeFromBitSource graph.1 raw
    (prepareSteinerArcRowsWithWork_spec raw).1 height nextBit D
  pure { result with work := result.work+graph.2+4 }

theorem finSteinerBinaryServeFromArcRowsWithWork_stream {n : ℕ}
    (raw : List (Fin n × Fin n)) (height : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (D : List (Fin n × Fin n)) :
    let graph := prepareSteinerArcRowsWithWork raw
    let expected := (finSteinerBinaryServeFromBitSource graph.1 raw
      (prepareSteinerArcRowsWithWork_spec raw).1 height (steinerBitStreamSource stream) D).run start
    (finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start =
      ({ expected.1 with work := expected.1.work+graph.2+4 },expected.2) := by
  rfl

theorem finSteinerBinaryServeFromArcRows_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (raw : List (Fin n × Fin n)) (stream : ℕ → Bool) (start : ℕ)
      (D : List (Fin n × Fin n)), (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
      ((finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start).1.work ≤
        C*(n+raw.length+D.length+1)^k := by
  obtain ⟨C,k,replay⟩ := finSteinerBinaryServeFromBitSource_polynomial height
  refine ⟨C*2^k+27,max k 2,?_⟩
  intro n raw stream start D feasible
  let graph := prepareSteinerArcRowsWithWork raw
  let size := n+raw.length+D.length+1
  have positive : 0 < size := by dsimp [size]; omega
  obtain ⟨same,cardBound,buildBound⟩ := prepareSteinerArcRowsWithWork_spec raw
  have sizeBound : n+graph.1.card+raw.length+D.length+1 ≤ 2*size := by
    change graph.1.card ≤ raw.length at cardBound
    dsimp [size]
    omega
  have feasibleGraph : ∀ d ∈ D, Reach graph.1 d.1 d.2 := by rw [← same]; exact feasible
  have replayCost := replay graph.1 raw same stream start D feasibleGraph
  have paidReplay : ((finSteinerBinaryServeFromBitSource graph.1 raw same height
      (steinerBitStreamSource stream) D).run start).1.work ≤ (C*2^k)*size^(max k 2) := calc
    _ ≤ C*(n+graph.1.card+raw.length+D.length+1)^k := replayCost
    _ ≤ C*(2*size)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left sizeBound _)
    _ = (C*2^k)*size^k := by rw [Nat.mul_pow,Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_left _ _))
  have paidBuild : graph.2+4 ≤ 27*size^(max k 2) := by
    have bound : graph.2 ≤ 23*size^2 :=
      buildBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [size]; omega) _))
    have posSq : 1 ≤ size^2 := Nat.one_le_pow _ _ positive
    have allowance : graph.2+4 ≤ 27*size^2 := by omega
    exact allowance.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_right _ _)))
  rw [finSteinerBinaryServeFromArcRowsWithWork_stream]
  change ((finSteinerBinaryServeFromBitSource graph.1 raw same height
    (steinerBitStreamSource stream) D).run start).1.work + graph.2+4 ≤ _
  rw [Nat.add_assoc, Nat.add_mul]
  exact Nat.add_le_add paidReplay paidBuild

open MeasureTheory
open scoped ENNReal

/-- Theorem 21 from raw arc rows. The recorded work includes building
the graph, and one sampled word serves all online prefixes. -/
theorem theorem21_online_steiner_sampled_arc_rows {ε : ℝ} (epsilon : 0 < ε) :
    ∃ (height : ℕ) (K : ℝ) (C k : ℕ), 0 < height ∧ 0 < K ∧
      (∀ {n : ℕ} (raw : List (Fin n × Fin n)) (stream : ℕ → Bool) (D : List (Fin n × Fin n)),
        (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
        let result := (finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) D).run 0
        result.2 = steinerBitBudget raw.toFinset height ∧
          result.1.graph ⊆ raw.toFinset ∧ Preserves raw.toFinset result.1.graph D ∧
          result.1.work ≤ C*(n+raw.length+D.length+1)^k) ∧
      (∀ {n : ℕ} (raw : List (Fin n × Fin n)) (stream : ℕ → Bool) {D E : List (Fin n × Fin n)},
        D <+: E → (∀ d ∈ E, Reach raw.toFinset d.1 d.2) →
          ((finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) D).run 0).1.graph ⊆
            ((finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) E).run 0).1.graph) ∧
      (∀ {n : ℕ} {Z : Arcs (Fin n)} (raw : List (Fin n × Fin n)) (D : List (Fin n × Fin n)),
        Z ⊆ raw.toFinset → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∫⁻ stream, (((finSteinerBinaryServeFromArcRowsWithWork raw height
          (steinerBitStreamSource stream) D).run 0).1.graph.card : ℝ≥0∞) ∂fairBitMeasure) ≤
            ENNReal.ofReal (K*(n:ℝ)^(3/5+ε)*Z.card)) := by
  obtain ⟨height,K,_,_,heightPos,constantPos,correct,monotone,expected⟩ :=
    theorem21_online_steiner_sampled_arrivals epsilon
  obtain ⟨C,k,cost⟩ := finSteinerBinaryServeFromArcRows_polynomial height
  refine ⟨height,K,C,k,heightPos,constantPos,?_,?_,?_⟩
  · intro n raw stream D feasible
    let G := (prepareSteinerArcRowsWithWork raw).1
    have same : raw.toFinset = G := (prepareSteinerArcRowsWithWork_spec raw).1
    have feasibleGraph : ∀ d ∈ D, Reach G d.1 d.2 := by rw [← same]; exact feasible
    obtain ⟨bits,sub,preserves,_⟩ := correct G raw same stream D feasibleGraph
    refine ⟨?_,?_,?_,cost raw stream 0 D feasible⟩
    · rw [finSteinerBinaryServeFromArcRowsWithWork_stream]
      exact bits.trans (congrArg (fun graphs => steinerBitBudget graphs height) same.symm)
    · rw [finSteinerBinaryServeFromArcRowsWithWork_stream]
      intro arc member
      exact same.symm ▸ sub member
    · rw [finSteinerBinaryServeFromArcRowsWithWork_stream]
      intro demand member
      exact (preserves demand member).trans (by rw [same])
  · intro n raw stream D E prefixOf feasible
    let G := (prepareSteinerArcRowsWithWork raw).1
    have same : raw.toFinset = G := (prepareSteinerArcRowsWithWork_spec raw).1
    have feasibleGraph : ∀ d ∈ E, Reach G d.1 d.2 := by rw [← same]; exact feasible
    rw [finSteinerBinaryServeFromArcRowsWithWork_stream,finSteinerBinaryServeFromArcRowsWithWork_stream]
    exact monotone G raw same stream prefixOf feasibleGraph
  · intro n Z raw D sub feasible
    let G := (prepareSteinerArcRowsWithWork raw).1
    have same : raw.toFinset = G := (prepareSteinerArcRowsWithWork_spec raw).1
    have subGraph : Z ⊆ G := same ▸ sub
    simpa only [finSteinerBinaryServeFromArcRowsWithWork_stream] using expected raw same D subGraph feasible

private structure CachedFinArc (n width : ℕ) where
  arc : Fin n × Fin n
  labels : List Bool × List Bool
  canonical : labels = (binaryFinLabel width arc.1,binaryFinLabel width arc.2)

private theorem CachedFinArc.arc_injective {n width : ℕ} :
    Function.Injective (@CachedFinArc.arc n width) := by
  intro a b equal
  rcases a with ⟨a,labelsA,canonicalA⟩
  rcases b with ⟨b,labelsB,canonicalB⟩
  change a = b at equal
  subst b
  subst labelsA
  subst labelsB
  rfl

private def cacheBinaryArcRowsWithWork {n : ℕ} (width : ℕ) :
    List (Fin n × Fin n) → List (CachedFinArc n width) × ℕ
  | [] => ([],2)
  | arc::rest =>
    let left := encodeBoundedNatWithBinaryWork arc.1.val width
    let right := encodeBoundedNatWithBinaryWork arc.2.val width
    let later := cacheBinaryArcRowsWithWork width rest
    (⟨arc,(left.1,right.1),rfl⟩::later.1,left.2+right.2+later.2+7)

private theorem cacheBinaryArcRowsWithWork_spec {n width : ℕ} (fits : n ≤ 2^width)
    (rows : List (Fin n × Fin n)) :
    let out := cacheBinaryArcRowsWithWork width rows
    out.1.map CachedFinArc.arc = rows ∧
      out.2 ≤ 2+rows.length*(2*boundedNatToBinaryWorkBudget width+7) := by
  induction rows with
  | nil => simp [cacheBinaryArcRowsWithWork]
  | cons row rest ih =>
    obtain ⟨same,charge⟩ := ih
    have left := (encodeBoundedNatWithBinaryWork_spec row.1.val width (row.1.isLt.trans_le fits)).2.2
    have right := (encodeBoundedNatWithBinaryWork_spec row.2.val width (row.2.isLt.trans_le fits)).2.2
    change (cacheBinaryArcRowsWithWork width rest).1.map CachedFinArc.arc = rest at same
    change (cacheBinaryArcRowsWithWork width rest).2 ≤ _ at charge
    change (encodeBoundedNatWithBinaryWork row.1.val width).2 ≤ _ at left
    change (encodeBoundedNatWithBinaryWork row.2.val width).2 ≤ _ at right
    simp only [cacheBinaryArcRowsWithWork,List.map_cons,same,List.length_cons,true_and]
    rw [Nat.add_mul rest.length 1,Nat.one_mul]
    omega

private theorem binaryFinLabel_injective {n width : ℕ} (fits : n ≤ 2^width) :
    Function.Injective (@binaryFinLabel n width) := by
  intro a b same
  apply Fin.ext
  rw [← (binaryFinLabel_spec width fits a).1,← (binaryFinLabel_spec width fits b).1,same]

private theorem cachedArc_test_spec {n width : ℕ} (fits : n ≤ 2^width) (a b : CachedFinArc n width) :
    let out := binaryArcMemWithWork a.labels [b.labels]
    (out.1 = true ↔ a = b) ∧ out.2 ≤ 10*width+16 := by
  obtain ⟨same,charge⟩ := binaryArcMemWithWork_spec (binaryFinLabel width) (binaryFinLabel_injective fits)
    width (fun v => (binaryFinLabel_spec width fits v).2.le) a.arc [b.arc]
  have bits : binaryEncodeArcs (binaryFinLabel width) [b.arc] = [b.labels] := by
    rw [b.canonical]
    rfl
  dsimp only at same charge ⊢
  rw [bits,← a.canonical] at same charge
  refine ⟨?_,by simp only [List.length_singleton,Nat.one_mul] at charge; omega⟩
  rw [same,decide_eq_true_eq,List.mem_singleton]
  exact ⟨fun eq => CachedFinArc.arc_injective eq,fun eq => congrArg CachedFinArc.arc eq⟩

private def scanCachedArcRowsWithWork {n width : ℕ} (needle : CachedFinArc n width) :
    List (CachedFinArc n width) → Bool × ℕ
  | [] => (false,2)
  | arc::rest =>
    let same := binaryArcMemWithWork needle.labels [arc.labels]
    if same.1 then (true,same.2+5) else
      let later := scanCachedArcRowsWithWork needle rest
      (later.1,same.2+later.2+5)

private theorem scanCachedArcRowsWithWork_spec {n width : ℕ} (fits : n ≤ 2^width) (needle : CachedFinArc n width)
    (rows : List (CachedFinArc n width)) :
    let out := scanCachedArcRowsWithWork needle rows
    (out.1 = true ↔ needle ∈ rows) ∧ out.2 ≤ (10*width+21)*rows.length+2 := by
  induction rows with
  | nil => simp [scanCachedArcRowsWithWork]
  | cons arc rest ih =>
    let fetch := binaryArcMemWithWork needle.labels [arc.labels]
    obtain ⟨equal,fee⟩ := cachedArc_test_spec fits needle arc
    change fetch.1 = true ↔ needle = arc at equal
    change fetch.2 ≤ 10*width+16 at fee
    by_cases found : fetch.1 = true
    · rw [scanCachedArcRowsWithWork,ite_eq_left found]
      have same := equal.mp found
      refine ⟨by simp [same],?_⟩
      change fetch.2+5 ≤ (10*width+21)*(arc::rest).length+2
      rw [List.length_cons,Nat.mul_succ]
      omega
    · rw [scanCachedArcRowsWithWork,ite_eq_right found]
      refine ⟨?_,?_⟩
      · simpa only [List.mem_cons,not_congr equal |>.mp found,false_or] using ih.1
      · have recursion : (scanCachedArcRowsWithWork needle rest).2 ≤ (10*width+21)*rest.length+2 := ih.2
        change fetch.2+(scanCachedArcRowsWithWork needle rest).2+5 ≤ (10*width+21)*(arc::rest).length+2
        rw [List.length_cons,Nat.mul_succ]
        omega

private theorem bitLength_fits_fin_labels (n : ℕ) : n ≤ 2^(bitLengthWithWork n).1 := by
  rw [(bitLengthWithWork_spec n).1]
  have fits : n < 2^n.size := by
    apply lt_of_not_ge
    intro impossible
    exact (lt_irrefl n.size) (Nat.lt_size.mpr impossible)
  exact fits.le

/-- Encode each input label once and build the graph using metered bit
comparisons of the cached arc keys. The exact graph retains every input arc. -/
def prepareSteinerBinaryArcRowsWithWork {n : ℕ} (raw : List (Fin n × Fin n)) : Arcs (Fin n) × ℕ :=
  let width := bitLengthWithWork n
  let encoded := cacheBinaryArcRowsWithWork width.1 raw
  let unique := dedupArcRowsUsingScan scanCachedArcRowsWithWork
    (fun a rows => (scanCachedArcRowsWithWork_spec (bitLength_fits_fin_labels n) a rows).1) encoded.1
  let out := unique.1.val.map CachedFinArc.arc
  (⟨(out : Multiset (Fin n × Fin n)),by simpa using unique.1.property.map CachedFinArc.arc_injective⟩,
    width.2+encoded.2+unique.2+5*out.length+8)

/-- The preparatory work depends only on the vertex and raw-row counts. -/
def steinerBinaryArcRowsWorkBudget (n rows : ℕ) : ℕ :=
  (7*n+3)+(2+rows*(2*boundedNatToBinaryWorkBudget n+7))+(10*n+36)*(rows+1)^2+5*rows+8

theorem prepareSteinerBinaryArcRowsWithWork_spec {n : ℕ} (raw : List (Fin n × Fin n)) :
    let out := prepareSteinerBinaryArcRowsWithWork raw
    raw.toFinset = out.1 ∧ out.1.card ≤ raw.length ∧ out.2 ≤ steinerBinaryArcRowsWorkBudget n raw.length := by
  let width := bitLengthWithWork n
  let encoded := cacheBinaryArcRowsWithWork width.1 raw
  let cert := fun a rows => (scanCachedArcRowsWithWork_spec (bitLength_fits_fin_labels n) a rows).1
  let unique := dedupArcRowsUsingScan scanCachedArcRowsWithWork cert encoded.1
  let out := unique.1.val.map CachedFinArc.arc
  have widthLe : width.1 ≤ n := by
    rw [(bitLengthWithWork_spec n).1]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  obtain ⟨image,encoding⟩ := cacheBinaryArcRowsWithWork_spec (bitLength_fits_fin_labels n) raw
  change encoded.1.map CachedFinArc.arc = raw at image
  change encoded.2 ≤ 2+raw.length*(2*boundedNatToBinaryWorkBudget width.1+7) at encoding
  have count : encoded.1.length = raw.length := by
    rw [← List.length_map (f := CachedFinArc.arc),image]
  obtain ⟨members,kept,deduplication⟩ := dedupArcRowsUsingScan_spec scanCachedArcRowsWithWork cert
    (10*width.1+21) (fun a rows => (scanCachedArcRowsWithWork_spec (bitLength_fits_fin_labels n) a rows).2) encoded.1
  change unique.1.val.length ≤ encoded.1.length at kept
  change unique.2 ≤ (10*width.1+21+15)*(encoded.1.length+1)^2 at deduplication
  have outSize : out.length ≤ raw.length := by simpa only [out,List.length_map,count] using kept
  have equal : raw.toFinset = (prepareSteinerBinaryArcRowsWithWork raw).1 := by
    ext arc
    change arc ∈ raw.toFinset ↔ arc ∈ (out : Multiset (Fin n × Fin n))
    rw [List.mem_toFinset,Multiset.mem_coe,← image,List.mem_map,List.mem_map]
    exact ⟨fun ⟨a,member,eq⟩ => ⟨a,(members a).mpr member,eq⟩,
      fun ⟨a,member,eq⟩ => ⟨a,(members a).mp member,eq⟩⟩
  refine ⟨equal,outSize,?_⟩
  change width.2+encoded.2+unique.2+5*out.length+8 ≤ steinerBinaryArcRowsWorkBudget n raw.length
  have buildWidth : width.2 ≤ 7*n+3 := bitLengthWork_le n
  have oneEncoding : boundedNatToBinaryWorkBudget width.1 ≤ boundedNatToBinaryWorkBudget n := by
    unfold boundedNatToBinaryWorkBudget
    exact Nat.add_le_add_left (Nat.mul_le_mul widthLe (by omega)) 2
  have encodeRoom : encoded.2 ≤ 2+raw.length*(2*boundedNatToBinaryWorkBudget n+7) :=
    encoding.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) 2)
  have dedupRoom : unique.2 ≤ (10*n+36)*(raw.length+1)^2 := by
    rw [count] at deduplication
    exact deduplication.trans (Nat.mul_le_mul_right _ (by omega))
  unfold steinerBinaryArcRowsWorkBudget
  omega

/-- The binary arc preparation has cubic recorded work in the vertex
and raw-row counts. -/
theorem steinerBinaryArcRowsWorkBudget_cubic (n rows : ℕ) :
    steinerBinaryArcRowsWorkBudget n rows ≤ 100*(n+rows+1)^3 := by
  let size := n+rows+1
  have nLe : n ≤ size := by dsimp only [size]; omega
  have rowsLe : rows ≤ size := by dsimp only [size]; omega
  have rowsNext : rows+1 ≤ size := by dsimp only [size]; omega
  have positive : 0 < size := by dsimp only [size]; omega
  have square : size ≤ size^2 := by
    have growth := Nat.pow_le_pow_right positive (show 1 ≤ 2 by decide)
    simpa only [pow_one] using growth
  have cube : size ≤ size^3 := by
    have growth := Nat.pow_le_pow_right positive (show 1 ≤ 3 by decide)
    simpa only [pow_one] using growth
  have squarePositive : 1 ≤ size^2 := Nat.one_le_pow _ _ positive
  have encodeOne : 2*boundedNatToBinaryWorkBudget n+7 ≤ 25*size^2 := by
    have product : n*(2*n+5) ≤ 7*size^2 := by
      have room : 2*n+5 ≤ 7*size := by omega
      calc
        _ ≤ size*(7*size) := Nat.mul_le_mul nLe room
        _ = _ := by ring
    unfold boundedNatToBinaryWorkBudget
    omega
  have encode : rows*(2*boundedNatToBinaryWorkBudget n+7) ≤ 25*size^3 := by
    calc
      _ ≤ size*(25*size^2) := Nat.mul_le_mul rowsLe encodeOne
      _ = _ := by ring
  have scan : (10*n+36)*(rows+1)^2 ≤ 46*size^3 := by
    have head : 10*n+36 ≤ 46*size := by omega
    calc
      _ ≤ (46*size)*size^2 := Nat.mul_le_mul head (Nat.pow_le_pow_left rowsNext _)
      _ = _ := by ring
  have fixed : 7*n+3+2+5*rows+8 ≤ 25*size^3 := by omega
  unfold steinerBinaryArcRowsWorkBudget
  change _ ≤ 100*size^3
  omega

end OnlineReachabilityPreservers
