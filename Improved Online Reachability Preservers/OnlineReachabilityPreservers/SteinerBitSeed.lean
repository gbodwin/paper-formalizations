import OnlineReachabilityPreservers.SteinerBitCursor

/-! Decode the three independent seed components consecutively from a finite fair-bit prefix. -/

namespace OnlineReachabilityPreservers

private def consumeBitArray {A S : Type*} : (count : ℕ) →
    (Fin count → S → Option (A × S)) → S →
      Option ((Fin count → A) × S)
  | 0, _, bits => some (Fin.elim0, bits)
  | count+1, read, bits => (read 0 bits).bind fun current =>
      (consumeBitArray count (fun i => read i.succ) current.2).map fun tail =>
        (Fin.cases current.1 tail.1,tail.2)

private def consumeBitArrayLoop {A S : Type*} (count : ℕ)
    (read : Fin count → S → Option (A × S)) :
    (remaining : ℕ) → S → (values : Array A) → values.size + remaining = count →
    Option (Array A × S)
  | 0, bits, values, _ => some (values, bits)
  | remaining+1, bits, values, fits =>
    match read ⟨values.size, by omega⟩ bits with
    | none => none
    | some (value, suffix) =>
        consumeBitArrayLoop count read remaining suffix (values.push value) (by simp only [Array.size_push]; omega)

private theorem consumeBitArrayLoop_eq {A S : Type*} (count : ℕ)
    (read : Fin count → S → Option (A × S)) (remaining : ℕ)
    (bits : S) (values : Array A) (fits : values.size + remaining = count) :
    consumeBitArrayLoop count read remaining bits values fits =
      (consumeBitArray remaining (fun i => read ⟨values.size + i.val, by omega⟩) bits).map
        (fun (new, suffix) => (values ++ Array.ofFn new, suffix)) := by
  induction remaining generalizing bits values with
  | zero => simp [consumeBitArrayLoop, consumeBitArray]
  | succ remaining ih =>
    simp only [consumeBitArrayLoop, consumeBitArray, Fin.val_zero, Nat.add_zero]
    cases result : read ⟨values.size, by omega⟩ bits with
    | none => rfl
    | some next =>
      obtain ⟨value, suffix⟩ := next
      simp only [Option.bind_some]
      rw [ih]
      have reads : (fun i : Fin remaining => read ⟨(values.push value).size + i.val, by simp only [Array.size_push]; omega⟩) =
          (fun i : Fin remaining => read ⟨values.size+i.succ.val, by omega⟩) := by
        funext i
        congr 1
        apply Fin.ext
        simp only [Array.size_push, Fin.val_succ]
        omega
      rw [reads]
      cases consumeBitArray remaining (fun i => read ⟨values.size + i.succ.val, by omega⟩) suffix with
      | none => rfl
      | some rest =>
        obtain ⟨new, unread⟩ := rest
        simp only [Option.map_some]
        rw [Array.ofFn_succ', ← Array.append_assoc]
        simp only [Fin.cases_zero, Fin.cases_succ, ← Array.push_eq_append]

private def consumeBitArrayTail {A S : Type*} (count : ℕ)
    (read : Fin count → S → Option (A × S)) (bits : S) :
    Option ((Fin count → A) × S) :=
  let initial : Array A := Array.emptyWithCapacity count
  match parsed : consumeBitArrayLoop count read count bits initial (by simp [initial]) with
  | none => none
  | some (values, rest) =>
      have size : values.size = count := by
        have eq := consumeBitArrayLoop_eq count read count bits initial (by simp [initial])
        simp only [initial, Array.emptyWithCapacity_eq, Array.size_empty, Nat.zero_add, Array.empty_append] at eq
        have comparison := parsed.symm.trans eq
        cases answer : consumeBitArray count read bits with
        | none => simp [answer] at comparison
        | some result =>
          simp [answer] at comparison
          simp [comparison.1]
      some (fun i => values[i.val]'(size.symm ▸ i.isLt), rest)

@[csimp] private theorem consumeBitArray_eq_tail : @consumeBitArray = @consumeBitArrayTail := by
  funext A S count read bits
  unfold consumeBitArrayTail
  dsimp only
  have eq := consumeBitArrayLoop_eq count read count bits (Array.emptyWithCapacity count) (by simp)
  simp only [Array.emptyWithCapacity_eq, Array.size_empty, Nat.zero_add, Array.empty_append] at eq
  split
  · rename_i parsed
    simp only [Array.emptyWithCapacity_eq] at parsed
    rw [parsed] at eq
    cases answer : consumeBitArray count read bits <;> simp [answer] at eq ⊢
  · rename_i values rest parsed
    simp only [Array.emptyWithCapacity_eq] at parsed
    rw [parsed] at eq
    cases answer : consumeBitArray count read bits with
    | none => simp [answer] at eq
    | some result =>
      obtain ⟨new, unread⟩ := result
      simp [answer] at eq
      apply congrArg some
      apply Prod.ext
      · funext i
        simp only [eq.1, Array.getElem_ofFn]
      · exact eq.2.symm

private theorem consumeBitArray_chunks {A : Type*} {count : ℕ}
    (read : Fin count → List Bool → Option (A × List Bool)) (chunks : Fin count → List Bool)
    (values : Fin count → A) (rest : List Bool)
    (ok : ∀ i tail, read i (chunks i ++ tail) = some (values i,tail)) :
    consumeBitArray count read ((List.ofFn chunks).flatten ++ rest) = some (values,rest) := by
  induction count with
  | zero =>
    have same : (Fin.elim0 : Fin 0 → A) = values := funext (fun i => i.elim0)
    simp [consumeBitArray, same]
  | succ count ih =>
    have tail := ih (fun i => read i.succ) (fun i => chunks i.succ) (fun i => values i.succ)
      (fun i => ok i.succ)
    rw [List.ofFn_succ, List.flatten_cons, List.append_assoc, consumeBitArray, ok 0,
      Option.bind_some, tail]
    simp
    exact funext (Fin.cases rfl (fun _ => rfl))

private theorem consumeBitArray_chunks_iff {A : Type*} {count : ℕ}
    (read : Fin count → List Bool → Option (A × List Bool)) (chunks : Fin count → List Bool)
    (values : Fin count → A) (rest : List Bool) (event : Fin count → Prop)
    (exactLength : ∀ i source suffix, read i source = some (values i,suffix) →
      source.drop (chunks i).length = suffix)
    (readsEvent : ∀ i tail, read i (chunks i ++ tail) = some (values i,tail) ↔ event i) :
    consumeBitArray count read ((List.ofFn chunks).flatten ++ rest) = some (values,rest) ↔
      ∀ i, event i := by
  refine ⟨?_, fun hits => consumeBitArray_chunks read chunks values rest
    (fun i tail => (readsEvent i tail).mpr (hits i))⟩
  induction count with
  | zero => exact fun _ i => i.elim0
  | succ count ih =>
    intro done
    let tail := (List.ofFn fun i : Fin count => chunks i.succ).flatten ++ rest
    rw [List.ofFn_succ, List.flatten_cons, List.append_assoc, consumeBitArray, Option.bind_eq_some_iff] at done
    obtain ⟨⟨value,afterFirst⟩,first,next⟩ := done
    obtain ⟨⟨remaining,afterLast⟩,more,out⟩ := Option.map_eq_some_iff.mp next
    have same : Fin.cases value remaining = values := congrArg Prod.fst out
    have head : value = values 0 := congrFun same 0
    have suffix : remaining = fun i => values i.succ := funext (fun i => congrFun same i.succ)
    have last : afterLast = rest := congrArg Prod.snd out
    subst value remaining afterLast
    have drop := exactLength 0 _ _ first
    change (chunks 0 ++ tail).drop (chunks 0).length = afterFirst at drop
    rw [List.drop_append_length] at drop
    subst afterFirst
    refine Fin.cases ((readsEvent 0 tail).mp first) ?_
    exact ih (fun i => read i.succ) (fun i => chunks i.succ) (fun i => values i.succ) (fun i => event i.succ)
      (fun i => exactLength i.succ) (fun i => readsEvent i.succ) more

private theorem consumeBitArray_suffix {A : Type*} {count : ℕ}
    (read : Fin count → List Bool → Option (A × List Bool)) (used : A → ℕ)
    (values : Fin count → A) (bits rest : List Bool)
    (spec : ∀ i source v suffix, read i source = some (v,suffix) →
      suffix.length + used v = source.length ∧ source.drop (used v) = suffix)
    (done : consumeBitArray count read bits = some (values,rest)) :
    rest.length + (∑ i, used (values i)) = bits.length ∧ bits.drop (∑ i, used (values i)) = rest := by
  induction count generalizing bits with
  | zero =>
    simp [consumeBitArray] at done
    simp [← done.2]
  | succ count ih =>
    rw [consumeBitArray, Option.bind_eq_some_iff] at done
    obtain ⟨⟨value,tail⟩,first,next⟩ := done
    obtain ⟨⟨remaining,unread⟩,more,out⟩ := Option.map_eq_some_iff.mp next
    have same : Fin.cases value remaining = values := congrArg Prod.fst out
    have suffixEq : unread = rest := congrArg Prod.snd out
    subst unread
    obtain ⟨firstLen,firstDrop⟩ := spec 0 bits value tail first
    obtain ⟨moreLen,moreDrop⟩ := ih (fun i => read i.succ) remaining tail (fun i => spec i.succ) more
    rw [← same, Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    constructor
    · omega
    · rw [← moreDrop, ← firstDrop, List.drop_drop]

private theorem consumeBitArray_stage_end {A : Type*} {count : ℕ}
    (read : Fin count → List Bool → Option (A × List Bool)) (used : A → ℕ)
    (rows : Fin count → List Bool) (values : Fin count → A) (tail suffix : List Bool)
    (spec : ∀ i source v after, read i source = some (v,after) →
      after.length + used v = source.length ∧ source.drop (used v) = after)
    (width : ∀ i, (rows i).length = used (values i))
    (done : consumeBitArray count read ((List.ofFn rows).flatten ++ tail) = some (values,suffix)) :
    suffix = tail := by
  have len : (List.ofFn rows).flatten.length = ∑ i, used (values i) := by
    rw [List.length_flatten, List.map_ofFn]
    simp only [Function.comp_def, width, List.sum_ofFn]
  have drop := (consumeBitArray_suffix read used values _ suffix spec done).2
  rwa [← len, List.drop_append_length, eq_comm] at drop

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Index each finite seed array in a given order. The first stream
segment has fixed-width grid choices. The next two use rejection for
the hub draws and the thin choices, respectively. -/
def decodeCompleteSteinerSeed (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (bits : List Bool) :
    Option ((EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G) ×
      ((Fin (completeSteinerHubCount V) → ℕ) × (G → ℕ)) × List Bool) :=
  (consumeBitArray (A := Fin (forestSeedSize (forestScale G height)))
    (Fintype.card (EarlySeedCoordinate G height))
    (fun _ => consumeFairWord ((forestScale G height).log2+1)) bits).bind fun early =>
    (consumeBitArray (A := Fin (Fintype.card V) × ℕ) (completeSteinerHubCount V)
      (fun _ => consumeFairIndex (Fintype.card V)) early.2).bind fun hubs =>
      (consumeBitArray (A := Fin G.card × ℕ) G.card (fun _ => consumeFairIndex G.card) hubs.2).map fun thin =>
        let earlySeed := (earlySeedCoordinates G height).symm (early.1 ∘ coordinates)
        let hubSeed := fun i => vertices.symm ((hubs.1 i).1)
        let thinSeed := fun e => (thin.1 (arcs e)).1
        ((earlySeed, hubSeed, thinSeed), (fun i => (hubs.1 i).2, fun e => (thin.1 (arcs e)).2), thin.2)

/-- The bit count for a successful complete decoding is the fixed early
budget and the full words consumed by the two rejection phases. -/
theorem decodeCompleteSteinerSeed_suffix (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) {bits rest : List Bool}
    {early : EarlyRoundSample G height} {hubs : Fin (completeSteinerHubCount V) → V} {thin : ThinSample G}
    {hubRejects : Fin (completeSteinerHubCount V) → ℕ} {thinRejects : G → ℕ}
    (done : decodeCompleteSteinerSeed G height coordinates vertices arcs bits =
      some ((early,hubs,thin),(hubRejects,thinRejects),rest)) :
    let used := earlySeedBits G height +
      (∑ i, uniformProposalWidth (Fintype.card V)*(hubRejects i+1)) +
      (∑ e, uniformProposalWidth G.card*(thinRejects e+1))
    rest.length + used = bits.length ∧ bits.drop used = rest := by
  dsimp only
  rw [decodeCompleteSteinerSeed, Option.bind_eq_some_iff] at done
  obtain ⟨⟨earlyWords,hubBits⟩,earlyRead,more⟩ := done
  obtain ⟨⟨hubWords,thinBits⟩,hubRead,last⟩ := Option.bind_eq_some_iff.mp more
  obtain ⟨⟨thinWords,suffix⟩,thinRead,out⟩ := Option.map_eq_some_iff.mp last
  have hubEq : (fun i => (hubWords i).2) = hubRejects := congrArg (fun r => r.2.1.1) out
  have thinEq : (fun e => (thinWords (arcs e)).2) = thinRejects := congrArg (fun r => r.2.1.2) out
  have suffixEq : suffix = rest := congrArg (fun r => r.2.2) out
  subst suffix
  obtain ⟨earlyLen, earlyDrop⟩ := consumeBitArray_suffix _ (fun _ => (forestScale G height).log2+1)
    earlyWords bits hubBits (fun _ _ _ _ => consumeFairWord_suffix) earlyRead
  obtain ⟨hubLen, hubDrop⟩ := consumeBitArray_suffix _
    (fun word => uniformProposalWidth (Fintype.card V)*(word.2+1))
    hubWords hubBits thinBits (fun _ _ _ _ => consumeFairIndex_suffix) hubRead
  obtain ⟨thinLen, thinDrop⟩ := consumeBitArray_suffix _ (fun word => uniformProposalWidth G.card*(word.2+1))
    thinWords thinBits rest (fun _ _ _ _ => consumeFairIndex_suffix) thinRead
  have earlyUsed : (∑ _ : Fin (Fintype.card (EarlySeedCoordinate G height)),
      ((forestScale G height).log2+1)) = earlySeedBits G height := by simp [earlySeedBits]
  have hubUsed : (∑ i, uniformProposalWidth (Fintype.card V)*((hubWords i).2+1)) =
      ∑ i, uniformProposalWidth (Fintype.card V)*(hubRejects i+1) := by simp only [← hubEq]
  have thinUsed : (∑ i, uniformProposalWidth G.card*((thinWords i).2+1)) =
      ∑ e, uniformProposalWidth G.card*(thinRejects e+1) := by
    rw [← thinEq]
    exact (Fintype.sum_equiv arcs _ _ (fun _ => rfl)).symm
  simp only [earlyUsed] at earlyLen earlyDrop
  simp only [hubUsed] at hubLen hubDrop
  simp only [thinUsed] at thinLen thinDrop
  constructor
  · omega
  · rw [← thinDrop, ← hubDrop, ← earlyDrop, List.drop_drop, List.drop_drop]
    simp only [Nat.add_assoc]

/-- At fixed rejection counts, the complete decoder's outcome on consecutive
bit segments is exactly the conjunction of the single-coordinate events. -/
theorem decodeCompleteSteinerSeed_chunks_iff (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ)
    (earlyBits : Fin (Fintype.card (EarlySeedCoordinate G height)) → Fin ((forestScale G height).log2+1) → Bool)
    (hubBits : ∀ i, Fin ((hubRejects i+1)*uniformProposalWidth (Fintype.card V)) → Bool)
    (thinBits : ∀ i, Fin ((thinRejects (arcs.symm i)+1)*uniformProposalWidth G.card) → Bool)
    (rest : List Bool) :
    let earlyWords := (List.ofFn fun i => List.ofFn (earlyBits i)).flatten
    let hubWords := (List.ofFn fun i => List.ofFn (hubBits i)).flatten
    let thinWords := (List.ofFn fun i => List.ofFn (thinBits i)).flatten
    decodeCompleteSteinerSeed G height coordinates vertices arcs (earlyWords ++ hubWords ++ thinWords ++ rest) =
      some ((early,hubs,thin),(hubRejects,thinRejects),rest) ↔
      (∀ i, earlyBits i = earlySeedBitWords G height early (coordinates.symm i)) ∧
      (∀ i, hubBits i ∈ flatBitRetryLastEvent (hubRejects i) (vertices (hubs i)) []) ∧
      (∀ i, thinBits i ∈ flatBitRetryLastEvent (thinRejects (arcs.symm i)) (thin (arcs.symm i)) []) := by
  dsimp only
  let earlyWords := fun i => List.ofFn (earlyBits i)
  let earlyValues := fun i => earlySeedCoordinates G height early (coordinates.symm i)
  let hubWords := fun i => List.ofFn (hubBits i)
  let hubValues := fun i => (vertices (hubs i),hubRejects i)
  let thinWords := fun i => List.ofFn (thinBits i)
  let thinValues := fun i => (thin (arcs.symm i),thinRejects (arcs.symm i))
  let earlyTest := fun i => earlyBits i = earlySeedBitWords G height early (coordinates.symm i)
  let hubTest := fun i => hubBits i ∈ flatBitRetryLastEvent (hubRejects i) (vertices (hubs i)) []
  let thinTest := fun i => thinBits i ∈ flatBitRetryLastEvent (thinRejects (arcs.symm i)) (thin (arcs.symm i)) []
  have earlyWordReads (i : Fin _) (suffix : List Bool) :
      consumeFairWord ((forestScale G height).log2+1) (earlyWords i ++ suffix) =
        some (earlyValues i,suffix) ↔ earlyTest i := by
    change consumeFairWord _ (List.ofFn (earlyBits i) ++ suffix) = _ ↔ _
    rw [consumeFairWord_ofFn]
    let codec := uniformBitsEquiv ((forestScale G height).log2+1)
    have decoded := codec.apply_symm_apply (earlyValues i)
    change some (codec (earlyBits i),suffix) = some (earlyValues i,suffix) ↔ earlyTest i
    simp only [Option.some.injEq, Prod.mk.injEq, eq_self, and_true]
    change codec (earlyBits i) = earlyValues i ↔ earlyBits i = codec.symm (earlyValues i)
    exact ⟨fun h => codec.injective (h.trans decoded.symm), fun h => (congrArg codec h).trans decoded⟩
  have hubWordReads (i : Fin _) (suffix : List Bool) :
      consumeFairIndex (Fintype.card V) (hubWords i ++ suffix) = some (hubValues i,suffix) ↔ hubTest i :=
    flatBitRetryLastEvent_read (Fintype.card_pos_iff.mpr ⟨hubs i⟩) suffix
  have thinWordReads (i : Fin _) (suffix : List Bool) :
      consumeFairIndex G.card (thinWords i ++ suffix) = some (thinValues i,suffix) ↔ thinTest i :=
    flatBitRetryLastEvent_read (Finset.card_pos.mpr ⟨(arcs.symm i).val,(arcs.symm i).property⟩) suffix
  let hubTail := (List.ofFn hubWords).flatten ++ ((List.ofFn thinWords).flatten ++ rest)
  let thinTail := (List.ofFn thinWords).flatten ++ rest
  have earlyRead := consumeBitArray_chunks_iff _ earlyWords earlyValues hubTail earlyTest
    (fun i _ _ ok => by simpa only [earlyWords, List.length_ofFn] using (consumeFairWord_suffix ok).2) earlyWordReads
  have hubRead := consumeBitArray_chunks_iff _ hubWords hubValues thinTail hubTest
    (fun i _ _ ok => by simpa only [hubWords, hubValues, List.length_ofFn, Nat.mul_comm] using
      (consumeFairIndex_suffix ok).2) hubWordReads
  have thinRead := consumeBitArray_chunks_iff _ thinWords thinValues rest thinTest
    (fun i _ _ ok => by simpa only [thinWords, thinValues, List.length_ofFn, Nat.mul_comm] using
      (consumeFairIndex_suffix ok).2) thinWordReads
  simp only [List.append_assoc]
  change decodeCompleteSteinerSeed G height coordinates vertices arcs
    ((List.ofFn earlyWords).flatten ++ hubTail) = _ ↔ _
  constructor
  · intro done
    rw [decodeCompleteSteinerSeed, Option.bind_eq_some_iff] at done
    obtain ⟨⟨earlyOut,afterEarly⟩,first,next⟩ := done
    obtain ⟨⟨hubOut,afterHub⟩,second,last⟩ := Option.bind_eq_some_iff.mp next
    obtain ⟨⟨thinOut,afterThin⟩,third,out⟩ := Option.map_eq_some_iff.mp last
    have earlyEq : earlyOut = earlyValues := by
      have agreed : earlyOut ∘ coordinates = earlySeedCoordinates G height early :=
        (earlySeedCoordinates G height).symm.injective (by simpa using congrArg (fun r => r.1.1) out)
      funext i
      simpa [earlyValues, Function.comp_def] using congrFun agreed (coordinates.symm i)
    have hubEq : hubOut = hubValues := by
      funext i
      apply Prod.ext
      · exact vertices.symm.injective (by simpa [hubValues] using congrFun (congrArg (fun r => r.1.2.1) out) i)
      · exact congrFun (congrArg (fun r => r.2.1.1) out) i
    have thinEq : thinOut = thinValues := by
      funext i
      apply Prod.ext
      · simpa [thinValues] using congrFun (congrArg (fun r => r.1.2.2) out) (arcs.symm i)
      · simpa [thinValues] using congrFun (congrArg (fun r => r.2.1.2) out) (arcs.symm i)
    have restEq : afterThin = rest := congrArg (fun r => r.2.2) out
    subst earlyOut hubOut thinOut afterThin
    have earlyEnd := consumeBitArray_stage_end _ (fun _ => (forestScale G height).log2+1)
      earlyWords earlyValues hubTail afterEarly (fun _ _ _ _ => consumeFairWord_suffix)
      (fun i => List.length_ofFn) first
    subst afterEarly
    have hubEnd := consumeBitArray_stage_end _ (fun v => uniformProposalWidth (Fintype.card V)*(v.2+1))
      hubWords hubValues thinTail afterHub (fun _ _ _ _ => consumeFairIndex_suffix)
      (fun i => by simp [hubWords, hubValues, Nat.mul_comm]) second
    subst afterHub
    exact ⟨earlyRead.mp first, hubRead.mp second, thinRead.mp third⟩
  · rintro ⟨first,second,third⟩
    rw [decodeCompleteSteinerSeed, earlyRead.mpr first, Option.bind_some, hubRead.mpr second,
      Option.bind_some, thinRead.mpr third]
    simp [earlyValues, hubValues, thinValues, Function.comp_def]

/-- The finite cylinder for one complete decoded seed and fixed rejection
counts, with its coordinates written as successive stream segments. -/
noncomputable def completeSteinerBitSeedEvent (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ) (rest : List Bool) :
    Finset ((Fin (Fintype.card (EarlySeedCoordinate G height)) → Fin ((forestScale G height).log2+1) → Bool) ×
      (∀ i, Fin ((hubRejects i+1)*uniformProposalWidth (Fintype.card V)) → Bool) ×
      (∀ i, Fin ((thinRejects (arcs.symm i)+1)*uniformProposalWidth G.card) → Bool)) := by
  classical
  exact Finset.univ.filter fun (earlyBits,hubBits,thinBits) =>
    let fixed := (List.ofFn fun i => List.ofFn (earlyBits i)).flatten
    let hub := (List.ofFn fun i => List.ofFn (hubBits i)).flatten
    let arc := (List.ofFn fun i => List.ofFn (thinBits i)).flatten
    decodeCompleteSteinerSeed G height coordinates vertices arcs (fixed ++ hub ++ arc ++ rest) =
      some ((early,hubs,thin),(hubRejects,thinRejects),rest)

theorem completeSteinerBitSeedEvent_suffix_eq (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ) (rest tail : List Bool) :
    completeSteinerBitSeedEvent G height coordinates vertices arcs early hubs thin hubRejects thinRejects rest =
      completeSteinerBitSeedEvent G height coordinates vertices arcs early hubs thin hubRejects thinRejects tail := by
  classical
  ext input
  rcases input with ⟨earlyBits,hubBits,thinBits⟩
  have outcome suffix := decodeCompleteSteinerSeed_chunks_iff G height coordinates vertices arcs early hubs thin
    hubRejects thinRejects earlyBits hubBits thinBits suffix
  dsimp only at outcome
  simp only [completeSteinerBitSeedEvent, Finset.mem_filter, Finset.mem_univ, true_and, outcome]

theorem completeSteinerBitSeedEvent_probability (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (hubRejects : Fin (completeSteinerHubCount V) → ℕ) (thinRejects : G → ℕ) (rest : List Bool) :
    let earlyHit := ({earlySeedBitWords G height early ∘ coordinates.symm} : Finset _)
    let hubHits := fun i => flatBitRetryLastEvent (hubRejects i) (vertices (hubs i)) []
    let thinHits := fun i => flatBitRetryLastEvent (thinRejects (arcs.symm i)) (thin (arcs.symm i)) []
    finiteProbability (completeSteinerBitSeedEvent G height coordinates vertices arcs early hubs thin
      hubRejects thinRejects rest) =
        finiteProbability earlyHit * ((∏ i, finiteProbability (hubHits i)) * ∏ i, finiteProbability (thinHits i)) := by
  classical
  dsimp only
  let earlyHit := ({earlySeedBitWords G height early ∘ coordinates.symm} : Finset _)
  let hubHits := fun i => flatBitRetryLastEvent (hubRejects i) (vertices (hubs i)) []
  let thinHits := fun i => flatBitRetryLastEvent (thinRejects (arcs.symm i)) (thin (arcs.symm i)) []
  have eventEq : completeSteinerBitSeedEvent G height coordinates vertices arcs early hubs thin hubRejects thinRejects rest =
      earlyHit ×ˢ (Fintype.piFinset hubHits ×ˢ Fintype.piFinset thinHits) := by
    ext input
    rcases input with ⟨earlyBits,hubBits,thinBits⟩
    simp only [completeSteinerBitSeedEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Fintype.mem_piFinset, earlyHit, Finset.mem_singleton]
    have decoded := decodeCompleteSteinerSeed_chunks_iff G height coordinates vertices arcs early hubs thin
      hubRejects thinRejects earlyBits hubBits thinBits rest
    dsimp only at decoded
    rw [decoded]
    simp only [funext_iff, Function.comp_apply, hubHits, thinHits]
  rw [eventEq, finiteProbability_product, finiteProbability_product]
  simp only [finiteProbability, Fintype.card_piFinset, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]
  rfl

/-- Summing the independent first-success probabilities for each decoded
coordinate gives the uniform seed law of the fixed-trace algorithm. -/
theorem completeSteinerBitSeed_uniform (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) :
    let fixed := finiteProbability ({earlySeedBitWords G height early ∘ coordinates.symm} : Finset _)
    let hub := ∏ i, ∑' k, finiteProbability (flatBitRetryLastEvent k (vertices (hubs i)) [])
    let arc := ∏ i : Fin G.card, ∑' k, finiteProbability (flatBitRetryLastEvent k (thin (arcs.symm i)) [])
    fixed * (hub * arc) =
      finiteProbability ({(early,hubs,thin)} : Finset (EarlyRoundSample G height × _ × ThinSample G)) := by
  classical
  dsimp only
  let encode := (earlySeedBitWords G height).trans (Equiv.arrowCongr coordinates (Equiv.refl _))
  have first : finiteProbability ({earlySeedBitWords G height early ∘ coordinates.symm} : Finset _) =
      finiteProbability ({early} : Finset (EarlyRoundSample G height)) := by
    simp only [finiteProbability, Finset.card_singleton, Fintype.card_congr encode]
  have hubMass (i : Fin (completeSteinerHubCount V)) :
      (∑' k, finiteProbability (flatBitRetryLastEvent k (vertices (hubs i)) [])) =
        1/(Fintype.card V:ℝ) := flatBitRetry_uniform (Fintype.card_pos_iff.mpr ⟨hubs i⟩) _ []
  have arcMass (i : Fin G.card) :
      (∑' k, finiteProbability (flatBitRetryLastEvent k (thin (arcs.symm i)) [])) = 1/(G.card:ℝ) :=
    flatBitRetry_uniform (Finset.card_pos.mpr ⟨(arcs.symm i).val,(arcs.symm i).property⟩) _ []
  have hub : (∏ _ : Fin (completeSteinerHubCount V), 1/(Fintype.card V:ℝ)) =
      finiteProbability ({hubs} : Finset _) := by
    simp [finiteProbability, Fintype.card_pi]
  have arc : (∏ _ : Fin G.card, 1/(G.card:ℝ)) = finiteProbability ({thin} : Finset _) := by
    simp [finiteProbability, Fintype.card_pi]
  simp_rw [first, hubMass, arcMass, hub, arc, ← finiteProbability_product ({hubs} : Finset _) {thin},
    ← finiteProbability_product ({early} : Finset _) ({hubs} ×ˢ {thin})]
  simp

/-- Use the actual consumption on the decoder's first-success events.
The aggregate expected bit count is polynomial at fixed height. -/
theorem completeSteinerBitConsumption_polynomial (G : Arcs V) (height : ℕ)
    (draw : Fin (completeSteinerHubCount V) → V) :
    let readBits := fun N => ∑' k : ℕ, (uniformProposalWidth N : ℝ)*(k+1)*
      (∑ t : Fin N, finiteProbability (flatBitRetryLastEvent k t []))
    (earlySeedBits G height : ℝ) +
      (∑ _ : Fin (completeSteinerHubCount V), readBits (Fintype.card V)) + (∑ _ : G, readBits G.card) ≤
      completeSteinerSeedPolynomial (Fintype.card V) G.card height := by
  intro readBits
  have hub (i : Fin (completeSteinerHubCount V)) :
      readBits (Fintype.card V) = expectedRejectionBits (Fintype.card V) :=
    flatBitRetry_expectedBits_eq (Fintype.card_pos_iff.mpr ⟨draw i⟩) []
  have arc (e : G) : readBits G.card = expectedRejectionBits G.card :=
    flatBitRetry_expectedBits_eq (Finset.card_pos.mpr ⟨e.val,e.property⟩) []
  have hubSum := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin (completeSteinerHubCount V))) = Finset.univ)
    (fun i _ => hub i)
  have arcSum := Finset.sum_congr (rfl : (Finset.univ : Finset G) = Finset.univ) (fun e _ => arc e)
  rw [hubSum, arcSum]
  simpa only [completeSteinerExpectedSeedBits, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul] using completeSteinerExpectedSeedBits_polynomial G height

/-- Count coordinates by the radix sizes, without materializing the coordinate array. -/
def earlySeedCoordinateCountByWidth (V : Type*) [Fintype V] (height width : ℕ) : ℕ :=
  let n := Fintype.card V
  let histories := ∑ k : Fin (height+1), n ^ k.val
  earlyTrialCount V height * (n * (width * (2 * histories + 1)))

theorem earlySeedCoordinateCountByWidth_eq (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) :
    earlySeedCoordinateCountByWidth V height width = Fintype.card (EarlySeedCoordinate G height) := by
  rw [earlySeedCoordinate_card, width_eq, heightNode_card]
  rfl

/-- Compute the tighter bit bound with a previously prepared word width. -/
def completeSteinerSeedBitBoundAtWidth (G : Arcs V) (height width : ℕ) : ℕ :=
  earlySeedCoordinateCountByWidth V height width * width +
    completeSteinerHubCount V * (2 * uniformProposalWidth (Fintype.card V)) +
    G.card * (2 * uniformProposalWidth G.card)

theorem completeSteinerSeedBitBoundAtWidth_eq (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) :
    completeSteinerSeedBitBoundAtWidth G height width = completeSteinerSeedBitBound G height := by
  unfold completeSteinerSeedBitBoundAtWidth completeSteinerSeedBitBound earlySeedBits
  rw [earlySeedCoordinateCountByWidth_eq G height width width_eq, width_eq]

/-- The stored words in the order selected by the early seed index. -/
abbrev IndexedEarlySeedWords (G : Arcs V) (height : ℕ) :=
  Fin (Fintype.card (EarlySeedCoordinate G height)) → Fin (forestSeedSize (forestScale G height))

@[inline] private def earlySeedWordsAtWidth (G : Arcs V) (height width count : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (count_eq : count = Fintype.card (EarlySeedCoordinate G height))
    (early : Fin count → Fin (2^width)) : IndexedEarlySeedWords G height := fun i =>
  Fin.cast (congrArg (fun w : ℕ => 2^w) width_eq) (early (Fin.cast count_eq.symm i))

@[inline] private def assembleSeedAtWidth (G : Arcs V) (height width count : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (count_eq : count = Fintype.card (EarlySeedCoordinate G height))
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : Fin count → Fin (2^width)) (hubs : Fin (completeSteinerHubCount V) → Fin (Fintype.card V) × ℕ)
    (thin : Fin G.card → Fin G.card × ℕ) :
    (EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G) ×
      ((Fin (completeSteinerHubCount V) → ℕ) × (G → ℕ)) :=
  let words := earlySeedWordsAtWidth G height width count width_eq count_eq early
  let earlySeed := (earlySeedCoordinates G height).symm (fun c => words (coordinates c))
  let hubSeed := fun i => vertices.symm ((hubs i).1)
  let thinSeed := fun e => (thin (arcs e)).1
  ((earlySeed, hubSeed, thinSeed), (fun i => (hubs i).2, fun e => (thin (arcs e)).2))

private def decodeSeedAtWidthAndCount {S : Type*} (G : Arcs V) (height width count : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (count_eq : count = Fintype.card (EarlySeedCoordinate G height))
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (readWord : S → Option (Fin (2^width) × S))
    (readVertex : S → Option ((Fin (Fintype.card V) × ℕ) × S))
    (readArc : S → Option ((Fin G.card × ℕ) × S)) (bits : S) :
    Option ((EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G) ×
      ((Fin (completeSteinerHubCount V) → ℕ) × (G → ℕ)) × S) :=
  (consumeBitArray (A := Fin (2^width)) count (fun _ => readWord) bits).bind fun early =>
    (consumeBitArray (A := Fin (Fintype.card V) × ℕ) (completeSteinerHubCount V)
      (fun _ => readVertex) early.2).bind fun hubs =>
      (consumeBitArray (A := Fin G.card × ℕ) G.card (fun _ => readArc) hubs.2).map fun thin =>
        let seed := assembleSeedAtWidth G height width count width_eq count_eq coordinates vertices arcs early.1 hubs.1 thin.1
        (seed.1,seed.2,thin.2)

/-- Decode using a previously computed word width and an arithmetic coordinate count. -/
def decodeCompleteSteinerSeedAtWidth (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (bits : List Bool) :
    Option ((EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G) ×
      ((Fin (completeSteinerHubCount V) → ℕ) × (G → ℕ)) × List Bool) :=
  decodeSeedAtWidthAndCount G height width (earlySeedCoordinateCountByWidth V height width)
    width_eq (earlySeedCoordinateCountByWidth_eq G height width width_eq) coordinates vertices arcs
      (consumeFairWord width) (consumeFairIndex (Fintype.card V)) (consumeFairIndex G.card) bits

theorem decodeCompleteSteinerSeedAtWidth_eq (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (bits : List Bool) :
    decodeCompleteSteinerSeedAtWidth G height width width_eq coordinates vertices arcs bits =
      decodeCompleteSteinerSeed G height coordinates vertices arcs bits := by
  have exactDecode (width count : ℕ) (w : width = (forestScale G height).log2+1)
      (c : count = Fintype.card (EarlySeedCoordinate G height)) :
      decodeSeedAtWidthAndCount G height width count w c coordinates vertices arcs
        (consumeFairWord width) (consumeFairIndex (Fintype.card V)) (consumeFairIndex G.card) bits =
        decodeCompleteSteinerSeed G height coordinates vertices arcs bits := by
    subst width; subst count; rfl
  exact exactDecode width _ width_eq (earlySeedCoordinateCountByWidth_eq G height width width_eq)


private theorem consumeBitArray_cursor_spec {A : Type*} {budget : ℕ}
    (bits : Fin budget → Bool) (count : ℕ)
    (cursorRead : Fin count → BitCursor budget → Option (A × BitCursor budget))
    (listRead : Fin count → List Bool → Option (A × List Bool)) (cursor : BitCursor budget)
    (same : ∀ i c, (cursorRead i c).map (fun (value,next) => (value,cursorSuffix bits next)) =
      listRead i (cursorSuffix bits c)) :
    (consumeBitArray count cursorRead cursor).map (fun (value,next) => (value,cursorSuffix bits next)) =
      consumeBitArray count listRead (cursorSuffix bits cursor) := by
  induction count generalizing cursor with
  | zero => simp [consumeBitArray]
  | succ count ih =>
    simp only [consumeBitArray]
    cases head : cursorRead 0 cursor with
    | none =>
      have first : listRead 0 (cursorSuffix bits cursor) = none := by simpa only [head, Option.map_none] using (same 0 cursor).symm
      rw [first]
      rfl
    | some output =>
      obtain ⟨value,next⟩ := output
      have first : listRead 0 (cursorSuffix bits cursor) = some (value,cursorSuffix bits next) := by
        simpa only [head, Option.map_some] using (same 0 cursor).symm
      simp only [first, Option.bind_some]
      have rest := ih (fun i => cursorRead i.succ) (fun i => listRead i.succ) next (fun i c => same i.succ c)
      cases tail : consumeBitArray count (fun i => cursorRead i.succ) next with
      | none =>
        simp only [tail, Option.map_none] at rest
        rw [← rest]
        rfl
      | some suffix =>
        obtain ⟨values,last⟩ := suffix
        simp only [tail, Option.map_some] at rest
        rw [← rest]
        rfl

/-- Decode the same seed arrays, reading only the bits demanded by the cursor. -/
def decodeCompleteSteinerSeedCursorAtWidth (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    Option ((EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G) ×
      ((Fin (completeSteinerHubCount V) → ℕ) × (G → ℕ)) × BitCursor budget) :=
  decodeSeedAtWidthAndCount G height width (earlySeedCoordinateCountByWidth V height width)
    width_eq (earlySeedCoordinateCountByWidth_eq G height width width_eq) coordinates vertices arcs
      (consumeCursorWord bits width) (consumeCursorIndex bits (Fintype.card V))
      (consumeCursorIndex bits G.card) cursor

/-- The cursor decoder returns the original lists' seed, counts and unread suffix. -/
theorem decodeCompleteSteinerSeedCursorAtWidth_spec (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    (decodeCompleteSteinerSeedCursorAtWidth G height width width_eq coordinates vertices arcs bits cursor).map
      (fun (seed,counts,next) => (seed,counts,cursorSuffix bits next)) =
    decodeCompleteSteinerSeedAtWidth G height width width_eq coordinates vertices arcs (cursorSuffix bits cursor) := by
  let count := earlySeedCoordinateCountByWidth V height width
  let early := consumeBitArray (A := Fin (2^width)) count (fun _ => consumeCursorWord bits width) cursor
  have first := consumeBitArray_cursor_spec bits count (fun _ => consumeCursorWord bits width)
    (fun _ => consumeFairWord width) cursor (fun _ c => consumeCursorWord_spec bits width c)
  change early.map _ = _ at first
  unfold decodeCompleteSteinerSeedCursorAtWidth decodeCompleteSteinerSeedAtWidth decodeSeedAtWidthAndCount
  dsimp only
  change (early.bind _).map _ = _
  rw [← first]
  cases read : early with
  | none => rfl
  | some seed =>
    obtain ⟨earlyValues,next⟩ := seed
    simp only [Option.map_some, Option.bind_some]
    let hubs := consumeBitArray (A := Fin (Fintype.card V) × ℕ) (completeSteinerHubCount V)
      (fun _ => consumeCursorIndex bits (Fintype.card V)) next
    have second := consumeBitArray_cursor_spec bits (completeSteinerHubCount V)
      (fun _ => consumeCursorIndex bits (Fintype.card V)) (fun _ => consumeFairIndex (Fintype.card V)) next
      (fun _ c => consumeCursorIndex_spec bits (Fintype.card V) c)
    change hubs.map _ = _ at second
    change (hubs.bind _).map _ = _
    rw [← second]
    cases hubRead : hubs with
    | none => rfl
    | some seed =>
      obtain ⟨hubValues,afterHubs⟩ := seed
      simp only [Option.map_some, Option.bind_some]
      let thin := consumeBitArray (A := Fin G.card × ℕ) G.card (fun _ => consumeCursorIndex bits G.card) afterHubs
      have third := consumeBitArray_cursor_spec bits G.card (fun _ => consumeCursorIndex bits G.card)
        (fun _ => consumeFairIndex G.card) afterHubs (fun _ c => consumeCursorIndex_spec bits G.card c)
      change thin.map _ = _ at third
      change (thin.map _).map _ = _
      rw [← third]
      cases thinRead : thin <;> rfl

/-- Reading from the start of the cursor agrees with the finite-word decoder
on the sampled seed, including failure when there are too few bits. -/
theorem decodeCompleteSteinerSeedCursorAtWidth_seed_eq (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) :
    (decodeCompleteSteinerSeedCursorAtWidth G height width width_eq coordinates vertices arcs
      bits ⟨0, Nat.zero_le budget⟩).map Prod.fst =
    (decodeCompleteSteinerSeedAtWidth G height width width_eq coordinates vertices arcs
      (List.ofFn bits)).map Prod.fst := by
  have same := decodeCompleteSteinerSeedCursorAtWidth_spec G height width width_eq coordinates vertices arcs
    bits ⟨0, Nat.zero_le budget⟩
  simpa only [Option.map_map, Function.comp_def, cursorSuffix, List.drop_zero] using
    congrArg (Option.map Prod.fst) same

/-- The final cursor position records exactly the fixed early bits and
all complete proposals consumed by the two rejection phases. -/
theorem decodeCompleteSteinerSeedCursorAtWidth_position (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) {cursor next : BitCursor budget}
    {early : EarlyRoundSample G height} {hubs : Fin (completeSteinerHubCount V) → V} {thin : ThinSample G}
    {hubRejects : Fin (completeSteinerHubCount V) → ℕ} {thinRejects : G → ℕ}
    (success : decodeCompleteSteinerSeedCursorAtWidth G height width width_eq coordinates vertices arcs bits cursor =
      some ((early,hubs,thin),(hubRejects,thinRejects),next)) :
    let used := earlySeedBits G height +
      (∑ i, uniformProposalWidth (Fintype.card V)*(hubRejects i+1)) +
      (∑ e, uniformProposalWidth G.card*(thinRejects e+1))
    next.position = cursor.position + used := by
  have same := decodeCompleteSteinerSeedCursorAtWidth_spec G height width width_eq coordinates vertices arcs bits cursor
  rw [success, Option.map_some, decodeCompleteSteinerSeedAtWidth_eq] at same
  have length := (decodeCompleteSteinerSeed_suffix G height coordinates vertices arcs same.symm).1
  simp only [cursorSuffix, List.length_drop, List.length_ofFn] at length
  dsimp only
  have start := cursor.bounded
  have finish := next.bounded
  omega

private def consumeBitArrayWithEnd {A S : Type*} : (count : ℕ) →
    (Fin count → S → Option A × S) → S → Option (Fin count → A) × S
  | 0, _, state => (some Fin.elim0,state)
  | count+1, read, state =>
    match read 0 state with
    | (none, last) => (none,last)
    | (some head,next) =>
      let rest := consumeBitArrayWithEnd count (fun i => read i.succ) next
      (rest.1.map (Fin.cases head),rest.2)

private theorem consumeBitArrayWithEnd_agrees {A S : Type*} (count : ℕ)
    (read : Fin count → S → Option A × S) (reference : Fin count → S → Option (A × S))
    (state : S) (same : ∀ i s, let seen := read i s; seen.1.map (·,seen.2) = reference i s) :
    let result := consumeBitArrayWithEnd count read state
    result.1.map (·,result.2) = consumeBitArray count reference state := by
  induction count generalizing state with
  | zero => simp [consumeBitArrayWithEnd, consumeBitArray]
  | succ count ih =>
    dsimp only
    rw [consumeBitArrayWithEnd, consumeBitArray]
    have first := same 0 state
    cases front : read 0 state with
    | mk head next =>
      cases head with
      | none =>
        simp only [front, Option.map_none] at first
        rw [← first]
        rfl
      | some value =>
        simp only [front, Option.map_some] at first
        rw [← first]
        simp only [Option.bind_some]
        have tail := ih (fun i => read i.succ) (fun i => reference i.succ) next
          (fun i s => same i.succ s)
        dsimp only at tail
        rw [← tail]
        cases rear : consumeBitArrayWithEnd count (fun i => read i.succ) next with
        | mk rest final => cases rest <;> rfl

private theorem consumeBitArrayWithEnd_progress {A : Type*} {budget : ℕ} (count : ℕ)
    (read : Fin count → BitCursor budget → Option A × BitCursor budget) (cursor : BitCursor budget)
    (advances : ∀ i c, c.position ≤ (read i c).2.position) :
    cursor.position ≤ (consumeBitArrayWithEnd count read cursor).2.position := by
  induction count generalizing cursor with
  | zero => simp [consumeBitArrayWithEnd]
  | succ count ih =>
    rw [consumeBitArrayWithEnd]
    have start := advances 0 cursor
    cases front : read 0 cursor with
    | mk head next =>
      simp only [front] at start
      cases head with
      | none => exact start
      | some value => exact start.trans (ih (fun i => read i.succ) next (fun i c => advances i.succ c))

private def consumeCursorArrayLoopWithWork {A : Type*} {budget : ℕ}
    (read : BitCursor budget → (Option A × BitCursor budget) × ℕ) :
    ℕ → Array A → BitCursor budget → ℕ → (Option (Array A) × BitCursor budget) × ℕ
  | 0, values, cursor, work => ((some values,cursor),work+2)
  | remaining+1, values, cursor, work =>
    let head := read cursor
    match head.1.1 with
    | none => ((none,head.1.2),work+head.2+3)
    | some value => consumeCursorArrayLoopWithWork read remaining (values.push value)
        head.1.2 (work+head.2+6)

private theorem consumeCursorArrayLoopWithWork_spec {A : Type*} {budget : ℕ}
    (read : BitCursor budget → (Option A × BitCursor budget) × ℕ)
    (reference : BitCursor budget → Option A × BitCursor budget)
    (same : ∀ c, (read c).1 = reference c)
    (advances : ∀ c, c.position ≤ (read c).1.2.position)
    (bounded : ∀ c, (read c).2 ≤ 24*((read c).1.2.position-c.position)+22)
    (count : ℕ) (values : Array A) (cursor : BitCursor budget) (work : ℕ) :
    let out := consumeCursorArrayLoopWithWork read count values cursor work
    let ref := consumeBitArrayWithEnd count (fun _ => reference) cursor
    out.1 = (ref.1.map (fun rest => values ++ Array.ofFn rest),ref.2) ∧
      cursor.position ≤ out.1.2.position ∧
      out.2 ≤ work+24*(out.1.2.position-cursor.position)+28*count+2 := by
  induction count generalizing values cursor work with
  | zero => simp [consumeCursorArrayLoopWithWork, consumeBitArrayWithEnd]
  | succ count ih =>
    dsimp only
    rw [consumeCursorArrayLoopWithWork, consumeBitArrayWithEnd, ← same cursor]
    have progress := advances cursor
    have charge := bounded cursor
    rcases parsed : read cursor with ⟨⟨head,next⟩,headWork⟩
    simp only [parsed] at progress charge
    cases head with
    | none => exact ⟨rfl,progress,by dsimp only; omega⟩
    | some value =>
      dsimp only
      let ref := consumeBitArrayWithEnd count (fun _ => reference) next
      obtain ⟨agrees,moves,restWork⟩ := ih (values.push value) next (work+headWork+6)
      refine ⟨?_,progress.trans moves,by omega⟩
      rw [agrees]
      change (ref.1.map (fun rest => values.push value ++ Array.ofFn rest),ref.2) =
        ((ref.1.map (fun rest => (Fin.cases value rest : Fin (count+1) → A))).map
          (fun rest => values ++ Array.ofFn rest),ref.2)
      apply congrArg (·,ref.2)
      cases ref.1 with
      | none => rfl
      | some rest =>
        simp only [Option.map_some, Array.ofFn_succ', Fin.cases_zero, Fin.cases_succ,
          ← Array.append_assoc, ← Array.push_eq_append]

/-- Reserve a buffer for the requested number of words and fill it in order.
The tally charges reservation per slot and one unit per array append. -/
private def consumeCursorArrayWithWork {A : Type*} {budget : ℕ} (count : ℕ)
    (read : BitCursor budget → (Option A × BitCursor budget) × ℕ)
    (reference : BitCursor budget → Option A × BitCursor budget)
    (same : ∀ c, (read c).1 = reference c) (advances : ∀ c, c.position ≤ (read c).1.2.position)
    (bounded : ∀ c, (read c).2 ≤ 24*((read c).1.2.position-c.position)+22)
    (cursor : BitCursor budget) : (Option (Fin count → A) × BitCursor budget) × ℕ :=
  let readAll := consumeCursorArrayLoopWithWork read count (Array.emptyWithCapacity count) cursor (count+5)
  let ref := consumeBitArrayWithEnd count (fun _ => reference) cursor
  let expose (values : Array A) (found : readAll.1.1 = some values) : Fin count → A :=
    have size : values.size = count := by
      have spec := (consumeCursorArrayLoopWithWork_spec read reference same advances bounded count
        (Array.emptyWithCapacity count) cursor (count+5)).1
      change readAll.1 = _ at spec
      have accepted := congrArg Prod.fst spec
      change readAll.1.1 = (ref.1.map fun rest => Array.emptyWithCapacity count ++ Array.ofFn rest) at accepted
      rw [found] at accepted
      cases result : ref.1 with
      | none => simp [result] at accepted
      | some rest =>
        have array : values = Array.ofFn rest := by simpa [result] using accepted
        simp [array]
    fun i => values[i.val]'(size.symm ▸ i.isLt)
  ((readAll.1.1.pmap expose (fun _ found => found),readAll.1.2),readAll.2+3)

private theorem consumeCursorArrayWithWork_spec {A : Type*} {budget : ℕ} (count : ℕ)
    (read : BitCursor budget → (Option A × BitCursor budget) × ℕ)
    (reference : BitCursor budget → Option A × BitCursor budget)
    (same : ∀ c, (read c).1 = reference c) (advances : ∀ c, c.position ≤ (read c).1.2.position)
    (bounded : ∀ c, (read c).2 ≤ 24*((read c).1.2.position-c.position)+22)
    (cursor : BitCursor budget) :
    let out := consumeCursorArrayWithWork count read reference same advances bounded cursor
    out.1 = consumeBitArrayWithEnd count (fun _ => reference) cursor ∧
      cursor.position ≤ out.1.2.position ∧
      out.2 ≤ 24*(out.1.2.position-cursor.position)+29*count+10 := by
  let readAll := consumeCursorArrayLoopWithWork read count (Array.emptyWithCapacity count) cursor (count+5)
  let ref := consumeBitArrayWithEnd count (fun _ => reference) cursor
  obtain ⟨agrees,progress,work⟩ := consumeCursorArrayLoopWithWork_spec read reference same advances bounded count
    (Array.emptyWithCapacity count) cursor (count+5)
  change readAll.1 = (_,ref.2) at agrees
  dsimp only [consumeCursorArrayWithWork]
  refine ⟨?_,progress,by omega⟩
  have last : readAll.1.2 = ref.2 := congrArg Prod.snd agrees
  have entries := congrArg Prod.fst agrees
  change readAll.1.1 = (ref.1.map fun rest => Array.emptyWithCapacity count ++ Array.ofFn rest) at entries
  simp only [Array.emptyWithCapacity_eq, Array.empty_append] at entries
  refine Prod.ext ?_ last
  cases found : ref.1 with
  | none =>
    simp only [found, Option.map_none] at entries
    rw [Option.pmap_none' entries]
  | some rest =>
    simp only [found, Option.map_some] at entries
    rw [Option.pmap_some' entries]
    change some _ = some rest
    apply congrArg some
    funext i
    exact Array.getElem_ofFn _

/-- Track the final position even if a finite seed stops early. The state is
the position after the last complete word, including rejected proposals. -/
def decodeCompleteSteinerSeedCursorWithEndAtWidth (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    Option ((EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G) ×
      ((Fin (completeSteinerHubCount V) → ℕ) × (G → ℕ))) × BitCursor budget :=
  let count := earlySeedCoordinateCountByWidth V height width
  let count_eq := earlySeedCoordinateCountByWidth_eq G height width width_eq
  let early := consumeBitArrayWithEnd count (fun _ => consumeCursorWordWithEnd bits width) cursor
  match early.1 with
  | none => (none,early.2)
  | some earlyWords =>
    let hubs := consumeBitArrayWithEnd (completeSteinerHubCount V)
      (fun _ => consumeCursorIndexWithEnd bits (Fintype.card V)) early.2
    match hubs.1 with
    | none => (none,hubs.2)
    | some hubWords =>
      let thin := consumeBitArrayWithEnd G.card (fun _ => consumeCursorIndexWithEnd bits G.card) hubs.2
      (thin.1.map (assembleSeedAtWidth G height width count width_eq count_eq coordinates vertices arcs
        earlyWords hubWords),thin.2)

/-- Projecting the tracked outcome gives the exact established cursor
decoder, and its final position lies within the supplied interval. -/
theorem decodeCompleteSteinerSeedCursorWithEndAtWidth_spec (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    let out := decodeCompleteSteinerSeedCursorWithEndAtWidth G height width width_eq coordinates vertices arcs bits cursor
    out.1.map (fun (seed,counts) => (seed,counts,out.2)) =
      decodeCompleteSteinerSeedCursorAtWidth G height width width_eq coordinates vertices arcs bits cursor ∧
      cursor.position ≤ out.2.position ∧ out.2.position ≤ budget := by
  let count := earlySeedCoordinateCountByWidth V height width
  let early := consumeBitArrayWithEnd count (fun _ => consumeCursorWordWithEnd bits width) cursor
  have earlyRead := consumeBitArrayWithEnd_agrees count (fun _ => consumeCursorWordWithEnd bits width)
    (fun _ => consumeCursorWord bits width) cursor (fun _ c => (consumeCursorWordWithEnd_spec bits width c).1)
  have earlyMove := consumeBitArrayWithEnd_progress count (fun _ => consumeCursorWordWithEnd bits width) cursor
    (fun _ c => by
      have progress := (consumeCursorWordWithEnd_spec bits width c).2
      exact (Nat.le_add_right _ _).trans_eq progress.symm)
  change early.1.map _ = _ at earlyRead
  change cursor.position ≤ early.2.position at earlyMove
  have advance (N : ℕ) (c : BitCursor budget) :
      c.position ≤ (consumeCursorIndexWithEnd bits N c).2.position := by
    obtain ⟨k,h⟩ := (consumeCursorIndexWithEnd_spec bits N c).2.1
    rw [h]
    exact Nat.le_add_right _ _
  unfold decodeCompleteSteinerSeedCursorWithEndAtWidth decodeCompleteSteinerSeedCursorAtWidth decodeSeedAtWidthAndCount
  dsimp only
  rw [← earlyRead]
  cases ranEarly : early.1 with
  | none => exact ⟨rfl,earlyMove,early.2.bounded⟩
  | some earlyWords =>
    simp only [Option.map_some, Option.bind_some]
    let hubs := consumeBitArrayWithEnd (completeSteinerHubCount V)
      (fun _ => consumeCursorIndexWithEnd bits (Fintype.card V)) early.2
    have hubRead := consumeBitArrayWithEnd_agrees (completeSteinerHubCount V)
      (fun _ => consumeCursorIndexWithEnd bits (Fintype.card V))
      (fun _ => consumeCursorIndex bits (Fintype.card V)) early.2
      (fun _ c => (consumeCursorIndexWithEnd_spec bits (Fintype.card V) c).1)
    have hubMove := consumeBitArrayWithEnd_progress (completeSteinerHubCount V)
      (fun _ => consumeCursorIndexWithEnd bits (Fintype.card V)) early.2
      (fun _ => advance (Fintype.card V))
    change hubs.1.map _ = _ at hubRead
    change early.2.position ≤ hubs.2.position at hubMove
    rw [← hubRead]
    cases ranHubs : hubs.1 with
    | none => exact ⟨rfl,earlyMove.trans hubMove,hubs.2.bounded⟩
    | some hubWords =>
      simp only [Option.map_some, Option.bind_some]
      let thin := consumeBitArrayWithEnd G.card (fun _ => consumeCursorIndexWithEnd bits G.card) hubs.2
      have thinRead := consumeBitArrayWithEnd_agrees G.card (fun _ => consumeCursorIndexWithEnd bits G.card)
        (fun _ => consumeCursorIndex bits G.card) hubs.2
        (fun _ c => (consumeCursorIndexWithEnd_spec bits G.card c).1)
      have thinMove := consumeBitArrayWithEnd_progress G.card (fun _ => consumeCursorIndexWithEnd bits G.card)
        hubs.2 (fun _ => advance G.card)
      change thin.1.map _ = _ at thinRead
      change hubs.2.position ≤ thin.2.position at thinMove
      rw [← thinRead]
      refine ⟨?_,earlyMove.trans (hubMove.trans thinMove),thin.2.bounded⟩
      cases thin.1 <;> rfl

private theorem consumeCursorWordWithWork_advances {budget : ℕ} (bits : Fin budget → Bool)
    (width : ℕ) (cursor : BitCursor budget) :
    cursor.position ≤ (consumeCursorWordWithWork bits width cursor).1.2.position := by
  rw [(consumeCursorWordWithWork_spec bits width cursor).2.1]
  exact Nat.le_add_right _ _

private def consumeCursorWordsWithWork {budget : ℕ} (bits : Fin budget → Bool) (count width : ℕ)
    (cursor : BitCursor budget) :=
  consumeCursorArrayWithWork count (consumeCursorWordWithWork bits width) (consumeCursorWordWithEnd bits width)
    (fun c => (consumeCursorWordWithWork_spec bits width c).1) (consumeCursorWordWithWork_advances bits width)
    (fun c => (consumeCursorWordWithWork_spec bits width c).2.2.trans (by omega)) cursor

private theorem consumeCursorWordsWithWork_spec {budget : ℕ} (bits : Fin budget → Bool) (count width : ℕ)
    (cursor : BitCursor budget) :
    let out := consumeCursorWordsWithWork bits count width cursor
    out.1 = consumeBitArrayWithEnd count (fun _ => consumeCursorWordWithEnd bits width) cursor ∧
      cursor.position ≤ out.1.2.position ∧
      out.2 ≤ 24*(out.1.2.position-cursor.position)+29*count+10 :=
  consumeCursorArrayWithWork_spec count _ _ _ _ _ cursor

private def consumeCursorIndicesWithWork {budget : ℕ} (bits : Fin budget → Bool) (count N width : ℕ)
    (width_eq : width = uniformProposalWidth N) (cursor : BitCursor budget) :=
  consumeCursorArrayWithWork count (consumeCursorIndexAtWidthWithWork bits N width) (consumeCursorIndexWithEnd bits N)
    (fun c => (consumeCursorIndexAtWidthWithWork_spec bits N width c width_eq).1)
    (fun c => (consumeCursorIndexAtWidthWithWork_spec bits N width c width_eq).2.1)
    (fun c => (consumeCursorIndexAtWidthWithWork_spec bits N width c width_eq).2.2) cursor

private theorem consumeCursorIndicesWithWork_spec {budget : ℕ} (bits : Fin budget → Bool) (count N width : ℕ)
    (width_eq : width = uniformProposalWidth N) (cursor : BitCursor budget) :
    let out := consumeCursorIndicesWithWork bits count N width width_eq cursor
    out.1 = consumeBitArrayWithEnd count (fun _ => consumeCursorIndexWithEnd bits N) cursor ∧
      cursor.position ≤ out.1.2.position ∧
      out.2 ≤ 24*(out.1.2.position-cursor.position)+29*count+10 :=
  consumeCursorArrayWithWork_spec count _ _ _ _ _ cursor

/-- Cardinalities and proposal widths available before the three seed reads. -/
structure SteinerSeedDecoderSizes (G : Arcs V) (height width : ℕ) where
  vertexCount : ℕ
  arcCount : ℕ
  earlyCount : ℕ
  hubCount : ℕ
  vertexWidth : ℕ
  arcWidth : ℕ
  vertexCount_eq : vertexCount = Fintype.card V
  arcCount_eq : arcCount = G.card
  earlyCount_eq : earlyCount = earlySeedCoordinateCountByWidth V height width
  hubCount_eq : hubCount = completeSteinerHubCount V
  vertexWidth_eq : vertexWidth = uniformProposalWidth vertexCount
  arcWidth_eq : arcWidth = uniformProposalWidth arcCount

private abbrev CompleteSteinerSeedAndRejects (G : Arcs V) (height : ℕ) :=
  (EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G) ×
    ((Fin (completeSteinerHubCount V) → ℕ) × (G → ℕ))

private abbrev SteinerSeedAssembler (G : Arcs V) (height width : ℕ) (Result : Type*) :=
  (count : ℕ) → count = Fintype.card (EarlySeedCoordinate G height) →
    (Fin count → Fin (2^width)) → (Fin (completeSteinerHubCount V) → Fin (Fintype.card V) × ℕ) →
    (Fin G.card → Fin G.card × ℕ) → Result

@[inline] private def readSteinerSeedCursorWithWork {Result : Type*} (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (sizes : SteinerSeedDecoderSizes G height width)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget)
    (assemble : SteinerSeedAssembler G height width Result) : (Option Result × BitCursor budget) × ℕ :=
  let early := consumeCursorWordsWithWork bits sizes.earlyCount width cursor
  match early.1.1 with
  | none => ((none,early.1.2),early.2+5)
  | some earlyWords =>
    let hubs := consumeCursorIndicesWithWork bits sizes.hubCount sizes.vertexCount
      sizes.vertexWidth sizes.vertexWidth_eq early.1.2
    match hubs.1.1 with
    | none => ((none,hubs.1.2),early.2+hubs.2+9)
    | some hubWords =>
      let thin := consumeCursorIndicesWithWork bits sizes.arcCount sizes.arcCount
        sizes.arcWidth sizes.arcWidth_eq hubs.1.2
      let count_eq := sizes.earlyCount_eq.trans (earlySeedCoordinateCountByWidth_eq G height width width_eq)
      let hubSeed := fun i =>
        let entry := hubWords (Fin.cast sizes.hubCount_eq.symm i)
        (Fin.cast sizes.vertexCount_eq entry.1,entry.2)
      let thinSeed := fun words i =>
        let entry : Fin sizes.arcCount × ℕ := words (Fin.cast sizes.arcCount_eq.symm i)
        (Fin.cast sizes.arcCount_eq entry.1,entry.2)
      let seed := thin.1.1.map (fun words => assemble sizes.earlyCount count_eq earlyWords hubSeed (thinSeed words))
      ((seed,thin.1.2),early.2+hubs.2+thin.2+25)

private theorem readSteinerSeedCursorWithWork_project {Result Prior : Type*} (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (sizes : SteinerSeedDecoderSizes G height width)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget)
    (assemble : SteinerSeedAssembler G height width Result) (old : SteinerSeedAssembler G height width Prior)
    (project : Result → Prior) (invariant : Result → Prop)
    (agrees : ∀ count same early hubs thin, project (assemble count same early hubs thin) = old count same early hubs thin ∧
      invariant (assemble count same early hubs thin)) :
    let out := readSteinerSeedCursorWithWork G height width width_eq sizes bits cursor assemble
    ((out.1.1.map project,out.1.2),out.2) = readSteinerSeedCursorWithWork G height width width_eq sizes bits cursor old ∧
      ∀ value, out.1.1 = some value → invariant value := by
  dsimp only [readSteinerSeedCursorWithWork]
  generalize consumeCursorWordsWithWork bits sizes.earlyCount width cursor = early
  cases early.1.1 with
  | none => simp
  | some earlyWords =>
    dsimp only
    generalize consumeCursorIndicesWithWork bits sizes.hubCount sizes.vertexCount
      sizes.vertexWidth sizes.vertexWidth_eq early.1.2 = hubs
    cases hubs.1.1 with
    | none => simp
    | some hubWords =>
      dsimp only
      generalize consumeCursorIndicesWithWork bits sizes.arcCount sizes.arcCount
        sizes.arcWidth sizes.arcWidth_eq hubs.1.2 = thin
      cases thin.1.1 with
      | none => simp
      | some words =>
        simp only [Option.map_some, Option.some.injEq]
        obtain ⟨same,holds⟩ := agrees sizes.earlyCount _ earlyWords _ _
        exact ⟨by rw [same], fun value eq => eq ▸ holds⟩

/-- Decode a bounded bit input into the three seed arrays. The tally covers
the cursor reads, rejection loops, buffer reservation and filling, and stage
control. The prepared parameters and application of the returned seed and
its index maps have separate costs. -/
def decodeCompleteSteinerSeedCursorWithWork (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (sizes : SteinerSeedDecoderSizes G height width)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    (Option (CompleteSteinerSeedAndRejects G height) × BitCursor budget) × ℕ :=
  readSteinerSeedCursorWithWork G height width width_eq sizes bits cursor
    (fun count count_eq => assembleSeedAtWidth G height width count width_eq count_eq coordinates vertices arcs)

/-- Read the same seed and retain a direct view of its stored arc thresholds. -/
def decodeSteinerSeedCursorWithIndexedThin (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (sizes : SteinerSeedDecoderSizes G height width)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    (Option (CompleteSteinerSeedAndRejects G height × (Fin G.card → Fin G.card)) × BitCursor budget) × ℕ :=
  readSteinerSeedCursorWithWork G height width width_eq sizes bits cursor
    (fun count count_eq early hubs thin =>
      (assembleSeedAtWidth G height width count width_eq count_eq coordinates vertices arcs early hubs thin,
        fun i => (thin i).1))

theorem decodeSteinerSeedCursorWithIndexedThin_spec (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (sizes : SteinerSeedDecoderSizes G height width)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    let out := decodeSteinerSeedCursorWithIndexedThin G height width width_eq sizes coordinates vertices arcs bits cursor
    ((out.1.1.map Prod.fst,out.1.2),out.2) =
      decodeCompleteSteinerSeedCursorWithWork G height width width_eq sizes coordinates vertices arcs bits cursor ∧
      ∀ packet, out.1.1 = some packet → ∀ e, packet.2 (arcs e) = packet.1.1.2.2 e := by
  exact readSteinerSeedCursorWithWork_project G height width width_eq sizes bits cursor _ _
    Prod.fst (fun packet : CompleteSteinerSeedAndRejects G height × (Fin G.card → Fin G.card) =>
      ∀ e, packet.2 (arcs e) = packet.1.1.2.2 e)
    (fun _ _ _ _ _ => ⟨rfl, fun _ => rfl⟩)

/-- Direct indexed views of the early and thin arrays filled by the decoder. -/
structure SteinerSeedArrayViews (G : Arcs V) (height : ℕ) where
  early : IndexedEarlySeedWords G height
  thin : Fin G.card → Fin G.card

/-- Retain both indexed readers from the same successful bit decode. -/
def decodeSteinerSeedCursorWithArrayViews (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (sizes : SteinerSeedDecoderSizes G height width)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    (Option (CompleteSteinerSeedAndRejects G height × SteinerSeedArrayViews G height) × BitCursor budget) × ℕ :=
  readSteinerSeedCursorWithWork G height width width_eq sizes bits cursor
    (fun count count_eq early hubs thin =>
      (assembleSeedAtWidth G height width count width_eq count_eq coordinates vertices arcs early hubs thin,
        ⟨earlySeedWordsAtWidth G height width count width_eq count_eq early, fun i => (thin i).1⟩))

theorem decodeSteinerSeedCursorWithArrayViews_spec (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (sizes : SteinerSeedDecoderSizes G height width)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    let out := decodeSteinerSeedCursorWithArrayViews G height width width_eq sizes coordinates vertices arcs bits cursor
    ((out.1.1.map (fun p => (p.1,p.2.thin)),out.1.2),out.2) =
      decodeSteinerSeedCursorWithIndexedThin G height width width_eq sizes coordinates vertices arcs bits cursor ∧
    ∀ packet, out.1.1 = some packet →
      (earlySeedCoordinates G height).symm (fun c => packet.2.early (coordinates c)) = packet.1.1.1 := by
  exact readSteinerSeedCursorWithWork_project G height width width_eq sizes bits cursor _ _
    (fun p : CompleteSteinerSeedAndRejects G height × SteinerSeedArrayViews G height => (p.1,p.2.thin))
    (fun p => (earlySeedCoordinates G height).symm (fun c => p.2.early (coordinates c)) = p.1.1.1)
    (fun _ _ _ _ _ => ⟨rfl,rfl⟩)

/-- The metered decoder agrees on the seed, rejection counts and end cursor,
even when the bits end during a rejection stage. Its work is linear in the
actual cursor advance and the total requested buffer sizes. -/
theorem decodeCompleteSteinerSeedCursorWithWork_spec (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (sizes : SteinerSeedDecoderSizes G height width)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    let out := decodeCompleteSteinerSeedCursorWithWork G height width width_eq sizes coordinates vertices arcs bits cursor
    out.1 = decodeCompleteSteinerSeedCursorWithEndAtWidth G height width width_eq coordinates vertices arcs bits cursor ∧
      cursor.position ≤ out.1.2.position ∧
      out.2 ≤ 24*(out.1.2.position-cursor.position)+29*(sizes.earlyCount+sizes.hubCount+sizes.arcCount)+55 := by
  rcases sizes with ⟨n,m,e,h,vw,aw,hn,hm,he,hh,hvw,haw⟩
  subst n m e h vw aw
  dsimp only [decodeCompleteSteinerSeedCursorWithWork, readSteinerSeedCursorWithWork,
    decodeCompleteSteinerSeedCursorWithEndAtWidth]
  have earlySpec := consumeCursorWordsWithWork_spec bits (earlySeedCoordinateCountByWidth V height width) width cursor
  dsimp only at earlySpec
  generalize consumeCursorWordsWithWork bits (earlySeedCoordinateCountByWidth V height width) width cursor = early
    at earlySpec ⊢
  obtain ⟨earlySame,earlyMove,earlyWork⟩ := earlySpec
  rw [← earlySame]
  cases early.1.1 with
  | none =>
    dsimp only
    exact ⟨rfl,earlyMove,by omega⟩
  | some earlyWords =>
    dsimp only
    have hubSpec := consumeCursorIndicesWithWork_spec bits (completeSteinerHubCount V) (Fintype.card V)
      (uniformProposalWidth (Fintype.card V)) rfl early.1.2
    dsimp only at hubSpec
    generalize consumeCursorIndicesWithWork bits (completeSteinerHubCount V) (Fintype.card V)
      (uniformProposalWidth (Fintype.card V)) rfl early.1.2 = hubs at hubSpec ⊢
    obtain ⟨hubSame,hubMove,hubWork⟩ := hubSpec
    rw [← hubSame]
    cases hubs.1.1 with
    | none =>
      dsimp only
      exact ⟨rfl,earlyMove.trans hubMove,by omega⟩
    | some hubWords =>
      dsimp only
      have thinSpec := consumeCursorIndicesWithWork_spec bits G.card G.card
        (uniformProposalWidth G.card) rfl hubs.1.2
      dsimp only at thinSpec
      generalize consumeCursorIndicesWithWork bits G.card G.card (uniformProposalWidth G.card) rfl hubs.1.2 = thin
        at thinSpec ⊢
      obtain ⟨thinSame,thinMove,thinWork⟩ := thinSpec
      rw [← thinSame]
      refine ⟨?_,earlyMove.trans (hubMove.trans thinMove),by omega⟩
      simp only [Fin.cast_refl, id_eq]

end OnlineReachabilityPreservers
