import OnlineReachabilityPreservers.SteinerArrayRankWork
import OnlineReachabilityPreservers.SteinerFinArcRowsWork
import OnlineReachabilityPreservers.SteinerSeedDecoderWork

/-! Prepare the original graph key indexes for Fin-labelled input. -/

namespace OnlineReachabilityPreservers

/-- The canonical vertex index on Fin n needs only the existing index value. -/
def finSteinerVertexIndex (n : ℕ) : Fin n ≃ Fin (Fintype.card (Fin n)) := castFinIndex (by simp)

theorem finSteinerVertexIndex_eq (n : ℕ) : finSteinerVertexIndex n = steinerUniverseArrayIndex (Fin n) := by
  rw [steinerUniverseArrayIndex_eq]
  let cast := finSteinerVertexIndex n
  let original := steinerVertexIndex (Fin n)
  let perm := original.trans cast.symm
  have originalOrder : StrictMono original := (Fintype.orderIsoFinOfCardEq (Fin n) rfl).symm.strictMono
  have castOrder : StrictMono cast.symm := Fin.cast_strictMono (by simp)
  have order : StrictMono perm := castOrder.comp originalOrder
  have inverse : StrictMono perm.symm := by
    intro a b lt
    apply order.lt_iff_lt.mp
    simpa only [Equiv.apply_symm_apply] using lt
  apply Equiv.ext
  intro x
  have lower : x ≤ perm x := order.id_le x
  have upper : perm x ≤ x := by simpa only [id_eq, Equiv.symm_apply_apply] using inverse.id_le (perm x)
  have equal := le_antisymm upper lower
  exact cast.symm.injective ((cast.symm_apply_apply x).trans equal.symm)

private def fillArrayWithWordWork {A : Type*} (buffer : Array A) : List A → Array A × ℕ
  | [] => (buffer,3)
  | a :: tail =>
    let out := fillArrayWithWordWork (buffer.push a) tail
    (out.1,out.2+9)

private theorem fillArrayWithWordWork_spec {A : Type*} (buffer : Array A) (keys : List A) :
    let out := fillArrayWithWordWork buffer keys
    out.1.toList = buffer.toList ++ keys ∧ out.2 = 9*keys.length+3 := by
  induction keys generalizing buffer with
  | nil => simp [fillArrayWithWordWork]
  | cons a tail ih =>
    obtain ⟨shape,cost⟩ := ih (buffer.push a)
    constructor
    · simpa only [fillArrayWithWordWork,Array.toList_push,List.append_assoc,List.singleton_append] using shape
    · change (fillArrayWithWordWork (buffer.push a) tail).2+9 = _
      rw [cost,List.length_cons,Nat.mul_succ 9 tail.length]

private def listToArrayWithWordWork {A : Type*} (keys : List A) : Array A × ℕ :=
  let length := keys.length
  let filled := fillArrayWithWordWork (Array.mkEmpty length) keys
  (filled.1,filled.2+5*length+7)

private theorem listToArrayWithWordWork_spec {A : Type*} (keys : List A) :
    let out := listToArrayWithWordWork keys
    out.1 = keys.toArray ∧ out.2 = 14*keys.length+10 := by
  obtain ⟨exactList,tally⟩ := fillArrayWithWordWork_spec (Array.mkEmpty keys.length) keys
  constructor
  · apply Array.toList_inj.mp
    change (fillArrayWithWordWork (Array.mkEmpty keys.length) keys).1.toList = keys.toArray.toList
    rw [exactList]
    simp
  · dsimp only [listToArrayWithWordWork]
    rw [tally]
    omega

private def sortedIndexFromPreparedArray {A : Type*} [LinearOrder A] (keys : Finset A)
    (array : Array A) (same : array = keys.sort.toArray) (fuel : ℕ) (fuelEq : fuel = array.size.size) :
    keys ≃ Fin keys.card :=
  let rows := keys.sort
  have len : rows.length = keys.card := keys.length_sort _
  let lookup (x : keys) := (arrayLowerBoundWithWordWork array x.val fuel 0 array.size le_rfl).1
  have rank (x : keys) : lookup x = rows.idxOf x.val :=
    (sortedArrayRankWithWordWork_spec keys array same fuel fuelEq x).1
  have slot (i : Fin keys.card) : i.val < rows.length := len.symm ▸ i.isLt
  have arraySlot (i : Fin keys.card) : i.val < array.size := by
    rw [same, List.size_toArray]
    exact slot i
  have inside (x : keys) : x.val ∈ rows := (keys.mem_sort _).mpr x.property
  { toFun := fun x => ⟨lookup x, by rw [rank]; exact len ▸ List.idxOf_lt_length_of_mem (inside x)⟩
    invFun := fun i => ⟨array[i.val]'(arraySlot i), (keys.mem_sort _).mp (by
      simp only [same, List.getElem_toArray]
      exact List.getElem_mem (l := rows) (slot i))⟩
    left_inv := by
      intro x
      apply Subtype.ext
      simp only [same,List.getElem_toArray,rank]
      exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (inside x))
    right_inv := by
      intro i
      apply Fin.ext
      simp only [rank,same,List.getElem_toArray]
      exact (keys.sort_nodup _).idxOf_getElem (i := i.val) (slot i) }

private theorem sortedIndexFromPreparedArray_eq {A : Type*} [LinearOrder A] (keys : Finset A)
    (array : Array A) (same : array = keys.sort.toArray) (fuel : ℕ) (fuelEq : fuel = array.size.size) :
    sortedIndexFromPreparedArray keys array same fuel fuelEq = steinerSortedArrayIndex keys := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  change (arrayLowerBoundWithWordWork array x.val fuel 0 array.size le_rfl).1 = _
  rw [(sortedArrayRankWithWordWork_spec keys array same fuel fuelEq x).1]
  exact (binarySortedIndexWithChecks_spec keys x).1.symm

private def toLexArcSubtype {n : ℕ} (G : Arcs (Fin n)) :
    G ≃ G.map (toLex : (Fin n × Fin n) ≃ Fin n ×ₗ Fin n).toEmbedding :=
  { toFun := fun e => ⟨toLex e.val,Finset.mem_map_of_mem _ e.property⟩
    invFun := fun e => ⟨ofLex e.val,by
      obtain ⟨a,found,eq⟩ := Finset.mem_map.mp e.property
      exact (congrArg ofLex eq) ▸ found⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Build one sorted arc array directly from the raw arc list for Fin
vertices. The proof inputs certify its order and the same arc set. -/
def finSteinerArcIndexWithWordWork {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) : (G ≃ Fin G.card) × ℕ :=
  let keys := G.map (toLex : (Fin n × Fin n) ≃ Fin n ×ₗ Fin n).toEmbedding
  let ordered := finArcKeysWithWordWork raw
  let array := listToArrayWithWordWork ordered.1
  let fuel := bitLengthWithWork array.1.size
  let arrayEq : array.1 = keys.sort.toArray := (listToArrayWithWordWork_spec ordered.1).1.trans
    (congrArg List.toArray (finArcKeysWithWordWork_spec G raw same).1)
  let indexed := sortedIndexFromPreparedArray keys array.1 arrayEq fuel.1 (bitLengthWithWork_spec _).1
  let result := (toLexArcSubtype G).trans (indexed.trans (castFinIndex (Finset.card_map _)))
  (result,ordered.2+array.2+fuel.2+8)

theorem finSteinerArcIndexWithWordWork_spec {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) :
    let out := finSteinerArcIndexWithWordWork G raw same
    out.1 = steinerArcArrayIndex G ∧ out.2 ≤ (n*n)*(2*raw.length+30)+21*raw.length+30 := by
  let ordered := finArcKeysWithWordWork raw
  let array := listToArrayWithWordWork ordered.1
  let keys := G.map (toLex : (Fin n × Fin n) ≃ Fin n ×ₗ Fin n).toEmbedding
  obtain ⟨canonical, enumerated⟩ := finArcKeysWithWordWork_spec G raw same
  obtain ⟨arrayExact, arrayCost⟩ := listToArrayWithWordWork_spec ordered.1
  have len : ordered.1.length = G.card := by
    rw [canonical,Finset.length_sort,Finset.card_map]
  have card : G.card ≤ raw.length := same ▸ List.toFinset_card_le raw
  have size : array.1.size = G.card := by rw [arrayExact,List.size_toArray,len]
  have fuel := bitLengthWork_le array.1.size
  refine ⟨?_,?_⟩
  · dsimp only [finSteinerArcIndexWithWordWork]
    rw [sortedIndexFromPreparedArray_eq]
    ext x
    rfl
  · change ordered.2+array.2+(bitLengthWithWork array.1.size).2+8 ≤ _
    change ordered.2 ≤ _ at enumerated
    rw [size] at fuel ⊢
    change array.2 = _ at arrayCost
    rw [len] at arrayCost
    omega

end OnlineReachabilityPreservers
