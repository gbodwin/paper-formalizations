import OnlineReachabilityPreservers.DeterministicEnumerationWork
import OnlineReachabilityPreservers.SteinerBitOrders

/-! Enumerate the existing arc order directly for an indexed directed graph. -/

namespace OnlineReachabilityPreservers

private def finArcLexRank (n : ℕ) : (Fin n ×ₗ Fin n) ≃ Fin (n*n) := ofLex.trans finProdFinEquiv

private theorem finArcLexRank_strictMono (n : ℕ) : StrictMono (finArcLexRank n) := by
  intro e f order
  have lex := Prod.Lex.lt_iff.mp order
  change (ofLex e).2.val + n*(ofLex e).1.val < (ofLex f).2.val + n*(ofLex f).1.val
  rcases lex with before | ⟨same, before⟩
  · have next : (ofLex e).1.val+1 ≤ (ofLex f).1.val := before
    have begins := Nat.mul_le_mul_left n next
    rw [Nat.mul_add, Nat.mul_one] at begins
    have endOfBlock := (ofLex e).2.isLt
    omega
  · have lt : (ofLex e).2.val < (ofLex f).2.val := before
    rw [same]
    omega

private theorem finArcLexUnrank_strictMono (n : ℕ) : StrictMono (finArcLexRank n).symm := by
  intro i j before
  apply (finArcLexRank_strictMono n).lt_iff_lt.mp
  simpa only [Equiv.apply_symm_apply] using before

private def selectFinArcKeysWithWordWork {n : ℕ} (raw : List (Fin n × Fin n)) :
    List (Fin (n*n)) → List (Fin n ×ₗ Fin n) × ℕ
  | [] => ([],4)
  | i :: slots =>
    let edge := finProdFinEquiv.symm i
    let read := memScanWithWordWork edge raw
    let tail := selectFinArcKeysWithWordWork raw slots
    (if read.1 then toLex edge :: tail.1 else tail.1,tail.2+read.2+21)

private theorem selectFinArcKeysWithWordWork_spec {n : ℕ} (raw : List (Fin n × Fin n))
    (slots : List (Fin (n*n))) :
    let out := selectFinArcKeysWithWordWork raw slots
    out.1 = (slots.filter fun i => (memScanWithWordWork (finProdFinEquiv.symm i) raw).1).map (finArcLexRank n).symm ∧
      out.2 ≤ slots.length*(2*raw.length+22)+4 := by
  induction slots with
  | nil => simp [selectFinArcKeysWithWordWork]
  | cons i slots ih =>
    obtain ⟨same,tail⟩ := ih
    have work := (memScanWithWordWork_spec (finProdFinEquiv.symm i) raw).2
    constructor
    · simp only [selectFinArcKeysWithWordWork, same]
      let keep (j : Fin (n*n)) := (memScanWithWordWork (finProdFinEquiv.symm j) raw).1
      split
      · rename_i available
        rw [List.filter_cons_of_pos (p := keep) (a := i) (l := slots) available]
        rfl
      · rename_i absent
        rw [List.filter_cons_of_neg (p := keep) (a := i) (l := slots) absent]
    · change (selectFinArcKeysWithWordWork raw slots).2+(memScanWithWordWork (finProdFinEquiv.symm i) raw).2+21 ≤ _
      rw [List.length_cons, Nat.succ_mul slots.length (2*raw.length+22)]
      omega

/-- Filter the arithmetic lexicographic enumeration with membership in the
input arc list. This accepts both unsorted list inputs and repeated arcs. -/
def finArcKeysWithWordWork {n : ℕ} (raw : List (Fin n × Fin n)) : List (Fin n ×ₗ Fin n) × ℕ :=
  let slots := finVerticesWithWordWork (n*n)
  let out := selectFinArcKeysWithWordWork raw slots.1
  (out.1,slots.2+out.2+4)

/-- The resulting keys have the ordinary canonical arc order, with a
polynomial charge for the enumerated lists, pairs and membership scans. -/
theorem finArcKeysWithWordWork_spec {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) :
    let out := finArcKeysWithWordWork raw
    let keys := G.map (toLex : (Fin n × Fin n) ≃ Fin n ×ₗ Fin n).toEmbedding
    out.1 = keys.sort ∧ out.2 ≤ (n*n)*(2*raw.length+30)+9 := by
  let out := finArcKeysWithWordWork raw
  let slots := finVerticesWithWordWork (n*n)
  let keys := G.map (toLex : (Fin n × Fin n) ≃ Fin n ×ₗ Fin n).toEmbedding
  let build := selectFinArcKeysWithWordWork raw slots.1
  let keep (i : Fin (n*n)) := (memScanWithWordWork (finProdFinEquiv.symm i) raw).1
  let unrank := (finArcLexRank n).symm
  obtain ⟨sorted,selection⟩ := selectFinArcKeysWithWordWork_spec raw slots.1
  have built : out.1 = (slots.1.filter keep).map unrank := sorted
  obtain ⟨unique,all,work⟩ := finVerticesWithWordWork_spec (n*n)
  have enumeration : slots.1 = (Finset.univ : Finset (Fin (n*n))).sort := finVerticesWithWordWork_eq_sort (n*n)
  have length : slots.1.length = n*n := by
    rw [enumeration]
    simp
  have inOrder : slots.1.Pairwise (· ≤ ·) := enumeration ▸ Finset.pairwise_sort _ _
  have ordered : out.1.Pairwise (· ≤ ·) := by
    rw [built,List.pairwise_map]
    exact ((inOrder.filter keep).imp fun h => (finArcLexUnrank_strictMono n).monotone h)
  have distinct : out.1.Nodup := by
    rw [built]
    exact (unique.filter keep).map unrank.injective
  have member (e) : e ∈ out.1 ↔ e ∈ keys := by
    rw [built, List.mem_map,Finset.mem_map]
    constructor
    · rintro ⟨i, ok, rfl⟩
      have passed : keep i = true := (List.mem_filter.mp ok).2
      have seen : finProdFinEquiv.symm i ∈ raw := by
        simpa only [keep,(memScanWithWordWork_spec (finProdFinEquiv.symm i) raw).1,decide_eq_true_eq] using passed
      exact ⟨finProdFinEquiv.symm i,same ▸ List.mem_toFinset.mpr seen,rfl⟩
    · rintro ⟨edge, present, rfl⟩
      have seen := List.mem_toFinset.mp (same.symm ▸ present)
      let i := finProdFinEquiv edge
      refine ⟨i,List.mem_filter.mpr ⟨all i,?_⟩,?_⟩
      · dsimp only [keep,i]
        rw [Equiv.symm_apply_apply]
        simpa only [(memScanWithWordWork_spec edge raw).1,decide_eq_true_eq] using seen
      · change toLex (finProdFinEquiv.symm i) = toLex edge
        rw [show finProdFinEquiv.symm i = edge from finProdFinEquiv.symm_apply_apply edge]
  refine ⟨List.Perm.eq_of_pairwise' ordered (keys.pairwise_sort _)
    ((List.perm_ext_iff_of_nodup distinct (keys.sort_nodup _)).mpr fun e => (member e).trans (keys.mem_sort _).symm),?_⟩
  change slots.2 = _ at work
  change build.2 ≤ _ at selection
  change slots.2+build.2+4 ≤ _
  rw [length] at selection
  rw [work]
  calc
    _ ≤ 8*(n*n)+1+((n*n)*(2*raw.length+22)+4)+4 := by omega
    _ = _ := by ring

/-- Prepare one duplicate-free list of ordinary arc keys for interval scans. -/
def finArcRowsWithWordWork {n : ℕ} (raw : List (Fin n × Fin n)) :
    {r : List (Fin n × Fin n) // r.Nodup} × ℕ :=
  let ordered := finArcKeysWithWordWork raw
  let arcs := raw.toFinset
  let keys := arcs.map (toLex : (Fin n × Fin n) ≃ Fin n ×ₗ Fin n).toEmbedding
  have distinct : (ordered.1.map ofLex).Nodup := by
    rw [(finArcKeysWithWordWork_spec arcs raw rfl).1]
    exact (keys.sort_nodup _).map ((toLex : (Fin n × Fin n) ≃ Fin n ×ₗ Fin n).symm.injective)
  (⟨ordered.1.map ofLex,distinct⟩,ordered.2+7*ordered.1.length+4)

def finArcRowsWordBudget (n inputSize : ℕ) : ℕ := (n*n)*(2*inputSize+30)+7*inputSize+13

theorem finArcRowsWithWordWork_spec {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) :
    let out := finArcRowsWithWordWork raw
    out.1.val.toFinset = G ∧ out.2 ≤ finArcRowsWordBudget n raw.length := by
  let ordered := finArcKeysWithWordWork raw
  let keys := G.map (toLex : (Fin n × Fin n) ≃ Fin n ×ₗ Fin n).toEmbedding
  obtain ⟨sorted,spent⟩ := finArcKeysWithWordWork_spec G raw same
  change ordered.1 = keys.sort at sorted
  refine ⟨?_,?_⟩
  · change (ordered.1.map ofLex).toFinset = G
    rw [sorted]
    ext edge
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,keys,Finset.mem_map,Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨_,⟨arc,inside,rfl⟩,rfl⟩
      exact inside
    · intro inside
      exact ⟨toLex edge,⟨edge,inside,rfl⟩,rfl⟩
  · have count : ordered.1.length = G.card := by
      rw [sorted,Finset.length_sort,Finset.card_map]
    have under : G.card ≤ raw.length := same ▸ List.toFinset_card_le raw
    change ordered.2 ≤ (n*n)*(2*raw.length+30)+9 at spent
    change ordered.2+7*ordered.1.length+4 ≤ finArcRowsWordBudget n raw.length
    unfold finArcRowsWordBudget
    omega

end OnlineReachabilityPreservers
