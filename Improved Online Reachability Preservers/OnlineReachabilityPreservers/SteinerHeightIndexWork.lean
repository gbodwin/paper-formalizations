import OnlineReachabilityPreservers.SteinerBitOrders

/-! Charge arithmetic and label conversions in lexicographic indexing of bounded histories. -/

namespace OnlineReachabilityPreservers

/-- Compute the size of an index block with one multiply and add per height. -/
def heightLexBlockCountWithWordWork (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1,1)
  | h+1 =>
    let rest := heightLexBlockCountWithWordWork n h
    (n*rest.1+1,rest.2+5)

theorem heightLexBlockCountWithWordWork_spec (n h : ℕ) :
    let out := heightLexBlockCountWithWordWork n h
    out.1 = heightLexBlockCount n h ∧ out.2 = 5*h+1 := by
  induction h with
  | zero => exact ⟨rfl,rfl⟩
  | succ h ih =>
    obtain ⟨same,work⟩ := ih
    exact ⟨by simp only [heightLexBlockCountWithWordWork, heightLexBlockCount, same],
      by simp only [heightLexBlockCountWithWordWork, work]; omega⟩

theorem heightLexBlockCount_positive (n h : ℕ) : 0 < heightLexBlockCount n h := by
  cases h <;> simp [heightLexBlockCount]

/-- The number of block slots is at most the corresponding power of `n + 1`. -/
theorem heightLexBlockCount_le_pow (n h : ℕ) : heightLexBlockCount n h ≤ (n+1)^h := by
  induction h with
  | zero => simp [heightLexBlockCount]
  | succ h ih =>
    rw [heightLexBlockCount, pow_succ]
    have positive := heightLexBlockCount_positive n h
    calc
      _ ≤ heightLexBlockCount n h*(n+1) := by rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm n]; omega
      _ ≤ (n+1)^h*(n+1) := Nat.mul_le_mul_right _ ih

theorem heightLexBlockCount_bits (n h : ℕ) :
    (heightLexBlockCount n h).size ≤ h*(n+1).size+1 := by
  apply Nat.size_le.mpr
  have base : n+1 ≤ 2^(n+1).size := (Nat.lt_size_self (n+1)).le
  have positive : 0 < 2^((n+1).size*h) := Nat.pow_pos (by decide)
  calc
    heightLexBlockCount n h ≤ (n+1)^h := heightLexBlockCount_le_pow n h
    _ ≤ 2^((n+1).size*h) := by rw [pow_mul]; exact Nat.pow_le_pow_left base _
    _ < 2^(h*(n+1).size+1) := by rw [Nat.mul_comm h, pow_succ]; omega

/-- Read the list from its first label. Each recursive call charges the
supplied label rank and the arithmetic needed to find its block. -/
def heightNodeRankWithWordWork {V : Type*} (n : ℕ) (label : V → ℕ × ℕ) :
    (h : ℕ) → HeightNode V h → ℕ × ℕ
  | 0, _ => (0,2)
  | _h+1, ⟨[], _⟩ => (0,3)
  | h+1, ⟨v::rest, fits⟩ =>
    let block := heightLexBlockCountWithWordWork n h
    let first := label v
    let tail := heightNodeRankWithWordWork n label h ⟨rest, Nat.le_of_succ_le_succ fits⟩
    (first.1*block.1+tail.1+1,first.2+tail.2+block.2+12)

/-- A bound for ranking or unranking one history with a given per-label cost. -/
def heightNodeIndexWordBudget (h label : ℕ) : ℕ := 6*h^2+(label+24)*h+7

theorem heightNodeRankWithWordWork_spec {V : Type*} {n : ℕ} (vertices : V ≃ Fin n)
    (label : V → ℕ × ℕ) (budget : ℕ) (equal : ∀ v, (label v).1 = (vertices v).val)
    (bounded : ∀ v, (label v).2 ≤ budget) (h : ℕ) (node : HeightNode V h) :
    let out := heightNodeRankWithWordWork n label h node
    out.1 = (heightNodeLexIndex vertices h node).val ∧ out.2 ≤ heightNodeIndexWordBudget h budget := by
  induction h with
  | zero => exact ⟨rfl, by simp [heightNodeRankWithWordWork, heightNodeIndexWordBudget]⟩
  | succ h ih =>
    rcases node with ⟨row,fits⟩
    cases row with
    | nil =>
      refine ⟨rfl, ?_⟩
      simp only [heightNodeRankWithWordWork, heightNodeIndexWordBudget]
      omega
    | cons v rest =>
      obtain ⟨tailEq,tailCost⟩ := ih ⟨rest,Nat.le_of_succ_le_succ fits⟩
      obtain ⟨blockEq,blockCost⟩ := heightLexBlockCountWithWordWork_spec n h
      refine ⟨?_, ?_⟩
      · simp only [heightNodeRankWithWordWork, heightNodeLex_cons, equal v, blockEq, tailEq]
      · have firstCost := bounded v
        simp only [heightNodeRankWithWordWork, blockCost]
        unfold heightNodeIndexWordBudget at tailCost ⊢
        nlinarith

private theorem heightIndexRemaining_lt {n h : ℕ} (rank : Fin (heightLexBlockCount n (h+1)))
    (positive : 0 < rank.val) : rank.val-1 < n * heightLexBlockCount n h := by
  have bound := rank.isLt
  change rank.val < n * heightLexBlockCount n h + 1 at bound
  omega

/-- Unrank one bounded history in the same lexicographic order. -/
def heightNodeUnrankWithWordWork {V : Type*} (n : ℕ) (label : Fin n → V × ℕ) :
    (h : ℕ) → Fin (heightLexBlockCount n h) → HeightNode V h × ℕ
  | 0, _ => (⟨[], by simp⟩,2)
  | h+1, index =>
    if zero : index.val = 0 then (⟨[], by simp⟩,4)
    else
      let block := heightLexBlockCountWithWordWork n h
      have width : block.1 = heightLexBlockCount n h := (heightLexBlockCountWithWordWork_spec n h).1
      have positive : 0 < block.1 := width.symm ▸ heightLexBlockCount_positive n h
      let remaining := index.val-1
      let first : Fin n := ⟨remaining/block.1,
        (Nat.div_lt_iff_lt_mul positive).2 (width.symm ▸ heightIndexRemaining_lt index (Nat.pos_of_ne_zero zero))⟩
      let rest : Fin (heightLexBlockCount n h) := ⟨remaining%block.1, width ▸ Nat.mod_lt _ positive⟩
      let head := label first
      let tail := heightNodeUnrankWithWordWork n label h rest
      (⟨head.1::tail.1.val, Nat.succ_le_succ tail.1.property⟩,head.2+tail.2+block.2+16)

theorem heightNodeUnrankWithWordWork_spec {V : Type*} {n : ℕ} (vertices : V ≃ Fin n)
    (label : Fin n → V × ℕ) (budget : ℕ) (equal : ∀ v, (label v).1 = vertices.symm v)
    (bounded : ∀ v, (label v).2 ≤ budget) (h : ℕ) (index : Fin (heightLexBlockCount n h)) :
    let out := heightNodeUnrankWithWordWork n label h index
    out.1 = (heightNodeLexIndex vertices h).symm index ∧ out.2 ≤ heightNodeIndexWordBudget h budget := by
  induction h with
  | zero =>
    refine ⟨rfl, ?_⟩
    simp [heightNodeUnrankWithWordWork, heightNodeIndexWordBudget]
  | succ h ih =>
    by_cases zero : index.val = 0
    · simp only [heightNodeUnrankWithWordWork, zero, ↓reduceDIte]
      constructor
      · apply (heightNodeLexIndex vertices (h+1)).injective
        rw [Equiv.apply_symm_apply]
        apply Fin.ext
        exact zero.symm
      · unfold heightNodeIndexWordBudget
        omega
    · let block := heightLexBlockCountWithWordWork n h
      have width : block.1 = heightLexBlockCount n h := (heightLexBlockCountWithWordWork_spec n h).1
      have positive : 0 < block.1 := width.symm ▸ heightLexBlockCount_positive n h
      let remaining := index.val-1
      let first : Fin n := ⟨remaining/block.1,
        (Nat.div_lt_iff_lt_mul positive).2 (width.symm ▸ heightIndexRemaining_lt index (Nat.pos_of_ne_zero zero))⟩
      let rest : Fin (heightLexBlockCount n h) := ⟨remaining%block.1, width ▸ Nat.mod_lt _ positive⟩
      let head := label first
      let tail := heightNodeUnrankWithWordWork n label h rest
      obtain ⟨tailEq, tailCost⟩ := ih rest
      obtain ⟨_, blockCost⟩ := heightLexBlockCountWithWordWork_spec n h
      simp only [heightNodeUnrankWithWordWork, zero, ↓reduceDIte]
      change (⟨head.1::tail.1.val, Nat.succ_le_succ tail.1.property⟩ : HeightNode V (h+1)) =
        (heightNodeLexIndex vertices (h+1)).symm index ∧
        head.2+tail.2+block.2+16 ≤ heightNodeIndexWordBudget (h+1) budget
      constructor
      · apply (heightNodeLexIndex vertices (h+1)).injective
        rw [Equiv.apply_symm_apply]
        apply Fin.ext
        rw [heightNodeLex_cons, show head.1 = _ from equal first,
          Equiv.apply_symm_apply, show tail.1 = _ from tailEq, Equiv.apply_symm_apply]
        change (remaining/block.1)*heightLexBlockCount n h+remaining%block.1+1 = index.val
        rw [← width]
        have sum := Nat.div_add_mod' remaining block.1
        change _ = index.val-1 at sum
        omega
      · have firstCost : head.2 ≤ budget := bounded first
        have tailWork : tail.2 ≤ heightNodeIndexWordBudget h budget := tailCost
        have blockWork : block.2 = 5*h+1 := blockCost
        rw [blockWork]
        unfold heightNodeIndexWordBudget at tailWork ⊢
        nlinarith

end OnlineReachabilityPreservers
