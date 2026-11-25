import OnlineReachabilityPreservers.SteinerHeightIndexWork

/-! Enumerate the bounded histories once, in the same order as their seed index. -/

namespace OnlineReachabilityPreservers

private def historySuffixWithWordWork {V : Type*} (n h count : ℕ) (count_eq : count = heightLexBlockCount n h)
    (label : Fin n → V × ℕ) : (remaining : ℕ) → remaining ≤ count → List (HeightNode V h) × ℕ :=
  Nat.rec (motive := fun remaining => remaining ≤ count → List (HeightNode V h) × ℕ)
    (fun _ => ([],1)) (fun remaining previous fits =>
      let index : Fin (heightLexBlockCount n h) := ⟨count-(remaining+1),by omega⟩
      let here := heightNodeUnrankWithWordWork n label h index
      let tail := previous (Nat.le_of_succ_le fits)
      (here.1::tail.1,here.2+tail.2+9))

private theorem historySuffixWithWordWork_spec {V : Type*} {n h count : ℕ}
    (count_eq : count = heightLexBlockCount n h) (vertices : V ≃ Fin n)
    (label : Fin n → V × ℕ) (C : ℕ) (same : ∀ i, (label i).1 = vertices.symm i)
    (cost : ∀ i, (label i).2 ≤ C) (remaining : ℕ) (fits : remaining ≤ count) :
    let index := heightNodeLexIndex vertices h
    let out := historySuffixWithWordWork n h count count_eq label remaining fits
    (∀ node, node ∈ out.1 ↔ count-remaining ≤ (index node).val) ∧
      out.1.Pairwise (fun x y => index x < index y) ∧ out.1.length = remaining ∧
      out.2 ≤ (heightNodeIndexWordBudget h C+9)*remaining+1 := by
  induction remaining with
  | zero =>
    refine ⟨fun node => ?_, List.Pairwise.nil, rfl, by simp [historySuffixWithWordWork]⟩
    have below : (heightNodeLexIndex vertices h node).val < count := by
      rw [count_eq]
      exact (heightNodeLexIndex vertices h node).isLt
    change node ∈ ([] : List (HeightNode V h)) ↔ count-0 ≤ _
    simp [not_le_of_gt below]
  | succ remaining ih =>
    let index := heightNodeLexIndex vertices h
    let firstIndex : Fin (heightLexBlockCount n h) := ⟨count-(remaining+1),by omega⟩
    let first := heightNodeUnrankWithWordWork n label h firstIndex
    let tail := historySuffixWithWordWork n h count count_eq label remaining (Nat.le_of_succ_le fits)
    obtain ⟨works,firstCost⟩ := heightNodeUnrankWithWordWork_spec vertices label C same cost h firstIndex
    obtain ⟨memTail,ordered,tailLength,tailCost⟩ := ih (Nat.le_of_succ_le fits)
    have firstRank : index first.1 = firstIndex := by
      change first.1 = index.symm firstIndex at works
      rw [works, Equiv.apply_symm_apply]
    change (∀ node, node ∈ first.1::tail.1 ↔ count-(remaining+1) ≤ (index node).val) ∧
      (first.1::tail.1).Pairwise (fun x y => index x < index y) ∧ (first.1::tail.1).length = remaining+1 ∧
      first.2+tail.2+9 ≤ (heightNodeIndexWordBudget h C+9)*(remaining+1)+1
    refine ⟨?_, List.pairwise_cons.mpr ⟨?_,ordered⟩, ?_, ?_⟩
    · intro node
      rw [List.mem_cons, memTail]
      have exactHead : node = first.1 ↔ (index node).val = count-(remaining+1) := by
        constructor
        · intro eq
          rw [eq,firstRank]
        · intro eq
          apply index.injective
          rw [firstRank]
          exact Fin.ext eq
      rw [exactHead]
      change ((index node).val = count-(remaining+1) ∨ count-remaining ≤ (index node).val) ↔
        count-(remaining+1) ≤ (index node).val
      omega
    · intro node on
      have behind := (memTail node).mp on
      change count-remaining ≤ (index node).val at behind
      rw [firstRank]
      change count-(remaining+1) < (index node).val
      exact (show count-(remaining+1) < count-remaining by omega).trans_le behind
    · exact congrArg Nat.succ tailLength
    · rw [Nat.mul_succ]
      change first.2 ≤ _ at firstCost
      change tail.2 ≤ _ at tailCost
      omega

/-- Compute the history count once and enumerate every slot with the arithmetic unrank. -/
def heightNodesWithWordWork {V : Type*} (n h : ℕ) (label : Fin n → V × ℕ) : List (HeightNode V h) × ℕ :=
  let count := heightLexBlockCountWithWordWork n h
  let all := historySuffixWithWordWork n h count.1 (heightLexBlockCountWithWordWork_spec n h).1 label count.1 le_rfl
  (all.1, count.2+all.2+5)

theorem heightNodesWithWordWork_spec {V : Type*} {n : ℕ} (vertices : V ≃ Fin n)
    (label : Fin n → V × ℕ) (C : ℕ) (same : ∀ i, (label i).1 = vertices.symm i)
    (cost : ∀ i, (label i).2 ≤ C) (h : ℕ) :
    let index := heightNodeLexIndex vertices h
    let H := heightLexBlockCount n h
    let out := heightNodesWithWordWork n h label
    (∀ node, node ∈ out.1) ∧ out.1.Nodup ∧
      out.1.Pairwise (fun x y => index x < index y) ∧ out.1.length = H ∧
      out.2 ≤ (heightNodeIndexWordBudget h C+9)*H+5*h+7 := by
  let counts := heightLexBlockCountWithWordWork n h
  obtain ⟨equal,countCost⟩ := heightLexBlockCountWithWordWork_spec n h
  obtain ⟨members,order,len,work⟩ := historySuffixWithWordWork_spec equal vertices label C same cost counts.1 le_rfl
  have all : ∀ node, node ∈ (heightNodesWithWordWork n h label).1 := by
    intro node
    apply (members node).mpr
    change counts.1-counts.1 ≤ _
    simp
  have distinct : (heightNodesWithWordWork n h label).1.Nodup := by
    apply order.imp
    intro a b strict eq
    exact (lt_irrefl _ (eq ▸ strict))
  have bound : (heightNodesWithWordWork n h label).2 ≤
      (heightNodeIndexWordBudget h C+9)*heightLexBlockCount n h+5*h+7 := by
    dsimp only [heightNodesWithWordWork]
    change counts.1 = _ at equal
    change counts.2 = _ at countCost
    change _ ≤ (heightNodeIndexWordBudget h C+9)*counts.1+1 at work
    have charged := work.trans_eq (show (heightNodeIndexWordBudget h C+9)*counts.1+1 =
        (heightNodeIndexWordBudget h C+9)*heightLexBlockCount n h+1 by rw [equal])
    change (historySuffixWithWordWork n h counts.1 equal label counts.1 le_rfl).2 ≤ _ at charged
    change counts.2+(historySuffixWithWordWork n h counts.1 equal label counts.1 le_rfl).2+5 ≤ _
    omega
  exact ⟨all, distinct, order, len.trans equal, bound⟩

end OnlineReachabilityPreservers
