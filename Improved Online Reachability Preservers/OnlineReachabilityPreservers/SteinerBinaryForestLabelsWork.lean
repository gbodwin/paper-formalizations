import OnlineReachabilityPreservers.SteinerBinaryThinSampleWork
import OnlineReachabilityPreservers.SteinerForestPairKeysWork

/-! Give the metric forest's network vertices exact finite binary labels. -/

namespace OnlineReachabilityPreservers

private def finHeightForestIndex (n h : ℕ) :
    HeightForestVertex (Fin n) h ≃ Fin (n*(2*heightLexBlockCount n h)) :=
  let inner : (Bool ×ₗ HeightNode (Fin n) h) ≃ Fin (2*heightLexBlockCount n h) :=
    ofLex.trans ((finTwoEquiv.symm.prodCongr (heightNodeLexIndex (Equiv.refl (Fin n)) h)).trans finProdFinEquiv)
  ofLex.trans (((Equiv.refl (Fin n)).prodCongr inner).trans finProdFinEquiv)

private def finForestNetworkIndex (n h : ℕ) :
    ForestNetworkVertex (Fin n) h ≃ Fin (3*(n*(2*heightLexBlockCount n h))) :=
  ofLex.trans (((Equiv.refl (Fin 3)).prodCongr (finHeightForestIndex n h)).trans finProdFinEquiv)

private def rankFinForestNetworkWithWordWork {n h : ℕ} (block : ℕ) (v : ForestNetworkVertex (Fin n) h) : ℕ × ℕ :=
  let part := (ofLex v).2
  let history := heightNodeRankWithWordWork n (fun i : Fin n => (i.val,1)) h (heightForestHistory part)
  let side := if heightForestSide part then (1 : ℕ) else 0
  let axis := 2*block
  (history.1+block*side+axis*(heightForestRoot part).val+(n*axis)*(ofLex v).1.val,history.2+20)

private theorem rankFinForestNetworkWithWordWork_spec {n h : ℕ} (v : ForestNetworkVertex (Fin n) h) :
    let out := rankFinForestNetworkWithWordWork (heightLexBlockCount n h) v
    out.1 = (finForestNetworkIndex n h v).val ∧ out.2 ≤ heightNodeIndexWordBudget h 1+20 := by
  let part := (ofLex v).2
  let history := heightForestHistory part
  let block := heightLexBlockCount n h
  obtain ⟨rank,work⟩ := heightNodeRankWithWordWork_spec (Equiv.refl (Fin n)) (fun i => (i.val,1)) 1
    (fun _ => rfl) (fun _ => le_rfl) h history
  constructor
  · dsimp only [rankFinForestNetworkWithWordWork]
    change (heightNodeRankWithWordWork n (fun i : Fin n => (i.val,1)) h history).1+
      block*(if heightForestSide part then 1 else 0)+(2*block)*(heightForestRoot part).val+
        (n*(2*block))*(ofLex v).1.val = _
    rw [rank]
    cases side : heightForestSide part <;>
      simp [finForestNetworkIndex,finHeightForestIndex,finProdFinEquiv_apply_val,part,heightForestSide,
        heightForestRoot,finTwoEquiv,block] at side ⊢ <;> simp [side,history,part,heightForestHistory]
  · exact Nat.add_le_add_right work 20

structure BinaryFinForestNetworkLabels (n h : ℕ) where
  read : ForestNetworkVertex (Fin n) h → List Bool × ℕ
  count : ℕ
  width : ℕ
  work : ℕ

/-- Measure the shared history block and label width once, then encode
each vertex rank using that width. -/
def binaryFinForestNetworkLabelsWithWork (n h : ℕ) : BinaryFinForestNetworkLabels n h :=
  let block := heightLexBlockCountWithWordWork n h
  let count := 3*(n*(2*block.1))
  let width := bitLengthWithWork count
  let read := fun v : ForestNetworkVertex (Fin n) h =>
    let rank := rankFinForestNetworkWithWordWork block.1 v
    let word := encodeBoundedNatWithBinaryWork rank.1 width.1
    (word.1,rank.2+word.2+3)
  ⟨read,count,width.1,block.2+width.2+9⟩

/-- All vertices receive different labels of the measured width, and
the supplied residual depth is the exact number of network vertices. -/
theorem binaryFinForestNetworkLabelsWithWork_spec (n h : ℕ) :
    let out := binaryFinForestNetworkLabelsWithWork n h
    out.count = Fintype.card (ForestNetworkVertex (Fin n) h) ∧
    out.count ≤ 6*n*(n+1)^h ∧ out.width = out.count.size ∧
    Function.Injective (fun v => (out.read v).1) ∧
    (∀ v, (out.read v).1.length = out.width ∧
      (out.read v).2 ≤ heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget out.width+23) ∧
    out.work ≤ 5*h+7*out.count+13 := by
  let out := binaryFinForestNetworkLabelsWithWork n h
  let block := heightLexBlockCount n h
  let count := 3*(n*(2*block))
  obtain ⟨history,historyWork⟩ := heightLexBlockCountWithWordWork_spec n h
  have countEq : out.count = count := by dsimp only [out,binaryFinForestNetworkLabelsWithWork,count,block]; rw [history]
  have exactCount := (Fintype.card_congr (finForestNetworkIndex n h)).trans (Fintype.card_fin _)
  have countBound : count ≤ 6*n*(n+1)^h := by
    change 3*(n*(2*block)) ≤ _
    have steps : block ≤ (n+1)^h := heightLexBlockCount_le_pow n h
    calc
      _ ≤ 3*(n*(2*((n+1)^h))) := by gcongr
      _ = _ := by ring
  have exactWidth : out.width = out.count.size := (bitLengthWithWork_spec _).1
  have labels (v : ForestNetworkVertex (Fin n) h) :
      binaryWordValue (out.read v).1 = (finForestNetworkIndex n h v).val ∧
      (out.read v).1.length = out.width ∧
      (out.read v).2 ≤ heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget out.width+23 := by
    let rank := rankFinForestNetworkWithWordWork block v
    obtain ⟨numeric,rankWork⟩ := rankFinForestNetworkWithWordWork_spec v
    have fits : rank.1 < 2^out.width := by
      change rank.1 = _ at numeric
      rw [numeric,exactWidth,countEq]
      exact ((finForestNetworkIndex n h v).isLt).trans (Nat.lt_size_self count)
    obtain ⟨value,length,fee⟩ := encodeBoundedNatWithBinaryWork_spec rank.1 out.width fits
    have readEq : out.read v =
        ((encodeBoundedNatWithBinaryWork rank.1 out.width).1,rank.2+(encodeBoundedNatWithBinaryWork rank.1 out.width).2+3) := by
      dsimp only [out,binaryFinForestNetworkLabelsWithWork,rank,block]
      rw [history]
    rw [readEq]
    change rank.2 ≤ _ at rankWork
    exact ⟨value.trans numeric,length,by omega⟩
  refine ⟨countEq.trans exactCount.symm,countEq ▸ countBound,exactWidth,?_,fun v => (labels v).2,?_⟩
  · intro u v hu
    apply (finForestNetworkIndex n h).injective
    apply Fin.ext
    exact (labels u).1.symm.trans ((congrArg binaryWordValue hu).trans (labels v).1)
  · have widthWork := bitLengthWork_le out.count
    have setup : out.work = (heightLexBlockCountWithWordWork n h).2+(bitLengthWithWork out.count).2+9 := rfl
    rw [setup,historyWork]
    change (bitLengthWithWork out.count).2 ≤ 7*out.count+3 at widthWork
    change 5*h+1+(bitLengthWithWork out.count).2+9 ≤ 5*h+7*out.count+13
    omega

end OnlineReachabilityPreservers
