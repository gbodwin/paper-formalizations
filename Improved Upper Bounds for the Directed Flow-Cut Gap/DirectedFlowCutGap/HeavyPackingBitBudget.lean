import DirectedFlowCutGap.HeavyPackingPrefix
import DirectedFlowCutGap.QueryBudgetPolynomial
import DirectedFlowCutGap.BinaryPackingPrefixBudget

/-! A polynomial sufficient bit-prefix length for the complete adaptive
original-weight packing program. This replaces a proof-side maximum over all
execution branches by one explicit arithmetic expression. Constructing its
inputs and the physical program runtime remain separate. -/
namespace DirectedFlowCutGap.HeavyPackingBitBudget
noncomputable section
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinaryFractionalRows BinarySamplerMetadata
open HeavyCutProvider FiniteDrawTrees LazyFairBitTrees

def bound (n B S : ℕ) (resources width : Bits) : ℕ :=
  (3*n^2+1)*((3*HeavyPackingJoin.oracleExponent n B+1)*
    QueryBudgetArithmetic.polynomial (24*n^2))+
      (2*value width+value resources+3)*(3*n^2*(S+1)+2)

theorem within {n S : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (hw : ∀ i,BinaryRational.StoredBounded (get w i) S) (resources width : Bits) :
    Within (bound n B S resources width) (HeavyPackingPrefix.tree adjacency w B resources width) := by
  unfold HeavyPackingPrefix.tree
  dsimp only []
  split_ifs
  · exact .pure _ _
  · have h := BinaryPackingPrefixBudget.confidence_within w (columns adjacency w)
      (HeavyPackingJoin.support_valid adjacency w) _
      (BinaryHeavyProviderTrees.draw adjacency w (3*HeavyPackingJoin.oracleExponent n B) empty)
      (fun c => QueryBudgetPolynomial.provider_within adjacency w c _ empty) hw resources width
    exact within_bind h _ (r := 0) (fun _ => .pure 0 _)

/-- Coarse polynomial in graph size, semantic confidence width and stored width. -/
def polynomial (n B S : ℕ) : ℕ :=
  (3*n^2+1)*((3*(3*n^2+2*B+n+3)+1)*
    QueryBudgetArithmetic.polynomial (24*n^2))+
      (2*B+n+3)*(3*n^2*(S+1)+2)

theorem bound_le_polynomial (n B S : ℕ) (resources width : Bits)
    (hn : value resources=n) (hB : value width=B) :
    bound n B S resources width≤polynomial n B S := by
  have hs : Nat.size n≤n := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n))
  have ho := FairBitConfidence.trials_le (3*n^2+1) (WeightedFailureBudget.exponent n B+1)
  have hx : HeavyPackingJoin.oracleExponent n B≤3*n^2+2*B+n+3 := by
    unfold HeavyPackingJoin.oracleExponent
    unfold WeightedFailureBudget.exponent at ho
    omega
  unfold bound polynomial
  rw [hn,hB]
  gcongr

theorem within_polynomial {n S : ℕ} (adjacency : RetainedGridState.PairFlags n)
    (w : Row n) (B : ℕ) (hw : ∀ i,BinaryRational.StoredBounded (get w i) S)
    (resources width : Bits) (hn : value resources=n) (hB : value width=B) :
    Within (polynomial n B S) (HeavyPackingPrefix.tree adjacency w B resources width) :=
  within_mono (within adjacency w B hw resources width)
    (bound_le_polynomial n B S resources width hn hB)

/-- Full adaptive result law for this explicit sufficient prefix. No fresh
stream is substituted between calls or before the final weighted ticket. -/
theorem output_law {n S : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (hw : ∀ i,BinaryRational.StoredBounded (get w i) S) (resources width : Bits) :
    (FiniteBinaryPrefix.prefixLaw (bound n B S resources width)).map
      (fun xs => ((HeavyPackingPrefix.read adjacency w B resources width).run xs).1)=
      HeavyPackingEntry.run adjacency w B resources width := by
  rw [HeavyPackingPrefix.read,FiniteBinaryPrefix.output_law
    (within adjacency w B hw resources width) (HeavyPackingPrefix.binary adjacency w B resources width),
    HeavyPackingPrefix.ideal_eq]

theorem suffix {n S : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (hw : ∀ i,BinaryRational.StoredBounded (get w i) S) (resources width : Bits)
    (xs : List (Fin 2)) (hlen : bound n B S resources width≤xs.length) :
    ∃ used≤bound n B S resources width,
      ((HeavyPackingPrefix.read adjacency w B resources width).run xs).2=xs.drop used :=
  FiniteBinaryPrefix.suffix (within adjacency w B hw resources width)
    (HeavyPackingPrefix.binary adjacency w B resources width) xs hlen

end
end DirectedFlowCutGap.HeavyPackingBitBudget
