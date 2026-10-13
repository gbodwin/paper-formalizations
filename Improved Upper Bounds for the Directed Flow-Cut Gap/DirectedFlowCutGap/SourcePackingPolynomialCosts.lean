import DirectedFlowCutGap.SourcePackingLengthExecution
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Explicit polynomial majorants for every original input-cost formula.
The only relaxation replaces max(1,m) by 1+m. No machine is changed. -/
noncomputable section
namespace DirectedFlowCutGap.SourcePackingPolynomial
open Polynomial

def poly_RowVertices_instructionBound ( n : Polynomial ℕ) : Polynomial ℕ := (8*n+19)*n+10

theorem bound_RowVertices_instructionBound (x : ℕ) {n : ℕ} {p_n : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) :
    RowVertices.instructionBound n ≤ (poly_RowVertices_instructionBound p_n).eval x := by
  dsimp only [RowVertices.instructionBound,poly_RowVertices_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr

def poly_PackingParameters_instructionBound ( n : Polynomial ℕ) : Polynomial ℕ := 1200*(3*n+12)^2

theorem bound_PackingParameters_instructionBound (x : ℕ) {n : ℕ} {p_n : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) :
    PackingParameters.instructionBound n ≤ (poly_PackingParameters_instructionBound p_n).eval x := by
  dsimp only [PackingParameters.instructionBound,poly_PackingParameters_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat]
  gcongr

def poly_ScalarQuotientRow_instructionBound ( n B : Polynomial ℕ) : Polynomial ℕ := n*(600*(4*B+2)^2+14)+4

theorem bound_ScalarQuotientRow_instructionBound (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    ScalarQuotientRow.instructionBound n B ≤ (poly_ScalarQuotientRow_instructionBound p_n p_B).eval x := by
  dsimp only [ScalarQuotientRow.instructionBound,poly_ScalarQuotientRow_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat]
  gcongr

def poly_GraphRelaxationProgram_perEntryBound ( B N S : Polynomial ℕ) : Polynomial ℕ := 12*N+20*B+100*(S+B+N+1)+20000*(4*B+2)^2+400*(8*B+9)^2+93

theorem bound_GraphRelaxationProgram_perEntryBound (x : ℕ) {B N S : ℕ} {p_B p_N p_S : Polynomial ℕ}
    (h0 : B ≤ (p_B).eval x) (h1 : N ≤ (p_N).eval x) (h2 : S ≤ (p_S).eval x) :
    GraphRelaxationProgram.perEntryBound B N S ≤ (poly_GraphRelaxationProgram_perEntryBound p_B p_N p_S).eval x := by
  dsimp only [GraphRelaxationProgram.perEntryBound,poly_GraphRelaxationProgram_perEntryBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr

def poly_GraphRelaxationProgram_instructionBound ( m B N S : Polynomial ℕ) : Polynomial ℕ := m*poly_GraphRelaxationProgram_perEntryBound B N S+4

theorem bound_GraphRelaxationProgram_instructionBound (x : ℕ) {m B N S : ℕ} {p_m p_B p_N p_S : Polynomial ℕ}
    (h0 : m ≤ (p_m).eval x) (h1 : B ≤ (p_B).eval x) (h2 : N ≤ (p_N).eval x) (h3 : S ≤ (p_S).eval x) :
    GraphRelaxationProgram.instructionBound m B N S ≤ (poly_GraphRelaxationProgram_instructionBound p_m p_B p_N p_S).eval x := by
  dsimp only [GraphRelaxationProgram.instructionBound,poly_GraphRelaxationProgram_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_GraphRelaxationProgram_perEntryBound])

def poly_GraphDiscoveryProgram_passBudget ( m M W N S : Polynomial ℕ) : Polynomial ℕ := m*(32*W+poly_GraphRelaxationProgram_instructionBound M W N S+60)+3

theorem bound_GraphDiscoveryProgram_passBudget (x : ℕ) {m M W N S : ℕ} {p_m p_M p_W p_N p_S : Polynomial ℕ}
    (h0 : m ≤ (p_m).eval x) (h1 : M ≤ (p_M).eval x) (h2 : W ≤ (p_W).eval x) (h3 : N ≤ (p_N).eval x) (h4 : S ≤ (p_S).eval x) :
    GraphDiscoveryProgram.passBudget m M W N S ≤ (poly_GraphDiscoveryProgram_passBudget p_m p_M p_W p_N p_S).eval x := by
  dsimp only [GraphDiscoveryProgram.passBudget,poly_GraphDiscoveryProgram_passBudget]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_GraphRelaxationProgram_instructionBound])

def poly_GraphDiscoveryProgram_roundBudget ( m k W N S : Polynomial ℕ) : Polynomial ℕ := k*(poly_GraphDiscoveryProgram_passBudget m (1+m) W N S+11)+13

theorem bound_GraphDiscoveryProgram_roundBudget (x : ℕ) {m k W N S : ℕ} {p_m p_k p_W p_N p_S : Polynomial ℕ}
    (h0 : m ≤ (p_m).eval x) (h1 : k ≤ (p_k).eval x) (h2 : W ≤ (p_W).eval x) (h3 : N ≤ (p_N).eval x) (h4 : S ≤ (p_S).eval x) :
    GraphDiscoveryProgram.roundBudget m k W N S ≤ (poly_GraphDiscoveryProgram_roundBudget p_m p_k p_W p_N p_S).eval x := by
  have hmax_m : max 1 m ≤ 1+(p_m).eval x := max_le (by omega) (by omega)
  dsimp only [GraphDiscoveryProgram.roundBudget,poly_GraphDiscoveryProgram_roundBudget]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_GraphDiscoveryProgram_passBudget])

def poly_GraphDiscoveryProgram_roundWidth ( B k : Polynomial ℕ) : Polynomial ℕ := 1+k*(B+2)

theorem bound_GraphDiscoveryProgram_roundWidth (x : ℕ) {B k : ℕ} {p_B p_k : Polynomial ℕ}
    (h0 : B ≤ (p_B).eval x) (h1 : k ≤ (p_k).eval x) :
    GraphDiscoveryProgram.roundWidth B k ≤ (poly_GraphDiscoveryProgram_roundWidth p_B p_k).eval x := by
  dsimp only [GraphDiscoveryProgram.roundWidth,poly_GraphDiscoveryProgram_roundWidth]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr

def poly_GraphDiscoveryProgram_discoveryWidth ( m B : Polynomial ℕ) : Polynomial ℕ := B+poly_GraphDiscoveryProgram_roundWidth B m

theorem bound_GraphDiscoveryProgram_discoveryWidth (x : ℕ) {m B : ℕ} {p_m p_B : Polynomial ℕ}
    (h0 : m ≤ (p_m).eval x) (h1 : B ≤ (p_B).eval x) :
    GraphDiscoveryProgram.discoveryWidth m B ≤ (poly_GraphDiscoveryProgram_discoveryWidth p_m p_B).eval x := by
  dsimp only [GraphDiscoveryProgram.discoveryWidth,poly_GraphDiscoveryProgram_discoveryWidth]
  simp only [Polynomial.eval_add]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_GraphDiscoveryProgram_roundWidth])

def poly_GraphDiscoveryProgram_lookupBudget ( m W : Polynomial ℕ) : Polynomial ℕ := m*(32*W+400*(4*W+1)^2+60)+3

theorem bound_GraphDiscoveryProgram_lookupBudget (x : ℕ) {m W : ℕ} {p_m p_W : Polynomial ℕ}
    (h0 : m ≤ (p_m).eval x) (h1 : W ≤ (p_W).eval x) :
    GraphDiscoveryProgram.lookupBudget m W ≤ (poly_GraphDiscoveryProgram_lookupBudget p_m p_W).eval x := by
  dsimp only [GraphDiscoveryProgram.lookupBudget,poly_GraphDiscoveryProgram_lookupBudget]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr

def poly_GraphDiscoveryProgram_discoveryBudget ( m B N S : Polynomial ℕ) : Polynomial ℕ := poly_GraphDiscoveryProgram_roundBudget m m (poly_GraphDiscoveryProgram_discoveryWidth m B) N S+
    poly_GraphDiscoveryProgram_lookupBudget (1+m) (poly_GraphDiscoveryProgram_discoveryWidth m B)+6

theorem bound_GraphDiscoveryProgram_discoveryBudget (x : ℕ) {m B N S : ℕ} {p_m p_B p_N p_S : Polynomial ℕ}
    (h0 : m ≤ (p_m).eval x) (h1 : B ≤ (p_B).eval x) (h2 : N ≤ (p_N).eval x) (h3 : S ≤ (p_S).eval x) :
    GraphDiscoveryProgram.discoveryBudget m B N S ≤ (poly_GraphDiscoveryProgram_discoveryBudget p_m p_B p_N p_S).eval x := by
  have hmax_m : max 1 m ≤ 1+(p_m).eval x := max_le (by omega) (by omega)
  dsimp only [GraphDiscoveryProgram.discoveryBudget,poly_GraphDiscoveryProgram_discoveryBudget]
  simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_GraphDiscoveryProgram_roundBudget, bound_GraphDiscoveryProgram_discoveryWidth, bound_GraphDiscoveryProgram_lookupBudget])

def poly_SupportRecoveryProgram_scanCap ( S W N : Polynomial ℕ) : Polynomial ℕ := S*(64*W+57)+12*N+52*W+87

theorem bound_SupportRecoveryProgram_scanCap (x : ℕ) {S W N : ℕ} {p_S p_W p_N : Polynomial ℕ}
    (h0 : S ≤ (p_S).eval x) (h1 : W ≤ (p_W).eval x) (h2 : N ≤ (p_N).eval x) :
    SupportRecoveryProgram.scanCap S W N ≤ (poly_SupportRecoveryProgram_scanCap p_S p_W p_N).eval x := by
  dsimp only [SupportRecoveryProgram.scanCap,poly_SupportRecoveryProgram_scanCap]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr

def poly_SupportRecoveryProgram_searchCap ( V S W N : Polynomial ℕ) : Polynomial ℕ := V*(V*((1+V*V)*poly_SupportRecoveryProgram_scanCap S W N+40)+12)+(1+V*V)*(32*W+27)+16

theorem bound_SupportRecoveryProgram_searchCap (x : ℕ) {V S W N : ℕ} {p_V p_S p_W p_N : Polynomial ℕ}
    (h0 : V ≤ (p_V).eval x) (h1 : S ≤ (p_S).eval x) (h2 : W ≤ (p_W).eval x) (h3 : N ≤ (p_N).eval x) :
    SupportRecoveryProgram.searchCap V S W N ≤ (poly_SupportRecoveryProgram_searchCap p_V p_S p_W p_N).eval x := by
  dsimp only [SupportRecoveryProgram.searchCap,poly_SupportRecoveryProgram_searchCap]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_SupportRecoveryProgram_scanCap])

def poly_CanonicalRationalSum_instructionBound ( n B : Polynomial ℕ) : Polynomial ℕ := n*(720000*((n+1)*(B+1)+1)^2+10)+7

theorem bound_CanonicalRationalSum_instructionBound (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    CanonicalRationalSum.instructionBound n B ≤ (poly_CanonicalRationalSum_instructionBound p_n p_B).eval x := by
  dsimp only [CanonicalRationalSum.instructionBound,poly_CanonicalRationalSum_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr

def poly_MaterializedPathSum_instructionBound ( m B N sourceLength : Polynomial ℕ) : Polynomial ℕ := m*(100*(sourceLength+B+N+1)+11)+poly_CanonicalRationalSum_instructionBound m B+7

theorem bound_MaterializedPathSum_instructionBound (x : ℕ) {m B N sourceLength : ℕ} {p_m p_B p_N p_sourceLength : Polynomial ℕ}
    (h0 : m ≤ (p_m).eval x) (h1 : B ≤ (p_B).eval x) (h2 : N ≤ (p_N).eval x) (h3 : sourceLength ≤ (p_sourceLength).eval x) :
    MaterializedPathSum.instructionBound m B N sourceLength ≤ (poly_MaterializedPathSum_instructionBound p_m p_B p_N p_sourceLength).eval x := by
  dsimp only [MaterializedPathSum.instructionBound,poly_MaterializedPathSum_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_CanonicalRationalSum_instructionBound])

def poly_CostedSupportProgram_recoveryCap ( N S W : Polynomial ℕ) : Polynomial ℕ := poly_SupportRecoveryProgram_searchCap N S W N+7*N+
  poly_MaterializedPathSum_instructionBound N W N W+23

theorem bound_CostedSupportProgram_recoveryCap (x : ℕ) {N S W : ℕ} {p_N p_S p_W : Polynomial ℕ}
    (h0 : N ≤ (p_N).eval x) (h1 : S ≤ (p_S).eval x) (h2 : W ≤ (p_W).eval x) :
    CostedSupportProgram.recoveryCap N S W ≤ (poly_CostedSupportProgram_recoveryCap p_N p_S p_W).eval x := by
  dsimp only [CostedSupportProgram.recoveryCap,poly_CostedSupportProgram_recoveryCap]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_SupportRecoveryProgram_searchCap, bound_MaterializedPathSum_instructionBound])

def poly_GraphRecoveryController_instructionBound ( N W S : Polynomial ℕ) : Polynomial ℕ := poly_GraphDiscoveryProgram_discoveryBudget N W N S+poly_CostedSupportProgram_recoveryCap N N W+24

theorem bound_GraphRecoveryController_instructionBound (x : ℕ) {N W S : ℕ} {p_N p_W p_S : Polynomial ℕ}
    (h0 : N ≤ (p_N).eval x) (h1 : W ≤ (p_W).eval x) (h2 : S ≤ (p_S).eval x) :
    GraphRecoveryController.instructionBound N W S ≤ (poly_GraphRecoveryController_instructionBound p_N p_W p_S).eval x := by
  dsimp only [GraphRecoveryController.instructionBound,poly_GraphRecoveryController_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_GraphDiscoveryProgram_discoveryBudget, bound_CostedSupportProgram_recoveryCap])

def poly_DemandCollection_instructionBound ( k n W : Polynomial ℕ) : Polynomial ℕ := k*(poly_GraphRecoveryController_instructionBound n W W+37)+
    (6400*(n*(W+1)+2)^2+12)*k+10

theorem bound_DemandCollection_instructionBound (x : ℕ) {k n W : ℕ} {p_k p_n p_W : Polynomial ℕ}
    (h0 : k ≤ (p_k).eval x) (h1 : n ≤ (p_n).eval x) (h2 : W ≤ (p_W).eval x) :
    DemandCollection.instructionBound k n W ≤ (poly_DemandCollection_instructionBound p_k p_n p_W).eval x := by
  dsimp only [DemandCollection.instructionBound,poly_DemandCollection_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_GraphRecoveryController_instructionBound])

def poly_OracleMask_instructionBound ( vertices edges W : Polynomial ℕ) : Polynomial ℕ := (vertices+1)*((edges+3)*(32*W+30)+11)+1

theorem bound_OracleMask_instructionBound (x : ℕ) {vertices edges W : ℕ} {p_vertices p_edges p_W : Polynomial ℕ}
    (h0 : vertices ≤ (p_vertices).eval x) (h1 : edges ≤ (p_edges).eval x) (h2 : W ≤ (p_W).eval x) :
    OracleMask.instructionBound vertices edges W ≤ (poly_OracleMask_instructionBound p_vertices p_edges p_W).eval x := by
  dsimp only [OracleMask.instructionBound,poly_OracleMask_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr

def poly_CapacityBottleneck_instructionBound ( n W : Polynomial ℕ) : Polynomial ℕ := (6400*(W+1)^2+36)*n+10

theorem bound_CapacityBottleneck_instructionBound (x : ℕ) {n W : ℕ} {p_n p_W : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : W ≤ (p_W).eval x) :
    CapacityBottleneck.instructionBound n W ≤ (poly_CapacityBottleneck_instructionBound p_n p_W).eval x := by
  dsimp only [CapacityBottleneck.instructionBound,poly_CapacityBottleneck_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr

def poly_GraphOracleMachine_instructionBound ( demands n W : Polynomial ℕ) : Polynomial ℕ := poly_DemandCollection_instructionBound demands n W+poly_OracleMask_instructionBound n n W+
    poly_CapacityBottleneck_instructionBound n W+6*n+40

theorem bound_GraphOracleMachine_instructionBound (x : ℕ) {demands n W : ℕ} {p_demands p_n p_W : Polynomial ℕ}
    (h0 : demands ≤ (p_demands).eval x) (h1 : n ≤ (p_n).eval x) (h2 : W ≤ (p_W).eval x) :
    GraphOracleMachine.instructionBound demands n W ≤ (poly_GraphOracleMachine_instructionBound p_demands p_n p_W).eval x := by
  dsimp only [GraphOracleMachine.instructionBound,poly_GraphOracleMachine_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_DemandCollection_instructionBound, bound_OracleMask_instructionBound, bound_CapacityBottleneck_instructionBound])

def poly_PackingStart_initialWidth ( B : Polynomial ℕ) : Polynomial ℕ := B+B+1

theorem bound_PackingStart_initialWidth (x : ℕ) {B : ℕ} {p_B : Polynomial ℕ}
    (h0 : B ≤ (p_B).eval x) :
    PackingStart.initialWidth B ≤ (poly_PackingStart_initialWidth p_B).eval x := by
  dsimp only [PackingStart.initialWidth,poly_PackingStart_initialWidth]
  simp only [Polynomial.eval_add,Polynomial.eval_one]
  gcongr

def poly_NormalizedRow_scalarWidth ( n B : Polynomial ℕ) : Polynomial ℕ := (n+1)*(B+2)+1

theorem bound_NormalizedRow_scalarWidth (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    NormalizedRow.scalarWidth n B ≤ (poly_NormalizedRow_scalarWidth p_n p_B).eval x := by
  dsimp only [NormalizedRow.scalarWidth,poly_NormalizedRow_scalarWidth]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr

def poly_NormalizedRow_instructionBound ( n B : Polynomial ℕ) : Polynomial ℕ := 17*n+4+poly_CanonicalRationalSum_instructionBound n (B+1)+
    poly_ScalarQuotientRow_instructionBound n (poly_NormalizedRow_scalarWidth n B)+10

theorem bound_NormalizedRow_instructionBound (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    NormalizedRow.instructionBound n B ≤ (poly_NormalizedRow_instructionBound p_n p_B).eval x := by
  dsimp only [NormalizedRow.instructionBound,poly_NormalizedRow_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_CanonicalRationalSum_instructionBound, bound_ScalarQuotientRow_instructionBound, bound_NormalizedRow_scalarWidth])

def poly_ObjectiveProductList_instructionBound ( n B : Polynomial ℕ) : Polynomial ℕ := n*(500*(4*B+2)^2+15)+4

theorem bound_ObjectiveProductList_instructionBound (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    ObjectiveProductList.instructionBound n B ≤ (poly_ObjectiveProductList_instructionBound p_n p_B).eval x := by
  dsimp only [ObjectiveProductList.instructionBound,poly_ObjectiveProductList_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat]
  gcongr

def poly_ObjectiveRow_instructionBound ( n B : Polynomial ℕ) : Polynomial ℕ := poly_ObjectiveProductList_instructionBound n B+poly_CanonicalRationalSum_instructionBound n (B+B+1)+5

theorem bound_ObjectiveRow_instructionBound (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    ObjectiveRow.instructionBound n B ≤ (poly_ObjectiveRow_instructionBound p_n p_B).eval x := by
  dsimp only [ObjectiveRow.instructionBound,poly_ObjectiveRow_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_ObjectiveProductList_instructionBound, bound_CanonicalRationalSum_instructionBound])

def poly_PackingStart_bestWidth ( n B : Polynomial ℕ) : Polynomial ℕ := let S := poly_NormalizedRow_scalarWidth n (poly_PackingStart_initialWidth B)
  S+S+1

theorem bound_PackingStart_bestWidth (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    PackingStart.bestWidth n B ≤ (poly_PackingStart_bestWidth p_n p_B).eval x := by
  dsimp only [PackingStart.bestWidth,poly_PackingStart_bestWidth]
  simp only [Polynomial.eval_add,Polynomial.eval_one]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_NormalizedRow_scalarWidth, bound_PackingStart_initialWidth])

def poly_PackingStart_instructionBound ( d n B : Polynomial ℕ) : Polynomial ℕ := poly_ScalarQuotientRow_instructionBound n B+
    poly_GraphOracleMachine_instructionBound d n (poly_PackingStart_initialWidth B)+
    poly_NormalizedRow_instructionBound n (poly_PackingStart_initialWidth B)+
    poly_ObjectiveRow_instructionBound n (poly_PackingStart_bestWidth n B)+5*n+64

theorem bound_PackingStart_instructionBound (x : ℕ) {d n B : ℕ} {p_d p_n p_B : Polynomial ℕ}
    (h0 : d ≤ (p_d).eval x) (h1 : n ≤ (p_n).eval x) (h2 : B ≤ (p_B).eval x) :
    PackingStart.instructionBound d n B ≤ (poly_PackingStart_instructionBound p_d p_n p_B).eval x := by
  dsimp only [PackingStart.instructionBound,poly_PackingStart_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_ScalarQuotientRow_instructionBound, bound_GraphOracleMachine_instructionBound, bound_PackingStart_initialWidth, bound_NormalizedRow_instructionBound, bound_ObjectiveRow_instructionBound, bound_PackingStart_bestWidth])

def poly_PackingGuard_objectiveWidth ( n B : Polynomial ℕ) : Polynomial ℕ := n*(B+B+2)+1

theorem bound_PackingGuard_objectiveWidth (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    PackingGuard.objectiveWidth n B ≤ (poly_PackingGuard_objectiveWidth p_n p_B).eval x := by
  dsimp only [PackingGuard.objectiveWidth,poly_PackingGuard_objectiveWidth]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr

def poly_PackingGuard_instructionBound ( n B : Polynomial ℕ) : Polynomial ℕ := poly_ObjectiveRow_instructionBound n B+400*(2*poly_PackingGuard_objectiveWidth n B+3)^2+12

theorem bound_PackingGuard_instructionBound (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    PackingGuard.instructionBound n B ≤ (poly_PackingGuard_instructionBound p_n p_B).eval x := by
  dsimp only [PackingGuard.instructionBound,poly_PackingGuard_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_ObjectiveRow_instructionBound, bound_PackingGuard_objectiveWidth])

def poly_AdaptivePackingState_normalizedWidth ( n B : Polynomial ℕ) : Polynomial ℕ := poly_NormalizedRow_scalarWidth n B+poly_NormalizedRow_scalarWidth n B+1

theorem bound_AdaptivePackingState_normalizedWidth (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    AdaptivePackingState.normalizedWidth n B ≤ (poly_AdaptivePackingState_normalizedWidth p_n p_B).eval x := by
  dsimp only [AdaptivePackingState.normalizedWidth,poly_AdaptivePackingState_normalizedWidth]
  simp only [Polynomial.eval_add,Polynomial.eval_one]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_NormalizedRow_scalarWidth])

def poly_PackingEntry_instructionBound ( B : Polynomial ℕ) : Polynomial ℕ := 22000*(4*(2*B+7)+2)^2+35

theorem bound_PackingEntry_instructionBound (x : ℕ) {B : ℕ} {p_B : Polynomial ℕ}
    (h0 : B ≤ (p_B).eval x) :
    PackingEntry.instructionBound B ≤ (poly_PackingEntry_instructionBound p_B).eval x := by
  dsimp only [PackingEntry.instructionBound,poly_PackingEntry_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat]
  gcongr

def poly_PackingUpdateRow_instructionBound ( n B : Polynomial ℕ) : Polynomial ℕ := n*(poly_PackingEntry_instructionBound B+32)+4

theorem bound_PackingUpdateRow_instructionBound (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    PackingUpdateRow.instructionBound n B ≤ (poly_PackingUpdateRow_instructionBound p_n p_B).eval x := by
  dsimp only [PackingUpdateRow.instructionBound,poly_PackingUpdateRow_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_PackingEntry_instructionBound])

def poly_PackingLoadRow_entryBound ( B : Polynomial ℕ) : Polynomial ℕ := 20000*(4*(B+1)+2)^2+8

theorem bound_PackingLoadRow_entryBound (x : ℕ) {B : ℕ} {p_B : Polynomial ℕ}
    (h0 : B ≤ (p_B).eval x) :
    PackingLoadRow.entryBound B ≤ (poly_PackingLoadRow_entryBound p_B).eval x := by
  dsimp only [PackingLoadRow.entryBound,poly_PackingLoadRow_entryBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr

def poly_PackingLoadRow_instructionBound ( n B : Polynomial ℕ) : Polynomial ℕ := n*(poly_PackingLoadRow_entryBound B+21)+4

theorem bound_PackingLoadRow_instructionBound (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    PackingLoadRow.instructionBound n B ≤ (poly_PackingLoadRow_instructionBound p_n p_B).eval x := by
  dsimp only [PackingLoadRow.instructionBound,poly_PackingLoadRow_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_PackingLoadRow_entryBound])

def poly_AdaptivePackingState_instructionBound ( d n B : Polynomial ℕ) : Polynomial ℕ := poly_PackingGuard_instructionBound n B+poly_GraphOracleMachine_instructionBound d n B+6*n+10*B+
    poly_NormalizedRow_instructionBound n B+poly_ObjectiveRow_instructionBound n (poly_AdaptivePackingState_normalizedWidth n B)+
    400*(2*B+2*poly_PackingGuard_objectiveWidth n (poly_AdaptivePackingState_normalizedWidth n B)+2)^2+
    poly_PackingUpdateRow_instructionBound n B+20000*(4*B+2)^2+poly_PackingLoadRow_instructionBound n B+300

theorem bound_AdaptivePackingState_instructionBound (x : ℕ) {d n B : ℕ} {p_d p_n p_B : Polynomial ℕ}
    (h0 : d ≤ (p_d).eval x) (h1 : n ≤ (p_n).eval x) (h2 : B ≤ (p_B).eval x) :
    AdaptivePackingState.instructionBound d n B ≤ (poly_AdaptivePackingState_instructionBound p_d p_n p_B).eval x := by
  dsimp only [AdaptivePackingState.instructionBound,poly_AdaptivePackingState_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_PackingGuard_instructionBound, bound_GraphOracleMachine_instructionBound, bound_NormalizedRow_instructionBound, bound_ObjectiveRow_instructionBound, bound_AdaptivePackingState_normalizedWidth, bound_PackingGuard_objectiveWidth, bound_PackingUpdateRow_instructionBound, bound_PackingLoadRow_instructionBound])

def poly_PackingIteration_smallWidth ( B t : Polynomial ℕ) : Polynomial ℕ := B+t*(2*B+8)

theorem bound_PackingIteration_smallWidth (x : ℕ) {B t : ℕ} {p_B p_t : Polynomial ℕ}
    (h0 : B ≤ (p_B).eval x) (h1 : t ≤ (p_t).eval x) :
    PackingIteration.smallWidth B t ≤ (poly_PackingIteration_smallWidth p_B p_t).eval x := by
  dsimp only [PackingIteration.smallWidth,poly_PackingIteration_smallWidth]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr

def poly_PackingIteration_commonWidth ( n B t : Polynomial ℕ) : Polynomial ℕ := poly_PackingIteration_smallWidth B t+poly_PackingGuard_objectiveWidth n (poly_AdaptivePackingState_normalizedWidth n (poly_PackingIteration_smallWidth B t))+B

theorem bound_PackingIteration_commonWidth (x : ℕ) {n B t : ℕ} {p_n p_B p_t : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) (h2 : t ≤ (p_t).eval x) :
    PackingIteration.commonWidth n B t ≤ (poly_PackingIteration_commonWidth p_n p_B p_t).eval x := by
  dsimp only [PackingIteration.commonWidth,poly_PackingIteration_commonWidth]
  simp only [Polynomial.eval_add]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_PackingIteration_smallWidth, bound_PackingGuard_objectiveWidth, bound_AdaptivePackingState_normalizedWidth])

def poly_PackingIteration_instructionBound ( d n B fuel bits : Polynomial ℕ) : Polynomial ℕ := fuel*(poly_AdaptivePackingState_instructionBound d n (poly_PackingIteration_commonWidth n B fuel)+12)+10*bits+13

theorem bound_PackingIteration_instructionBound (x : ℕ) {d n B fuel bits : ℕ} {p_d p_n p_B p_fuel p_bits : Polynomial ℕ}
    (h0 : d ≤ (p_d).eval x) (h1 : n ≤ (p_n).eval x) (h2 : B ≤ (p_B).eval x) (h3 : fuel ≤ (p_fuel).eval x) (h4 : bits ≤ (p_bits).eval x) :
    PackingIteration.instructionBound d n B fuel bits ≤ (poly_PackingIteration_instructionBound p_d p_n p_B p_fuel p_bits).eval x := by
  dsimp only [PackingIteration.instructionBound,poly_PackingIteration_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_AdaptivePackingState_instructionBound, bound_PackingIteration_commonWidth])

def poly_PackingRun_startWidth ( n B : Polynomial ℕ) : Polynomial ℕ := poly_PackingStart_initialWidth B+poly_PackingStart_bestWidth n B+
    poly_PackingGuard_objectiveWidth n (poly_PackingStart_bestWidth n B)+B+2

theorem bound_PackingRun_startWidth (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    PackingRun.startWidth n B ≤ (poly_PackingRun_startWidth p_n p_B).eval x := by
  dsimp only [PackingRun.startWidth,poly_PackingRun_startWidth]
  simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_PackingStart_initialWidth, bound_PackingStart_bestWidth, bound_PackingGuard_objectiveWidth])

def poly_PackingRun_instructionBound ( d n B fuel bits : Polynomial ℕ) : Polynomial ℕ := poly_PackingStart_instructionBound d n B+poly_PackingIteration_instructionBound d n (poly_PackingRun_startWidth n B) fuel bits+7

theorem bound_PackingRun_instructionBound (x : ℕ) {d n B fuel bits : ℕ} {p_d p_n p_B p_fuel p_bits : Polynomial ℕ}
    (h0 : d ≤ (p_d).eval x) (h1 : n ≤ (p_n).eval x) (h2 : B ≤ (p_B).eval x) (h3 : fuel ≤ (p_fuel).eval x) (h4 : bits ≤ (p_bits).eval x) :
    PackingRun.instructionBound d n B fuel bits ≤ (poly_PackingRun_instructionBound p_d p_n p_B p_fuel p_bits).eval x := by
  dsimp only [PackingRun.instructionBound,poly_PackingRun_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_PackingStart_instructionBound, bound_PackingIteration_instructionBound, bound_PackingRun_startWidth])

def poly_PackingComplete_parameterWidth ( n B : Polynomial ℕ) : Polynomial ℕ := B+3*n+9

theorem bound_PackingComplete_parameterWidth (x : ℕ) {n B : ℕ} {p_n p_B : Polynomial ℕ}
    (h0 : n ≤ (p_n).eval x) (h1 : B ≤ (p_B).eval x) :
    PackingComplete.parameterWidth n B ≤ (poly_PackingComplete_parameterWidth p_n p_B).eval x := by
  dsimp only [PackingComplete.parameterWidth,poly_PackingComplete_parameterWidth]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  gcongr

def poly_PackingComplete_instructionBound ( d n B : Polynomial ℕ) : Polynomial ℕ := poly_PackingParameters_instructionBound n+
  poly_PackingRun_instructionBound d n (poly_PackingComplete_parameterWidth n B) (3*n^2) (3*n+6)+8

theorem bound_PackingComplete_instructionBound (x : ℕ) {d n B : ℕ} {p_d p_n p_B : Polynomial ℕ}
    (h0 : d ≤ (p_d).eval x) (h1 : n ≤ (p_n).eval x) (h2 : B ≤ (p_B).eval x) :
    PackingComplete.instructionBound d n B ≤ (poly_PackingComplete_instructionBound p_d p_n p_B).eval x := by
  dsimp only [PackingComplete.instructionBound,poly_PackingComplete_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_PackingParameters_instructionBound, bound_PackingRun_instructionBound, bound_PackingComplete_parameterWidth])

def poly_PreparedPacking_instructionBound ( d n B : Polynomial ℕ) : Polynomial ℕ := poly_PackingComplete_instructionBound d n B+8

theorem bound_PreparedPacking_instructionBound (x : ℕ) {d n B : ℕ} {p_d p_n p_B : Polynomial ℕ}
    (h0 : d ≤ (p_d).eval x) (h1 : n ≤ (p_n).eval x) (h2 : B ≤ (p_B).eval x) :
    PreparedPacking.instructionBound d n B ≤ (poly_PreparedPacking_instructionBound p_d p_n p_B).eval x := by
  dsimp only [PreparedPacking.instructionBound,poly_PreparedPacking_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
  gcongr; aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_PackingComplete_instructionBound])

def poly_EnumeratedPacking_instructionBound ( d n B : Polynomial ℕ) : Polynomial ℕ := poly_RowVertices_instructionBound n+poly_PreparedPacking_instructionBound d n (B+n)+4

theorem bound_EnumeratedPacking_instructionBound (x : ℕ) {d n B : ℕ} {p_d p_n p_B : Polynomial ℕ}
    (h0 : d ≤ (p_d).eval x) (h1 : n ≤ (p_n).eval x) (h2 : B ≤ (p_B).eval x) :
    EnumeratedPacking.instructionBound d n B ≤ (poly_EnumeratedPacking_instructionBound p_d p_n p_B).eval x := by
  dsimp only [EnumeratedPacking.instructionBound,poly_EnumeratedPacking_instructionBound]
  simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
  gcongr <;> aesop (add safe [Nat.add_le_add, Nat.mul_le_mul, Nat.pow_le_pow_left, bound_RowVertices_instructionBound, bound_PreparedPacking_instructionBound])

end DirectedFlowCutGap.SourcePackingPolynomial
