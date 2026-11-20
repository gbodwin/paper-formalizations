import DirectedFlowCutGap.BinaryWeakDecomposition
import DirectedFlowCutGap.ChargedSourceAssembly
import DirectedFlowCutGap.PhysicalIntegerRoundingCost

/-! The weak-cut wire has a rational weight matrix and an adjacency
matrix. Its third table is empty because the solver computes the demands. -/
namespace DirectedFlowCutGap.PhysicalWeakCutWire

open BinaryArithmetic Polynomial
open PhysicalIntegerRoundingCost (eval_mono)
open BinaryWeakDecomposition (Result)

def weights {n : ℕ} (D : EncodedEdgeInput.Input n) : RationalEdgeThresholds.Weights n :=
  Vector.ofFn fun i => Vector.ofFn fun j => D.costs[(finProdFinEquiv (i,j)).val]

private def wireInput {n : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : EncodedEdgeInput.Input n :=
  ⟨adj,[],Vector.ofFn fun k =>
    let (i,j) := finProdFinEquiv.symm k
    w[i.val][j.val]⟩

theorem weights_wire {n : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : weights (wireInput adj w)=w := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let a : Fin n := ⟨i,hi⟩
  let b : Fin n := ⟨j,hj⟩
  simp only [weights,Vector.getElem_ofFn,wireInput]
  change w[(finProdFinEquiv.symm (finProdFinEquiv (a,b))).1.val][(finProdFinEquiv.symm (finProdFinEquiv (a,b))).2.val]=w[a.val][b.val]
  exact congrArg (fun p : Fin n × Fin n => w[p.1.val][p.2.val]) (Equiv.symm_apply_apply _ _)

def encode {n : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n) : Bits :=
  EncodedEdgeInput.encode (wireInput adj w)

private def weightsWithCost {n : ℕ} (D : EncodedEdgeInput.Input n) : RationalEdgeThresholds.Weights n × ℕ :=
  BinaryEdgeProjection.matrix fun i => (D.costs[i.val],4)

private theorem weightsWithCost_value {n : ℕ} (D : EncodedEdgeInput.Input n) :
    (weightsWithCost D).1=weights D := by
  simp only [weightsWithCost,BinaryEdgeProjection.matrix_value,weights]

private theorem weightsWithCost_paid {n : ℕ} (D : EncodedEdgeInput.Input n) :
    (weightsWithCost D).2 ≤ BinaryEdgeProjection.readbackBudget n 4 := by
  exact BinaryEdgeProjection.matrix_paid (fun i => (D.costs[i.val],4)) (fun _ => le_rfl)

private def runOn (k M κ : ℕ) (tape : Bits) :
    (Σ n,EncodedEdgeInput.Input n) → PhysicalCoverAccess.Read (Σ n,Result n)
  | ⟨n,D⟩ =>
    if D.demands.isEmpty then
      let data := weightsWithCost D
      ((BinaryWeakDecomposition.run k M κ D.adjacency data.1 tape).map (fun r => ⟨n,r⟩),data.2)
    else (none,2)

def run (k M κ : ℕ) (source tape : Bits) : PhysicalCoverAccess.Read (Σ n,Result n) :=
  let parsed := ChargedSourceAssembly.edge source
  let loaded := parsed.1.map (runOn k M κ tape)
  (loaded.bind Prod.fst,parsed.2+(loaded.map Prod.snd).getD 0+4)

theorem run_encode {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (tape : Bits) :
    (run k M κ (encode adj w) tape).1 =
      (BinaryWeakDecomposition.run k M κ adj w tape).map (fun out => ⟨n,out⟩) := by
  simp only [run,ChargedSourceAssembly.edge_value,encode,EncodedEdgeInput.parse_encode,Option.map_some,Option.bind_some]
  have row : (wireInput adj w).demands=[] := rfl
  simp only [runOn,row,List.isEmpty_nil,ite_true,weightsWithCost_value,weights_wire]
  rfl

private theorem entry_mem {n : ℕ} (D : EncodedEdgeInput.Input n) (i : Fin (n*n)) :
    D.costs[i.val] ∈ D.costs.toList := by
  have hi : i.val < D.costs.toList.length := by simp only [Vector.length_toList,i.isLt]
  simpa only [Vector.getElem_toList] using List.getElem_mem hi

theorem weights_fit {n : ℕ} {D : EncodedEdgeInput.Input n} {source : Bits}
    (parsed : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩) :
    AdaptiveWidthEnvelope.StoredWeights (weights D) source.length := by
  obtain ⟨_,_,fields⟩ := ChargedSourceAssembly.edge_dimensions parsed
  intro a b
  simp only [weights,Vector.getElem_ofFn]
  exact fields _ (entry_mem D (finProdFinEquiv (a,b)))

theorem wire_complete {n k M : ℕ} (hn : 0<n) (hk : 0<k) (hM : 0<M) (κ : ℕ)
    {D : EncodedEdgeInput.Input n} (source tape : Bits)
    (parsed : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩) (demands : D.demands=[])
    (enough : BinaryWeakDecomposition.tapeBound n source.length M κ ≤ tape.length) :
    ∃ out used, (run k M κ source tape).1=some ⟨n,out⟩ ∧ out.suffix=tape.drop used ∧
      used≤BinaryWeakDecomposition.tapeBound n source.length M κ := by
  have within := BinaryWeakDecomposition.tree_polynomial_reads hn hk M κ hM D.adjacency (weights D)
    (weights_fit parsed)
  obtain ⟨out,used,selected,suffix,reads⟩ := BinaryWeakDecomposition.complete k M κ D.adjacency
    (weights D) tape within enough
  refine ⟨out,used,?_,suffix,reads⟩
  simp only [run,parsed,Option.bind_some,runOn,demands,List.isEmpty_nil,ite_true,weightsWithCost_value,
    selected,Option.map_some]

attribute [local irreducible] BinaryWeakDecomposition.run

theorem wire_polynomial {k : ℕ} (hk : 0<k) (M : ℕ) (hM : 0<M) :
    ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (source tape : Bits) {n : ℕ}, 0<n →
      ∀ {r : Result n}, (run k M κ source tape).1=some ⟨n,r⟩ →
        (run k M κ source tape).2+r.familyPaid+r.samplePaid ≤ p.eval (source.length+κ) := by
  obtain ⟨p,pay⟩ := BinaryWeakDecomposition.run_polynomial hk M hM
  let pad : Polynomial ℕ := 2*X
  let matrix := BinaryEdgeProjection.readbackBudget (X : Polynomial ℕ) 4
  refine ⟨ChargedSourceAssembly.parsePolynomial+matrix+4+p.comp pad,?_⟩
  intro κ source tape n hn r ran
  let read := ChargedSourceAssembly.edge source
  change (read.1.map (runOn k M κ tape)).bind Prod.fst=some ⟨n,r⟩ at ran
  obtain ⟨wrapped,shaped,success⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨⟨m,D⟩,found,rfl⟩ := Option.map_eq_some_iff.mp shaped
  let wrap (out : Result m) : Σ n,Result n := ⟨m,out⟩
  by_cases h : D.demands.isEmpty=true
  · simp only [runOn,h,ite_true,weightsWithCost_value] at success
    change (BinaryWeakDecomposition.run k M κ D.adjacency (weights D) tape).map wrap=some ⟨n,r⟩ at success
    obtain ⟨out,actual,equal⟩ := Option.map_eq_some_iff.mp success
    dsimp only [wrap] at equal
    cases equal
    obtain ⟨dim,_,_⟩ := ChargedSourceAssembly.edge_dimensions found
    have fit := weights_fit found
    let x := source.length+κ
    have xS : source.length ≤ x := Nat.le_add_right _ _
    have nx : n≤x := dim.trans xS
    have input : n+source.length+κ ≤ pad.eval x := by
      simp only [pad,eval_mul,eval_X,eval_ofNat]
      unfold x at nx ⊢
      omega
    have work := (pay hn κ D.adjacency (weights D) fit tape actual).trans (eval_mono p input)
    have frame := ((ChargedSourceAssembly.edge_paid source).trans_eq (ChargedSourceAssembly.parsePolynomial_eval _).symm).trans
      (eval_mono ChargedSourceAssembly.parsePolynomial xS)
    change read.2 ≤ ChargedSourceAssembly.parsePolynomial.eval x at frame
    have eval : matrix.eval x=BinaryEdgeProjection.readbackBudget x 4 := by
      simp only [matrix,BinaryEdgeProjection.readbackBudget,eval_add,eval_mul,eval_pow,eval_ofNat,eval_X]
    have shape := (weightsWithCost_paid D).trans
      (show BinaryEdgeProjection.readbackBudget n 4 ≤ BinaryEdgeProjection.readbackBudget x 4 from by
        unfold BinaryEdgeProjection.readbackBudget
        gcongr)
    rw [eval_add,eval_add,eval_add,eval_comp,eval,eval_ofNat]
    change read.2+((read.1.map (runOn k M κ tape)).map Prod.snd).getD 0+4+r.familyPaid+r.samplePaid ≤ _
    simp only [found,Option.map_some,Option.getD_some,runOn,h,ite_true]
    change read.2+(weightsWithCost D).2+4+r.familyPaid+r.samplePaid ≤
      ChargedSourceAssembly.parsePolynomial.eval x+BinaryEdgeProjection.readbackBudget x 4+4+
        p.eval (pad.eval x)
    omega
  · simp [runOn,h] at success

end DirectedFlowCutGap.PhysicalWeakCutWire
