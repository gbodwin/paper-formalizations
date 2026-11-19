import DirectedFlowCutGap.PhysicalOriginalInputSolvers
import DirectedFlowCutGap.PhysicalEdgeCostEnvelope

/-! Bound parsing and the recorded solver phases from the actual supplied
source length, including accepted encodings with padded rational fields. -/

namespace DirectedFlowCutGap.PhysicalWireCostEnvelope

open BinaryArithmetic BinaryRational Polynomial
open PhysicalIntegerRoundingCost (eval_mono)

private theorem prepareOn_some {A B : ℕ → Type} (init : (n : ℕ) → A n → Option (B n))
    {parsed : Option (Σ n, A n)} {n : ℕ} {r : B n}
    (h : PhysicalVertexSolver.prepareOn init parsed=some ⟨n,r⟩) :
    ∃ input : A n, parsed=some ⟨n,input⟩ ∧ init n input=some r := by
  obtain ⟨⟨m,input⟩,source,run⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨out,actual,eq⟩ := Option.map_eq_some_iff.mp run
  cases eq
  exact ⟨input,source,actual⟩

private theorem rowBits_le {x : ℕ} (qs : List Fraction) (fits : ∀ q ∈ qs, StoredBounded q x) :
    LambdaRowProgram.rowBits qs ≤ qs.length*(x+x) := by
  induction qs with
  | nil => simp [LambdaRowProgram.rowBits]
  | cons q qs ih =>
    have widths := fits q List.mem_cons_self
    have a := widths.1
    have b := widths.2
    have more := ih (fun r hr => fits r (List.mem_cons_of_mem _ hr))
    simp only [LambdaRowProgram.rowBits,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem vertex_wire_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits)
    {n : ℕ} {r : PhysicalAmplifiedVertexSolver.Result n},
    (PhysicalOriginalInputSolvers.vertexWithCost κ mode source tape).1=some ⟨n,r⟩ →
      (PhysicalOriginalInputSolvers.vertexWithCost κ mode source tape).2+r.dispatch+r.readback+r.roundingAndSelection ≤
        p.eval (source.length+κ) := by
  obtain ⟨p,hp⟩ := PhysicalSolverCostEnvelope.vertex_polynomial
  let pad : Polynomial ℕ := X+X+1+C 2*X^2+X
  refine ⟨ChargedSourceAssembly.parsePolynomial+p.comp pad,?_⟩
  intro κ mode source tape n r actual
  let x := source.length+κ
  obtain ⟨D,decoded,run⟩ := prepareOn_some
    (fun _ input => PhysicalAmplifiedVertexSolver.vertex κ mode input tape) actual
  obtain ⟨size,demands,fields⟩ := ChargedSourceAssembly.vertex_dimensions decoded
  have width := rowBits_le D.costs.toList fields
  rw [Vector.length_toList] at width
  have hS : source.length ≤ x := Nat.le_add_right _ _
  have conf : κ ≤ x := Nat.le_add_left _ _
  have padded : PhysicalSolverCostEnvelope.vertexSize D κ ≤ pad.eval x := by
    simp only [pad,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one,
      PhysicalSolverCostEnvelope.vertexSize,ChargedVertexModes.priceWidth]
    have hn := size.trans hS
    have w := width.trans (show n*(source.length+source.length) ≤ x*(x+x) by gcongr)
    nlinarith [size.trans hS,demands.trans hS]
  have work := (hp κ mode D tape run).trans (eval_mono p padded)
  have parse := (ChargedSourceAssembly.vertex_paid source).trans_eq (ChargedSourceAssembly.parsePolynomial_eval _).symm
  have setup := parse.trans (eval_mono ChargedSourceAssembly.parsePolynomial hS)
  rw [eval_add,eval_comp]
  change (ChargedSourceAssembly.vertex source).2+r.dispatch+r.readback+r.roundingAndSelection ≤
    ChargedSourceAssembly.parsePolynomial.eval x+p.eval (pad.eval x)
  omega

theorem edge_wire_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits)
    {n : ℕ} {r : PhysicalAmplifiedEdgeSolver.EdgeResult n},
    (PhysicalOriginalInputSolvers.edgeWithCost κ mode source tape).1=some ⟨n,r⟩ →
      (PhysicalOriginalInputSolvers.edgeWithCost κ mode source tape).2+r.dispatch+r.readback+r.roundingAndSelection ≤
        p.eval (source.length+κ) := by
  obtain ⟨p,hp⟩ := PhysicalEdgeCostEnvelope.edge_polynomial
  let pad : Polynomial ℕ := C 3*X+1+X
  refine ⟨ChargedSourceAssembly.parsePolynomial+p.comp pad,?_⟩
  intro κ mode source tape n r actual
  let x := source.length+κ
  obtain ⟨D,decoded,run⟩ := prepareOn_some
    (fun _ input => PhysicalAmplifiedEdgeSolver.run κ (EncodedEdgeInput.decodeInput input) mode tape) actual
  obtain ⟨size,demands,fields⟩ := ChargedSourceAssembly.edge_dimensions decoded
  let G := EncodedEdgeInput.decodeInput D
  have widths (u v : Fin n) : G.costs[u.val][v.val].num.size ≤ source.length+1 ∧
      G.costs[u.val][v.val].den.size ≤ source.length+1 := by
    let i := finProdFinEquiv (u,v)
    let q := BinaryFractionalRows.get D.costs i
    have member : q ∈ D.costs.toList := by
      change D.costs[i.val] ∈ D.costs.toList
      have hi : i.val<D.costs.toList.length := by simp only [Vector.length_toList,i.isLt]
      simpa only [Vector.getElem_toList] using List.getElem_mem hi
    obtain ⟨a,b⟩ := fields q member
    simp only [G,EncodedEdgeInput.decodeInput,Vector.getElem_ofFn,BinaryFractionalRows.decode_get]
    change (value q.num).size ≤ _ ∧ (value q.den).size ≤ _
    exact ⟨(Nat.size_le.mpr (value_lt q.num)).trans (by omega),
      (Nat.size_le.mpr (value_lt q.den)).trans (by omega)⟩
  have hS : source.length ≤ x := Nat.le_add_right _ _
  have conf : κ ≤ x := Nat.le_add_left _ _
  have padded : n+G.demands.length+(source.length+1)+κ ≤ pad.eval x := by
    change n+D.demands.length+(source.length+1)+κ ≤ _
    simp only [pad,eval_add,eval_mul,eval_C,eval_X,eval_one]
    omega
  have work := (hp κ G mode tape (Nat.le_add_left _ _) widths run).trans (eval_mono p padded)
  have parse := (ChargedSourceAssembly.edge_paid source).trans_eq (ChargedSourceAssembly.parsePolynomial_eval _).symm
  have setup := parse.trans (eval_mono ChargedSourceAssembly.parsePolynomial hS)
  rw [eval_add,eval_comp]
  change (ChargedSourceAssembly.edge source).2+r.dispatch+r.readback+r.roundingAndSelection ≤
    ChargedSourceAssembly.parsePolynomial.eval x+p.eval (pad.eval x)
  omega

end DirectedFlowCutGap.PhysicalWireCostEnvelope
