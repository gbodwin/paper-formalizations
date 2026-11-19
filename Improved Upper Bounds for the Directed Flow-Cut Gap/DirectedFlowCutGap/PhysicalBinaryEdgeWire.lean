import DirectedFlowCutGap.PhysicalBinaryEdgeCost

/-! Join the counted binary edge solver to the literal input parser and its
stored rational fields. The source-size bound permits zero padding. -/

namespace DirectedFlowCutGap.PhysicalBinaryEdgeWire

open BinaryArithmetic BinaryRational FiniteDrawTrees Polynomial
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)
open PhysicalAmplifiedEdgeSolver (EdgeResult model)
open PhysicalIntegerRoundingCost (eval_mono)

def decodeBudget {R : Type*} [Semiring R] (n b : R) : R :=
  n^2*(40*(b+1)^2)+8*n^2+4+64*(n+1)^4

def decodeWithCost {n : ℕ} (D : EncodedEdgeInput.Input n) : EncodedEdgeLineInput.Input n × ℕ :=
  let prices := batch fun i => BinaryRawRational.decode (BinaryFractionalRows.get D.costs i)
  (⟨D.adjacency,D.demands,Vector.ofFn fun s => Vector.ofFn fun t => prices.1[(finProdFinEquiv (s,t)).val]⟩,
    prices.2+64*(n+1)^4)

@[simp] theorem decode_value {n : ℕ} (D : EncodedEdgeInput.Input n) : (decodeWithCost D).1=EncodedEdgeInput.decodeInput D := by
  simp only [decodeWithCost,EncodedEdgeInput.decodeInput,batch_value,BinaryRawRational.decode_value,
    BinaryFractionalRows.decode_get,Vector.getElem_ofFn]

theorem decode_paid {n b : ℕ} (D : EncodedEdgeInput.Input n)
    (fits : ∀ i, StoredBounded (BinaryFractionalRows.get D.costs i) b) :
    (decodeWithCost D).2 ≤ decodeBudget n b := by
  unfold decodeBudget decodeWithCost
  dsimp only
  rw [pow_two n]
  exact Nat.add_le_add_right (batch_paid _ fun i => BinaryRawRational.decode_paid (fits i)) _

def runOn {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n) (tape : Bits) :
    Option (EdgeResult n) :=
  let source := decodeWithCost D
  (PhysicalAmplifiedBinaryEdge.run κ source.1 mode tape).map
    (fun r => { r with roundingAndSelection := r.roundingAndSelection+source.2 })

theorem runOn_observe {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n) (tape : Bits) :
    (runOn κ mode D tape).map EdgeResult.observe =
      (EncodedSolverBits.run (EncodedEdgeSolver.bitTree κ (EncodedEdgeInput.decodeInput D) (model mode)) tape).map
        (fun (out,(rest,_)) => (out,rest)) := by
  simp only [runOn,Option.map_map,Function.comp_def,EdgeResult.observe,decode_value]
  exact PhysicalAmplifiedBinaryEdge.run_observe κ (EncodedEdgeInput.decodeInput D) mode tape

def edgeWithCost (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    PhysicalCoverAccess.Read (Σ n,EdgeResult n) :=
  let parsed := ChargedSourceAssembly.edge source
  (PhysicalVertexSolver.prepareOn (fun _ input => runOn κ mode input tape) parsed.1,parsed.2)

theorem edge_complete {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (source tape : Bits) (parsed : EncodedEdgeInput.parse source=some ⟨n,D⟩)
    (enough : EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length) :
    ∃ r used, (edgeWithCost κ mode source tape).1=some ⟨n,r⟩ ∧ r.suffix=tape.drop used ∧
      used ≤ EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
      EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) r.output := by
  let G := EncodedEdgeInput.decodeInput D
  let tree := EncodedEdgeSolver.bitTree κ G (model mode)
  have legal : ∀ a ∈ (ideal tree).support, EncodedEdgeSolver.Valid G a := by
    cases mode
    · exact fun _ h => EncodedEdgeSolver.mass_support_valid _ _ h
    · exact fun _ h => EncodedEdgeSolver.size_support_valid _ _ h
  have within : Within (EncodedSolverBits.edgeBudget κ G) tree := by
    cases mode
    · exact EncodedSolverBits.edge_mass_within κ G
    · exact EncodedSolverBits.edge_size_within κ G
  obtain ⟨r,k,actual,rest,used,valid⟩ := PhysicalOriginalInputCompleteness.returns
    EdgeResult.output EdgeResult.suffix (runOn κ mode D tape) (EncodedEdgeSolver.Valid G)
    (runOn_observe κ mode D tape) legal within (EncodedEdgeSolver.bitTree_binary ..) enough
  have trace : (edgeWithCost κ mode source tape).1=some ⟨n,r⟩ := by
    simp only [edgeWithCost,ChargedSourceAssembly.edge_value]
    exact PhysicalVertexSolver.prepareOn_eq (fun _ input => runOn κ mode input tape) parsed actual
  exact ⟨r,k,trace,rest,used,valid⟩

private theorem stored_member {m : ℕ} (row : BinaryFractionalRows.Row m) (i : Fin m) :
    BinaryFractionalRows.get row i ∈ row.toList := by
  change row[i.val] ∈ row.toList
  have hi : i.val < row.toList.length := by simp only [Vector.length_toList,i.isLt]
  simpa only [Vector.getElem_toList] using List.getElem_mem hi

attribute [local irreducible] PhysicalSourceReadback.run PhysicalSourceReadback.planBound

theorem edge_wire_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits)
    {n : ℕ} {r : EdgeResult n}, (edgeWithCost κ mode source tape).1=some ⟨n,r⟩ →
      (edgeWithCost κ mode source tape).2+r.dispatch+r.readback+r.roundingAndSelection ≤ p.eval (source.length+κ) := by
  obtain ⟨p,hp⟩ := PhysicalBinaryEdgeCost.edge_polynomial
  let pad : Polynomial ℕ := 3*X+1
  refine ⟨ChargedSourceAssembly.parsePolynomial+decodeBudget X X+p.comp pad,?_⟩
  intro κ mode source tape n r run
  let x := source.length+κ
  let parsed := ChargedSourceAssembly.edge source
  obtain ⟨⟨m,D⟩,found,tail⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨out,executed,same⟩ := Option.map_eq_some_iff.mp tail
  cases same
  obtain ⟨size,demands,fields⟩ := ChargedSourceAssembly.edge_dimensions found
  let G := (decodeWithCost D).1
  have fits (i : Fin (n*n)) : StoredBounded (BinaryFractionalRows.get D.costs i) source.length :=
    fields _ (stored_member _ _)
  have widths (u v : Fin n) :
      G.costs[u.val][v.val].num.size ≤ source.length+1 ∧ G.costs[u.val][v.val].den.size ≤ source.length+1 := by
    let i := finProdFinEquiv (u,v)
    let q := BinaryFractionalRows.get D.costs i
    obtain ⟨a,b⟩ := fits i
    simp only [G,decode_value,EncodedEdgeInput.decodeInput,Vector.getElem_ofFn,BinaryFractionalRows.decode_get]
    change (value q.num).size ≤ _ ∧ (value q.den).size ≤ _
    exact ⟨((Nat.size_le.mpr (value_lt q.num)).trans a).trans (Nat.le_succ _),
      ((Nat.size_le.mpr (value_lt q.den)).trans b).trans (Nat.le_succ _)⟩
  obtain ⟨base,call,rfl⟩ := Option.map_eq_some_iff.mp executed
  have hS : source.length ≤ x := Nat.le_add_right _ _
  have hn := size.trans hS
  have inside : n+G.demands.length+(source.length+1)+κ ≤ pad.eval x := by
    change n+D.demands.length+(source.length+1)+κ ≤ _
    simp only [pad,eval_mul,eval_add,eval_ofNat,eval_X,eval_one]
    omega
  have work := (hp κ G mode tape (Nat.le_add_left _ _) widths call).trans (eval_mono p inside)
  have parse := (ChargedSourceAssembly.edge_paid source).trans_eq (ChargedSourceAssembly.parsePolynomial_eval _).symm
  have framing := parse.trans (eval_mono ChargedSourceAssembly.parsePolynomial hS)
  change parsed.2 ≤ _ at framing
  have stored := decode_paid D fits
  have load : decodeBudget n source.length ≤ (decodeBudget (X : Polynomial ℕ) X).eval x := by
    simp only [decodeBudget,eval_add,eval_mul,eval_ofNat,eval_pow,eval_one,eval_X]
    gcongr
  have copying := stored.trans load
  simp only [eval_add,eval_comp]
  change parsed.2+base.dispatch+base.readback+(base.roundingAndSelection+(decodeWithCost D).2) ≤
    ChargedSourceAssembly.parsePolynomial.eval x+(decodeBudget (X : Polynomial ℕ) X).eval x+p.eval (pad.eval x)
  omega

end DirectedFlowCutGap.PhysicalBinaryEdgeWire
