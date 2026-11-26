import OnlineReachabilityPreservers.SteinerBinaryReplayResultWork
import OnlineReachabilityPreservers.SteinerIntegerBounds
import Lean.Elab.Tactic

/-! Polynomial growth of the recorded replay bound at fixed forest height. -/

namespace OnlineReachabilityPreservers

private structure ReplaySize where
  vertices : ℕ
  arcs : ℕ
  rawLength : ℕ
  demands : ℕ

private def ReplaySize.total (s : ReplaySize) : ℕ := s.vertices+s.arcs+s.rawLength+s.demands+1

private def ReplayPolynomialBound (f : ReplaySize → ℕ) : Prop :=
  ∃ C k : ℕ, ∀ s, f s ≤ C*s.total^k

private theorem replayPolynomial_constant (c : ℕ) : ReplayPolynomialBound (fun _ => c) :=
  ⟨c,0,by simp⟩

private theorem replayPolynomial_vertices : ReplayPolynomialBound ReplaySize.vertices :=
  ⟨1,1,fun s => by simp only [pow_one,Nat.one_mul,ReplaySize.total]; omega⟩

private theorem replayPolynomial_arcs : ReplayPolynomialBound ReplaySize.arcs :=
  ⟨1,1,fun s => by simp only [pow_one,Nat.one_mul,ReplaySize.total]; omega⟩

private theorem replayPolynomial_raw : ReplayPolynomialBound ReplaySize.rawLength :=
  ⟨1,1,fun s => by simp only [pow_one,Nat.one_mul,ReplaySize.total]; omega⟩

private theorem replayPolynomial_demands : ReplayPolynomialBound ReplaySize.demands :=
  ⟨1,1,fun s => by simp only [pow_one,Nat.one_mul,ReplaySize.total]; omega⟩

private theorem replayPolynomial_mono (f g : ReplaySize → ℕ) (le : ∀ s, f s ≤ g s)
    (bound : ReplayPolynomialBound g) : ReplayPolynomialBound f := by
  obtain ⟨C,k,sizes⟩ := bound
  exact ⟨C,k,fun s => (le s).trans (sizes s)⟩

private theorem replayPolynomial_add (f g : ReplaySize → ℕ) (left : ReplayPolynomialBound f)
    (right : ReplayPolynomialBound g) : ReplayPolynomialBound (fun s => f s+g s) := by
  obtain ⟨A,i,first⟩ := left
  obtain ⟨B,j,second⟩ := right
  refine ⟨A+B,i+j,fun s => ?_⟩
  have positive : 0 < s.total := by unfold ReplaySize.total; omega
  have degreeLeft := Nat.pow_le_pow_right positive (Nat.le_add_right i j)
  have degreeRight := Nat.pow_le_pow_right positive (Nat.le_add_left j i)
  rw [Nat.add_mul]
  exact Nat.add_le_add ((first s).trans (Nat.mul_le_mul_left A degreeLeft))
    ((second s).trans (Nat.mul_le_mul_left B degreeRight))

private theorem replayPolynomial_mul (f g : ReplaySize → ℕ) (left : ReplayPolynomialBound f)
    (right : ReplayPolynomialBound g) : ReplayPolynomialBound (fun s => f s*g s) := by
  obtain ⟨A,i,first⟩ := left
  obtain ⟨B,j,second⟩ := right
  refine ⟨A*B,i+j,fun s => (Nat.mul_le_mul (first s) (second s)).trans_eq ?_⟩
  rw [pow_add]
  ac_rfl

private theorem replayPolynomial_pow (f : ReplaySize → ℕ) (j : ℕ) (bound : ReplayPolynomialBound f) :
    ReplayPolynomialBound (fun s => f s^j) := by
  obtain ⟨A,i,first⟩ := bound
  refine ⟨A^j,i*j,fun s => (Nat.pow_le_pow_left (first s) j).trans_eq ?_⟩
  rw [pow_mul,mul_pow]

private theorem replayPolynomial_max (f g : ReplaySize → ℕ) (left : ReplayPolynomialBound f)
    (right : ReplayPolynomialBound g) : ReplayPolynomialBound (fun s => max (f s) (g s)) :=
  replayPolynomial_mono _ _ (fun _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
    (replayPolynomial_add f g left right)

private theorem replayPolynomial_min (f g : ReplaySize → ℕ) (bound : ReplayPolynomialBound f) :
    ReplayPolynomialBound (fun s => min (f s) (g s)) :=
  replayPolynomial_mono _ _ (fun _ => min_le_left _ _) bound

private theorem replayPolynomial_sub (f g : ReplaySize → ℕ) (bound : ReplayPolynomialBound f) :
    ReplayPolynomialBound (fun s => f s-g s) :=
  replayPolynomial_mono _ _ (fun _ => Nat.sub_le _ _) bound

private theorem replayPolynomial_div (f g : ReplaySize → ℕ) (bound : ReplayPolynomialBound f) :
    ReplayPolynomialBound (fun s => f s/g s) :=
  replayPolynomial_mono _ _ (fun _ => Nat.div_le_self _ _) bound

private theorem replayPolynomial_log (f : ReplaySize → ℕ) (bound : ReplayPolynomialBound f) :
    ReplayPolynomialBound (fun s => (f s).log2) :=
  replayPolynomial_mono _ _ (fun _ => Nat.log2_le_self _) bound

private theorem replayPolynomial_size (f : ReplaySize → ℕ) (bound : ReplayPolynomialBound f) :
    ReplayPolynomialBound (fun s => (f s).size) :=
  replayPolynomial_mono _ _ (fun _ => Nat.size_le.mpr Nat.lt_two_pow_self) bound

private theorem replayPolynomial_thinThreshold (f : ReplaySize → ℕ) (bound : ReplayPolynomialBound f) :
    ReplayPolynomialBound (fun s => steinerThinThreshold (f s)) :=
  replayPolynomial_mono _ _ (fun _ => steinerThinThreshold_le_vertices _) bound

open Lean Meta Elab Tactic in
/-- Compose the ordinary arithmetic bounds after unfolding each work allowance. -/
private partial def proveReplayPolynomial (s term : Expr) : StateT (Std.HashMap Expr Expr) MetaM Expr := do
  let term ← zetaReduce term
  if let some proof := (← get).get? term then return proof
  let recurse (op : Name) (arity : ℕ) : StateT (Std.HashMap Expr Expr) MetaM Expr := do
    let args := term.getAppArgs
    let left := args[args.size-2]!
    let right := args.back!
    let leftFn ← mkLambdaFVars #[s] left
    let rightFn ← mkLambdaFVars #[s] right
    let first ← proveReplayPolynomial s left
    if arity = 1 then return ← mkAppM op #[leftFn,rightFn,first]
    let second ← proveReplayPolynomial s right
    mkAppM op #[leftFn,rightFn,first,second]
  let unary (op : Name) : StateT (Std.HashMap Expr Expr) MetaM Expr := do
    let arg := term.getAppArgs.back!
    let inner ← mkLambdaFVars #[s] arg
    let bounded ← proveReplayPolynomial s arg
    mkAppM op #[inner,bounded]
  let proof ← if !term.containsFVar s.fvarId! then
    mkAppM ``replayPolynomial_constant #[term]
  else match term.getAppFn.constName? with
    | some ``ReplaySize.vertices => pure (mkConst ``replayPolynomial_vertices)
    | some ``ReplaySize.arcs => pure (mkConst ``replayPolynomial_arcs)
    | some ``ReplaySize.rawLength => pure (mkConst ``replayPolynomial_raw)
    | some ``ReplaySize.demands => pure (mkConst ``replayPolynomial_demands)
    | some ``HAdd.hAdd | some ``Nat.add => recurse ``replayPolynomial_add 2
    | some ``HMul.hMul | some ``Nat.mul => recurse ``replayPolynomial_mul 2
    | some ``Max.max => recurse ``replayPolynomial_max 2
    | some ``Min.min => recurse ``replayPolynomial_min 1
    | some ``HSub.hSub | some ``Nat.sub => recurse ``replayPolynomial_sub 1
    | some ``HDiv.hDiv | some ``Nat.div => recurse ``replayPolynomial_div 1
    | some ``Nat.log2 => unary ``replayPolynomial_log
    | some ``Nat.size => unary ``replayPolynomial_size
    | some ``steinerThinThreshold => unary ``replayPolynomial_thinThreshold
    | some ``HPow.hPow | some ``Nat.pow => do
      let args := term.getAppArgs
      let base := args[args.size-2]!
      let degree := args.back!
      if degree.containsFVar s.fvarId! then
        throwError "Expected a fixed exponent, reached {term}"
      mkAppM ``replayPolynomial_pow #[← mkLambdaFVars #[s] base,degree,← proveReplayPolynomial s base]
    | _ => do
      if let some body ← unfoldDefinition? term true then
        proveReplayPolynomial s body
      else
        throwError "No polynomial work rule for {term}"
  modify fun memo => memo.insert term proof
  return proof

open Lean Meta Elab Tactic in
local elab "bound_replay_polynomial" : tactic => liftMetaTactic fun goal => goal.withContext do
  let target ← goal.getType
  unless target.isAppOf ``ReplayPolynomialBound do
    throwError "Expected a replay polynomial bound"
  withLocalDeclD `s (mkConst ``ReplaySize) fun s => do
    let (proof,_) ← (proveReplayPolynomial s (mkApp target.appArg! s).headBeta).run {}
    goal.assign proof
  return []

set_option maxHeartbeats 3000000 in
/-- At every fixed height, the complete recorded work bound grows at most
polynomially in the sum of the input graph and trace sizes. -/
theorem finSteinerBinaryPhasesReplaySizeBudget_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ n m raw p,
      finSteinerBinaryPhasesReplaySizeBudget n m raw height p ≤ C*(n+m+raw+p+1)^k := by
  have bound : ReplayPolynomialBound (fun s =>
    finSteinerBinaryPhasesReplaySizeBudget s.vertices s.arcs s.rawLength height s.demands) := by
    bound_replay_polynomial
  obtain ⟨C,k,work⟩ := bound
  exact ⟨C,k,fun n m raw p => work ⟨n,m,raw,p⟩⟩

set_option maxHeartbeats 3000000 in
/-- One fixed-height polynomial bounds the recorded work together with
the supply of independent fair bits used for the replay. -/
theorem completeFinSteinerReplayWithBinaryPhasesWork_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
      (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)),
      (∀ d ∈ D, Reach G d.1 d.2) →
      let out := completeFinSteinerReplayWithBinaryPhasesWork G raw same height G.card rfl bits D
      let base := out.1.1.1
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1+
        steinerBitBudget G height ≤ C*(n+G.card+raw.length+D.length+1)^k := by
  have bound : ReplayPolynomialBound (fun s =>
    finSteinerBinaryPhasesReplaySizeBudget s.vertices s.arcs s.rawLength height s.demands+
      completeSteinerSeedPolynomial s.vertices s.arcs height*s.arcs) := by
    bound_replay_polynomial
  obtain ⟨C,k,work⟩ := bound
  refine ⟨C,k,?_⟩
  intro n G raw same bits D feasible
  have tally := (completeFinSteinerReplayWithBinaryPhasesWork_input_sizes G raw same height G.card rfl bits D feasible).2.2
  have supplied := steinerBitBudget_polynomial G height
  simp only [Fintype.card_fin] at supplied
  exact (Nat.add_le_add tally supplied).trans (work ⟨n,G.card,raw.length,D.length⟩)

set_option maxHeartbeats 3000000 in
/-- The metered final result and its prescribed fair-bit supply obey a
polynomial bound at any fixed forest height. -/
theorem finSteinerBinaryFinalGraphWithWork_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
      (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)),
      (∀ d ∈ D, Reach G d.1 d.2) →
      (finSteinerBinaryFinalGraphWithWork G raw same height bits D).2+steinerBitBudget G height ≤
        C*(n+G.card+raw.length+D.length+1)^k := by
  have bound : ReplayPolynomialBound (fun s =>
    finSteinerBinaryFinalGraphWorkBudget s.vertices s.arcs s.rawLength height s.demands+
      completeSteinerSeedPolynomial s.vertices s.arcs height*s.arcs) := by
    bound_replay_polynomial
  obtain ⟨C,k,work⟩ := bound
  refine ⟨C,k,?_⟩
  intro n G raw same bits D feasible
  have tally := (finSteinerBinaryFinalGraphWithWork_spec G raw same height bits D feasible).2
  have supplied := steinerBitBudget_polynomial G height
  simp only [Fintype.card_fin] at supplied
  exact (Nat.add_le_add tally supplied).trans (work ⟨n,G.card,raw.length,D.length⟩)

/-- Include computing the exact seed length and building its stored bit
array. The graph-size polynomial bounds the length before it is computed. -/
def finSteinerSeedInitializationWorkBudget (n m raw height : ℕ) : ℕ :=
  finSteinerBitBudgetWorkBound n m raw height + 6*(completeSteinerSeedPolynomial n m height*m)+11

set_option maxHeartbeats 3000000 in
theorem finSteinerSeedInitializationWorkBudget_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ n m raw p,
      finSteinerSeedInitializationWorkBudget n m raw height ≤ C*(n+m+raw+p+1)^k := by
  have bound : ReplayPolynomialBound (fun s =>
    finSteinerSeedInitializationWorkBudget s.vertices s.arcs s.rawLength height) := by
    bound_replay_polynomial
  obtain ⟨C,k,work⟩ := bound
  exact ⟨C,k,fun n m raw p => work ⟨n,m,raw,p⟩⟩

end OnlineReachabilityPreservers
