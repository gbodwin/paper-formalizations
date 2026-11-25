import DirectedFlowCutGap.ChargedSourceAssembly
import DirectedFlowCutGap.MeasuredBudgetRescaleEdgeFamily

namespace DirectedFlowCutGap.MeasuredRescaleWire

open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open RationalEdgeThresholds (Weights)
open MeasuredBudgetRescaleEdgeFamily (Preparation Draw prepare prepareBudget drawPrepared)

private def lengthMatrix {n : ℕ} (D : EncodedEdgeInput.Input n) : Weights n :=
  Vector.ofFn fun s => Vector.ofFn fun t => D.costs[(finProdFinEquiv (s,t)).val]

private def frame {n : ℕ} (A : Adjacency n) (w : Weights n) : EncodedEdgeInput.Input n :=
  ⟨A, [], Vector.ofFn fun i =>
    let e := finProdFinEquiv.symm i
    w[e.1.val][e.2.val]⟩

private theorem lengthMatrix_frame {n : ℕ} (A : Adjacency n) (w : Weights n) :
    lengthMatrix (frame A w) = w := by
  ext s hs t ht
  simp only [lengthMatrix,frame,Vector.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]

/-- The weak-decomposition sampler derives its demands from the lengths.
The checked graph frame stores lengths in the fraction field and reserves
the explicit-demand field for the empty list. -/
def encode {n : ℕ} (A : Adjacency n) (w : Weights n) : Bits :=
  EncodedEdgeInput.encode (frame A w)

def parse (source : Bits) : Option (Σ n, EncodedEdgeInput.Input n) :=
  (EncodedEdgeInput.parse source).filter (fun d => d.2.demands.isEmpty)

private theorem parse_encode {n : ℕ} (A : Adjacency n) (w : Weights n) :
    parse (encode A w) = some ⟨n, frame A w⟩ := by
  simp [parse, encode, EncodedEdgeInput.parse_encode, frame]

/-- Read adjacency and original lengths without preparing a particular sampler. -/
def unpack (source : Bits) : Option (Σ n, Adjacency n × Weights n) :=
  (parse source).map fun ⟨n,D⟩ => ⟨n,(D.adjacency,lengthMatrix D)⟩

theorem unpack_encode {n : ℕ} (A : Adjacency n) (w : Weights n) :
    unpack (encode A w) = some ⟨n,(A,w)⟩ := by
  rw [unpack,parse_encode]
  change some (⟨n,(A,lengthMatrix (frame A w))⟩ : Σ k, Adjacency k × Weights k) = _
  rw [lengthMatrix_frame]

structure Checked (n : ℕ) where
  adjacency : Adjacency n
  lengths : Weights n
  ready : Preparation n

private def prepareFrame {n : ℕ} (D : EncodedEdgeInput.Input n) : Checked n :=
  let w := lengthMatrix D
  ⟨D.adjacency,w,prepare D.adjacency w⟩

private def layoutWork (n : ℕ) : ℕ := 20*n*n+12*n+8

def sourceBudget (n width : ℕ) : ℕ :=
  ChargedSourceAssembly.parseBudget width + prepareBudget n width + layoutWork n

/-- Record parsing and preparation work before the exhaustive family phase. -/
def check (source : Bits) : Option (Σ n, Checked n) × ℕ :=
  let decoded := ChargedSourceAssembly.edge source
  match decoded.1 with
  | none => (none,decoded.2+3)
  | some ⟨n,D⟩ =>
    if D.demands.isEmpty then
      let ch := prepareFrame D
      (some ⟨n,ch⟩,decoded.2+ch.ready.work+layoutWork n)
    else (none,decoded.2+5)

theorem check_value (source : Bits) :
    (check source).1 = (parse source).map (fun ⟨n,D⟩ => ⟨n,prepareFrame D⟩) := by
  unfold check parse
  rw [← ChargedSourceAssembly.edge_value]
  dsimp only
  cases (ChargedSourceAssembly.edge source).1 with
  | none => rfl
  | some d =>
    rcases d with ⟨n,D⟩
    by_cases h : D.demands.isEmpty = true <;> simp [Option.filter,h]

theorem check_valid_paid {source : Bits} {n : ℕ} {D : EncodedEdgeInput.Input n}
    (parsed : parse source = some ⟨n,D⟩) :
    n ≤ source.length ∧ (check source).2 ≤ sourceBudget n source.length := by
  have raw : (ChargedSourceAssembly.edge source).1 = some ⟨n,D⟩ := by
    rw [ChargedSourceAssembly.edge_value]
    exact Option.filter_eq_some_iff.mp parsed |>.1
  have h : D.demands.isEmpty = true := Option.filter_eq_some_iff.mp parsed |>.2
  have sizes := ChargedSourceAssembly.edge_dimensions raw
  refine ⟨sizes.1,?_⟩
  have fits (s t : Fin n) : StoredBounded (lengthMatrix D)[s.val][t.val] source.length := by
    simp only [lengthMatrix,Vector.getElem_ofFn,Fin.eta]
    exact sizes.2.2 _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem (finProdFinEquiv (s,t)).isLt))
  have phase := MeasuredBudgetRescaleEdgeFamily.prepare_paid D.adjacency (lengthMatrix D) source.length fits
  have charged := ChargedSourceAssembly.edge_paid source
  unfold check sourceBudget
  dsimp only
  rw [raw]
  simp only [h,ite_true,prepareFrame]
  omega

theorem check_invalid_paid {source : Bits} (parsed : parse source = none) :
    (check source).2 ≤ ChargedSourceAssembly.parseBudget source.length + 5 := by
  have charged := ChargedSourceAssembly.edge_paid source
  unfold parse at parsed
  rw [← ChargedSourceAssembly.edge_value] at parsed
  unfold check
  dsimp only
  cases hd : (ChargedSourceAssembly.edge source).1 with
  | none =>
    dsimp only
    omega
  | some d =>
    rcases d with ⟨n,D⟩
    have h : ¬ D.demands.isEmpty = true := by
      intro empty
      simp [hd,Option.filter,empty] at parsed
    dsimp only
    rw [ite_eq_right h]
    dsimp only
    omega

/-- The outer option is the checked graph frame. The inner options record
the exact result of the literal-tape sampler. The numeric component counts
the deterministic preparation prefix. -/
def draw (source : Bits) (trials : ℕ) (tape : Bits) : Option (Σ n, Draw n) × ℕ :=
  let frame := check source
  (frame.1.map (fun ⟨n,ch⟩ => ⟨n,drawPrepared ch.adjacency ch.lengths ch.ready trials tape⟩),frame.2)

theorem draw_value (source : Bits) (trials : ℕ) (tape : Bits) :
    (draw source trials tape).1 = (parse source).map (fun ⟨n,D⟩ =>
      ⟨n,RationalBudgetedRescaleEdgeFamily.draw D.adjacency (lengthMatrix D) trials tape⟩) := by
  simp only [draw,check_value,Option.map_map]
  congr 1
  funext d
  rcases d with ⟨n,D⟩
  exact congrArg (fun v : Draw n => (⟨n,v⟩ : Σ k, Draw k))
    (MeasuredBudgetRescaleEdgeFamily.draw_reference D.adjacency (lengthMatrix D) trials tape)

theorem draw_encode {n : ℕ} (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : Bits) :
    (draw (encode A w) trials tape).1 = some ⟨n,RationalBudgetedRescaleEdgeFamily.draw A w trials tape⟩ := by
  rw [draw_value,parse_encode]
  change some (⟨n,RationalBudgetedRescaleEdgeFamily.draw A (lengthMatrix (frame A w)) trials tape⟩ : Σ k, Draw k) = _
  rw [lengthMatrix_frame]

theorem draw_encode_paid {n : ℕ} (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : Bits) :
    n ≤ (encode A w).length ∧ (draw (encode A w) trials tape).2 ≤ sourceBudget n (encode A w).length :=
  check_valid_paid (parse_encode A w)

theorem draw_invalid {source : Bits} (h : parse source = none) (trials : ℕ) (tape : Bits) :
    draw source trials tape = (none,(check source).2) := by
  apply Prod.ext
  · simp [draw_value,h]
  · rfl

end DirectedFlowCutGap.MeasuredRescaleWire
