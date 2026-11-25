import DirectedFlowCutGap.MeasuredRescaleWire
import DirectedFlowCutGap.RationalRankedEdgeOracle

namespace DirectedFlowCutGap.RationalRankedEdgeWire

open scoped NNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalEdgeDecomposition (Good originalWeight)
open RationalExactEdgeOracle (Edge)
open RationalRankedEdgeOracle (recognizes singleCut_none_iff)

/-- The outer option validates the frame. The inner option requires a
rank certificate for the decoded graph. On success the entire tape is returned. -/
def draw (source tape : Bits) : Option (Σ n, Option (Finset (Edge n) × Bits)) :=
  (MeasuredRescaleWire.unpack source).map fun ⟨n,A,w⟩ =>
    ⟨n,RationalRankedEdgeOracle.draw A w tape⟩

theorem draw_invalid {source : Bits} (h : MeasuredRescaleWire.parse source = none) (tape : Bits) :
    draw source tape = none := by
  simp [draw,MeasuredRescaleWire.unpack,h]

theorem draw_encode {n : ℕ} (A : Adjacency n) (w : Weights n) (tape : Bits) :
    draw (MeasuredRescaleWire.encode A w) tape = some ⟨n,RationalRankedEdgeOracle.draw A w tape⟩ := by
  simp [draw,MeasuredRescaleWire.unpack_encode]

theorem draw_outside {source : Bits} {n : ℕ} {A : Adjacency n} {w : Weights n}
    (decoded : MeasuredRescaleWire.unpack source = some ⟨n,(A,w)⟩) (tape : Bits)
    (unsupported : recognizes A w = false) : draw source tape = some ⟨n,none⟩ := by
  have rejected := (singleCut_none_iff A w).mpr unsupported
  simp [draw,decoded,RationalRankedEdgeOracle.draw,rejected]

theorem draw_spec {source : Bits} {n : ℕ} {A : Adjacency n} {w : Weights n}
    (decoded : MeasuredRescaleWire.unpack source = some ⟨n,(A,w)⟩) (tape : Bits)
    (recognized : recognizes A w = true) :
    ∃ X, draw source tape = some ⟨n,some (X,tape)⟩ ∧ Good A w X ∧
      ∀ e, (if e ∈ X then (1 : ℝ) else 0) ≤
        2*(originalWeight A w e : ℝ)*
          (ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  obtain ⟨X,found,good,marginal⟩ := RationalRankedEdgeOracle.draw_spec A w tape recognized
  exact ⟨X,by simp [draw,decoded,found],good,marginal⟩

end DirectedFlowCutGap.RationalRankedEdgeWire
