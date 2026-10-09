import DirectedFlowCutGap.IntegerShortestPaths
import DirectedFlowCutGap.VertexGridDistances
import DirectedFlowCutGap.GridLevelSampling
import DirectedFlowCutGap.TerminalPorts

/-!
# Integer midpoint level cuts from executed shortest paths

The algorithm computes actual endpoint-excluding distances by charging outgoing
edge numerators except at the fixed source. Every midpoint test is an integer
comparison. A complete supplied list drives all loops; no path enumeration,
real comparison, or choice occurs in executable definitions.
The complete-cut counter sums the declared shortest-path and cell-test counters
and inherits their exclusions. In particular, the source comparison inside
`outgoingNumerator` and evaluation of the supplied vertex-numerator function are
separate input-access costs, as are list operations and integer bit arithmetic.
-/
namespace DirectedFlowCutGap.IntegerLevelCuts

open scoped NNReal ENNReal
open IntegerShortestPaths

variable {V : Type*} [DecidableEq V]

/-- Executed distance numerator and primitive count for the vertex convention. -/
def vertexDistance (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (a : V → ℕ) (s t : V) : WithTop ℕ × ℕ :=
  distance E G (VertexGridDistances.outgoingNumerator a s) s t

/-- Membership in a midpoint cell. A finite test is charged four primitive
steps (one addition, two comparisons, one conjunction), an upper allowance
that also covers short-circuit evaluation. -/
def cellTest (d : WithTop ℕ) (a j : ℕ) : Bool × ℕ :=
  match d with
  | none => (false, 0)
  | some n => (decide (n ≤ j ∧ j < n+a), 4)

/-- Compute and retain the selected vertices, adding the actual subroutine counts. -/
def cutScan (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (a : V → ℕ) (s : V) (j : ℕ) : List V → List V × ℕ
  | [] => ([], 0)
  | v :: vs =>
      let d := vertexDistance E G a s v
      let b := cellTest d.1 (a v) j
      let r := cutScan E G a s j vs
      ((if b.1 then v :: r.1 else r.1), d.2 + b.2 + 1 + r.2)

 theorem cutScan_list (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (a : V → ℕ) (s : V) (j : ℕ) (vs : List V) :
    (cutScan E G a s j vs).1 =
      vs.filter (fun v => (cellTest (vertexDistance E G a s v).1 (a v) j).1) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [cutScan, List.filter_cons, ih]

/-- No deduplication scan is executed: the enumeration's uniqueness is retained. -/
def cut (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (a : V → ℕ) (s : V) (j : ℕ) : Finset V × ℕ :=
  let r := cutScan E G a s j E.vertices
  (⟨r.1, by
    rw [cutScan_list]
    exact E.nodup.filter _⟩, r.2)

 theorem mem_cut (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (a : V → ℕ) (s v : V) (j : ℕ) :
    v ∈ (cut E G a s j).1 ↔
      (cellTest (vertexDistance E G a s v).1 (a v) j).1 = true := by
  simp [cut, cutScan_list, E.complete v]

 theorem cellTest_count_le (d : WithTop ℕ) (a j : ℕ) :
    (cellTest d a j).2 ≤ 4 := by cases d <;> simp [cellTest]

 theorem cutScan_count_le (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (a : V → ℕ) (s : V) (j : ℕ) (vs : List V) :
    (cutScan E G a s j vs).2 ≤ vs.length *
      (E.vertices.length^2 * (3*E.vertices.length+2) + 3*E.vertices.length + 5) := by
  induction vs with
  | nil => simp [cutScan]
  | cons v vs ih =>
    have hd := distance_count_le E G (VertexGridDistances.outgoingNumerator a s) s v
    have hb := cellTest_count_le (vertexDistance E G a s v).1 (a v) j
    change (vertexDistance E G a s v).2 ≤ _ at hd
    simp only [cutScan, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Polynomial primitive bound for a complete midpoint cut, including all calls. -/
 theorem cut_count_le (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (a : V → ℕ) (s : V) (j : ℕ) :
    (cut E G a s j).2 ≤ E.vertices.length *
      (E.vertices.length^2 * (3*E.vertices.length+2) + 3*E.vertices.length + 5) :=
  cutScan_count_le E G a s j E.vertices

 theorem cutScan_empty (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (a : V → ℕ) (s : V) (j : ℕ) : cutScan E G a s j [] = ([],0) := rfl

variable [Fintype V]

/-- Equality to the frozen actual distance, including zero and infinite values. -/
 theorem vertexDistance_correct (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (a : V → ℕ) (L : ℕ) (s t : V) :
    scaled L (vertexDistance E G a s t).1 =
      DirectedFlowCutGap.vertexDistance G (fun v => (a v : ℝ≥0) / L) s t := by
  rw [vertexDistance, distance_correct, VertexGridDistances.grid_edgeDistance_eq_vertexDistance]

/-- Infinite output has precisely the original graph's disconnected-pair semantics. -/
 theorem vertexDistance_eq_top_iff (E : Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (a : V → ℕ) (s t : V) :
    (vertexDistance E G a s t).1 = ⊤ ↔ ¬Nonempty (SimplePath G s t) := by
  have h := vertexDistance_correct E G a 1 s t
  simp only [Nat.cast_one] at h
  rw [← DirectedFlowCutGap.vertexDistance_eq_top_iff G (fun v => (a v : ℝ≥0)/1) s t,
    ← h]
  cases (vertexDistance E G a s t).1 using WithTop.recTopCoe <;> simp [scaled]

/-- The whole computed finite set is the actual real midpoint level cut. -/
 theorem cut_correct (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (a : V → ℕ) {L : ℕ} (hL : 0 < L) (s : V) (j : Fin L) :
    (cut E G a s j.val).1 = levelCut G (fun v => (a v : ℝ≥0)/L) s
      (GridLevelSampling.midpoint L j).toNNReal := by
  ext v
  rw [mem_cut]
  have hd := (vertexDistance_correct E G a L s v).symm
  cases he : (vertexDistance E G a s v).1 using WithTop.recTopCoe with
  | top =>
    have hd' : DirectedFlowCutGap.vertexDistance G (fun v => (a v : ℝ≥0)/L) s v = ⊤ := by
      simpa only [he, scaled_top] using hd
    simp [cellTest, not_mem_levelCut_of_distance_top hd']
  | coe n =>
    have hd' : DirectedFlowCutGap.vertexDistance G (fun v => (a v : ℝ≥0)/L) s v =
        (((n : ℝ≥0)/L : ℝ≥0) : ℝ≥0∞) := by
      simpa only [he, scaled] using hd
    rw [GridLevelSampling.mem_levelCut_iff_grid hL s v j
      (GridLevelSampling.midpoint_mem_cell hL j) n (a v) hd' rfl]
    simp [cellTest]

/-- Natural grid coordinates for the permanent core/source/sink construction. -/
def portNumerator (a : V → ℕ) : TerminalPorts.Vertex V → ℕ
  | .inl v => a v
  | .inr _ => 0

/-- The same executed algorithm preserves the permanent-port distance identity. -/
 theorem portDistance_correct (E : Enumeration (TerminalPorts.Vertex V))
    (G : Digraph V) [DecidableRel (TerminalPorts.graph G).Adj]
    (a : V → ℕ) (L : ℕ) (s t : V) :
    scaled L (vertexDistance E (TerminalPorts.graph G) (portNumerator a)
      (TerminalPorts.source s) (TerminalPorts.sink t)).1 =
      DirectedFlowCutGap.vertexDistance G (fun v => (a v : ℝ≥0)/L) s t := by
  rw [vertexDistance_correct]
  have hw : (fun v : TerminalPorts.Vertex V => (portNumerator a v : ℝ≥0)/L) =
      TerminalPorts.extend (fun v => (a v : ℝ≥0)/L) := by
    funext v
    cases v with
    | inl v => rfl
    | inr v => simp [portNumerator, TerminalPorts.extend]
  rw [hw, TerminalPorts.vertexDistance_eq]

omit [Fintype V] in
/-- Numerator bit size is controlled by the vertex numerator budget. -/
 theorem vertexDistance_bits_bound (E : Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (a : V → ℕ) (C : ℕ) (s t : V) (ha : ∀ v, a v ≤ C)
    (d : ℕ) (hd : (vertexDistance E G a s t).1 = d) :
    d.size ≤ (E.vertices.length*C).size := by
  apply distance_bits_bound E G (VertexGridDistances.outgoingNumerator a s) C s t _ d hd
  intro e
  simp only [VertexGridDistances.outgoingNumerator]
  split_ifs
  · exact Nat.zero_le _
  · exact ha e.1

omit [Fintype V] in
/-- The addition in a finite midpoint test stays inside a polynomial numerator budget. -/
 theorem midpoint_numerator_bound (E : Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (a : V → ℕ) (L : ℕ) (s v : V) (ha : ∀ u, a u ≤ L)
    (d : ℕ) (hd : (vertexDistance E G a s v).1 = d) :
    d + a v ≤ (E.vertices.length+1)*L := by
  have hc : ∀ e, VertexGridDistances.outgoingNumerator a s e ≤ L := by
    intro e
    simp only [VertexGridDistances.outgoingNumerator]
    split_ifs
    · exact Nat.zero_le _
    · exact ha e.1
  have h := distance_numerator_bound E G (VertexGridDistances.outgoingNumerator a s)
    L s v hc d hd
  have hv := ha v
  nlinarith

omit [Fintype V] in
/-- In the intended regime L≤n, the largest midpoint numerator is at most n(n+1). -/
 theorem midpoint_bits_bound (E : Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (a : V → ℕ) (L : ℕ) (s v : V) (ha : ∀ u, a u ≤ L)
    (hL : L ≤ E.vertices.length) (d : ℕ)
    (hd : (vertexDistance E G a s v).1 = d) :
    (d + a v).size ≤ (E.vertices.length*(E.vertices.length+1)).size := by
  apply Nat.size_le_size
  exact (midpoint_numerator_bound E G a L s v ha d hd).trans (by nlinarith)

end DirectedFlowCutGap.IntegerLevelCuts
