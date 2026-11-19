import DirectedFlowCutGap.ActualGraphShortest
import DirectedFlowCutGap.EncodedRoundingInput

/-!
# Interpreting the physical shortest-path result as an integer distance

For integer vertex weights, the encoded recovery routine has
denominator-one inputs and a denominator-one answer. Its numerator,
with absence interpreted as infinity, is the exact distance used by
the rounding controller.
-/

namespace DirectedFlowCutGap.IntegerDistanceFromPhysical

open scoped NNReal NNRat ENNReal
open BinaryArithmetic BinaryRational RetainedGridState IntegerShortestPaths
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open FractionalCoverRawCore (rational)

def encodedRow {n : ℕ} (a : RetainedGridState.Row n) : BinaryFractionalRows.Row n :=
  Vector.ofFn fun i => ⟨a[i.val].bits, [true], by decide⟩

private def outgoing {n : ℕ} (a : RetainedGridState.Row n) (s : Fin n) : Pair n → ℕ :=
  VertexGridDistances.outgoingNumerator (fun i => a[i.val]) s

theorem decode_cost {n : ℕ} (a : RetainedGridState.Row n) (s : Fin n) (e : Pair n) :
    BinaryFractionalWalkOracle.decodeCost (BinaryFractionalGraphOracle.outgoing (encodedRow a) s) e =
      RawNonnegativeRational.Code.ofNat (outgoing a s e) := by
  rw [BinaryFractionalGraphOracle.outgoing_decode]
  by_cases h : e.1 = s
  · simp [FractionalCoverRawGraph.outgoing,outgoing,VertexGridDistances.outgoingNumerator,h,
      RawNonnegativeRational.Code.zero,RawNonnegativeRational.Code.ofNat]
  · simp [FractionalCoverRawGraph.outgoing,outgoing,VertexGridDistances.outgoingNumerator,h,
      encodedRow,BinaryFractionalRows.get,decode,value_bits,RawNonnegativeRational.Code.ofNat,value]

private theorem sum_den {n : ℕ} (a : RetainedGridState.Row n) (s : Fin n) (es : List (Pair n)) :
    value (BinaryFractionalRows.sum
      (BinaryFractionalWalkOracle.costList (BinaryFractionalGraphOracle.outgoing (encodedRow a) s) es).1).1.den = 1 := by
  change (decode (BinaryFractionalRows.sum _).1).den = 1
  rw [BinaryFractionalRows.sum_decode,BinaryFractionalWalkOracle.costList_decode]
  rw [funext (decode_cost a s)]
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,FractionalCoverRawCore.sumCodes,RawNonnegativeRational.Code.add,
      RawNonnegativeRational.Code.ofNat,Nat.one_mul]
    exact ih

abbrev Candidate := BinaryFractionalWalkOracle.Candidate

def shortest {n : ℕ} (E : Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : RetainedGridState.Row n) (s t : Fin n) : Option (Candidate n) :=
  (BinaryFractionalWalkOracle.shortest E adjacency (BinaryFractionalGraphOracle.outgoing (encodedRow a) s) s t).1

theorem shortest_den {n : ℕ} (E : Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : RetainedGridState.Row n) (s t : Fin n) {q : Candidate n}
    (h : shortest E adjacency a s t = some q) : value q.cost.den = 1 := by
  unfold shortest BinaryFractionalWalkOracle.shortest at h
  dsimp only at h
  split at h
  · cases h
  · rename_i x _
    cases h
    unfold BinaryFractionalWalkOracle.recover
    exact sum_den a s _

def result {n : ℕ} (q : Option (Candidate n)) : WithTop ℕ :=
  match q with
  | none => ⊤
  | some path => value path.cost.num

private theorem scaled_one_injective : Function.Injective (scaled 1) := by
  intro a b h
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;>
    simp_all [scaled_coe]

private theorem path_numerator {n : ℕ} {G : Digraph (Fin n)} {s t : Fin n}
    (a : RetainedGridState.Row n) (p : SimplePath G s t) :
    FractionalCoverWalkOracle.pathCost
      (fun e => rational (BinaryFractionalWalkOracle.decodeCost (BinaryFractionalGraphOracle.outgoing (encodedRow a) s) e)) p =
      ((∑ e ∈ p.edges, outgoing a s e : ℕ) : ℚ) := by
  simp [FractionalCoverWalkOracle.pathCost,decode_cost,Nat.cast_sum]

private theorem edge_numerator {n : ℕ} {G : Digraph (Fin n)} {s t : Fin n}
    (a : RetainedGridState.Row n) (p : SimplePath G s t) :
    p.edgeWeight (fun e => (outgoing a s e : ℝ≥0)) =
      ((∑ e ∈ p.edges, outgoing a s e : ℕ) : ℝ≥0) := by
  simp [SimplePath.edgeWeight,Nat.cast_sum]

theorem result_eq {n : ℕ} (E : Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : RetainedGridState.Row n) (s t : Fin n) :
    result (shortest E adjacency a s t) =
      (EncodedIntegerShortestPaths.distance E adjacency a s t).1 := by
  let G := BinaryFractionalWalkOracle.graph adjacency
  let _ : DecidableRel G.Adj := by dsimp only [G]; infer_instance
  let c := BinaryFractionalGraphOracle.outgoing (encodedRow a) s
  let cost := fun e => rational (BinaryFractionalWalkOracle.decodeCost c e)
  let weight := fun e => (outgoing a s e : ℝ≥0)
  have hc (e : Pair n) : 0 ≤ cost e := NNRat.coe_nonneg _
  have he := congrArg Prod.fst (FractionalCoverRawOracle.shortest_refines E G (BinaryFractionalWalkOracle.decodeCost c) s t)
  change ((FractionalCoverRawOracle.shortest E G (BinaryFractionalWalkOracle.decodeCost c) s t).1.map
    FractionalCoverRawOracle.decode) = (FractionalCoverPathOracle.shortest E G cost s t).1 at he
  rw [← BinaryFractionalWalkOracle.shortest_decode] at he
  rw [Option.map_map] at he
  change ((shortest E adjacency a s t).map
    (FractionalCoverRawOracle.decode ∘ BinaryFractionalWalkOracle.decode)) = _ at he
  have hd : scaled 1 (EncodedIntegerShortestPaths.distance E adjacency a s t).1 =
      edgeDistance G weight s t := by
    rw [EncodedIntegerShortestPaths.distance_value]
    exact (distance_correct E G (outgoing a s) 1 s t).trans (by simp [weight])
  apply scaled_one_injective
  rw [hd]
  cases h : shortest E adjacency a s t with
  | none =>
    rw [h] at he
    have hn := (FractionalCoverPathOracle.shortest_none_iff E G cost hc s t).mp he.symm
    simpa [result] using ((edgeDistance_eq_top_iff G weight s t).mpr hn).symm
  | some q =>
    have hden := shortest_den E adjacency a s t h
    have hnum : rational (decode q.cost) = (value q.cost.num : ℚ) := by
      simp [rational,RawNonnegativeRational.Code.value,decode,hden]
    have obs : scaled 1 (result (some q)) = ((value q.cost.num : ℝ≥0) : ℝ≥0∞) := by
      simp [result]
    rw [obs]
    rw [h, Option.map_some] at he
    apply le_antisymm
    · rw [le_edgeDistance_iff]
      intro p
      obtain ⟨j,hj,hmin⟩ := FractionalCoverPathOracle.shortest_minimum E G cost hc s t p
      rw [hj] at he
      have hq := Option.some.inj he
      subst j
      change rational (decode q.cost) ≤ FractionalCoverWalkOracle.pathCost cost p at hmin
      rw [hnum,path_numerator a p] at hmin
      rw [edge_numerator a p]
      exact_mod_cast hmin
    · obtain ⟨p,_,hp⟩ := FractionalCoverPathOracle.shortest_valid E G cost s t he.symm
      change rational (decode q.cost) = FractionalCoverWalkOracle.pathCost cost p at hp
      rw [hnum,path_numerator a p] at hp
      have hn : value q.cost.num = ∑ e ∈ p.edges, outgoing a s e := by exact_mod_cast hp
      have hle := edgeDistance_le_weight weight p
      change edgeDistance G weight s t ≤ (p.edgeWeight (fun e => (outgoing a s e : ℝ≥0)) : ℝ≥0∞) at hle
      rwa [edge_numerator a p,← hn] at hle

theorem encodedRow_stored {n : ℕ} (a : RetainedGridState.Row n) (W : ℕ) (hW : 1 ≤ W)
    (hwidth : ∀ i : Fin n, a[i.val].bits.length ≤ W) :
    ∀ f ∈ (encodedRow a).toList, StoredBounded f W := by
  intro f hf
  simp only [encodedRow,Vector.toList_ofFn] at hf
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  exact ⟨hwidth i,hW⟩

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

def interpret (r : Option GraphWalkExtension.Walk) : WithTop ℕ :=
  r.map (fun w => value w.cost.num)

def StoredDistance (heap : NaturalHeap) (root : ℕ) (d : WithTop ℕ) : Prop :=
  ∃ r, GraphDiscoveryProgram.StoredOption heap root r ∧ interpret r = d ∧
    ∀ w ∈ r, value w.cost.den = 1

theorem physical_distance {n H A : ℕ} (E : Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : RetainedGridState.Row n) (s t : Fin n)
    (sw : Bits) (hs : value sw = s.val) (label : Fin n → Bits) (hlabel : ∀ i, value (label i) = i.val)
    (initial : BitState 1344) (hstate : initial.Bounded H A)
    (hp : initial.pc = 1342) (hd : value initial.next = initial.heap.length) (hc : initial.stack = [])
    (input : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a
      (E.vertices.map label))
    (context : GraphDiscoveryProgram.GlobalContext (eraseState initial).heap (eraseState initial).registers.b
      (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (encodedRow a).toList sw (label t))
    (src : BoolList (eraseState initial).heap (eraseState initial).registers.c (label s))
    (W : ℕ) (hW : 1 ≤ W) (hw : sw.length ≤ W) (labels : ∀ i, (label i).length ≤ W)
    (hrow : ∀ i : Fin n, a[i.val].bits.length ≤ W) :
    ∃ paid out, Run GraphRecoveryController.program
        (GraphRecoveryController.steps (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
          (encodedRow a).toList sw (label t) (label s) + 1) paid initial [] out ∧
      StoredDistance (eraseState out).heap (eraseState out).registers.d
        (EncodedIntegerShortestPaths.distance E adjacency a s t).1 ∧
      out.source = initial.source ∧ out.stack = [] ∧ out.pc = 1343 ∧
      (attempt GraphRecoveryController.program out).result = none ∧
      paid + (attempt GraphRecoveryController.program out).operations ≤
        completeBound 1344 H A (GraphRecoveryController.instructionBound n W sw.length) := by
  obtain ⟨paid,out,hr,hout,_,_,_,htape,hstack,hpc,_,hstop,hcost⟩ :=
    GraphRecoveryController.graph_bit E adjacency (encodedRow a) s t sw hs label hlabel initial hstate hp hd hc
      input context src W hW hw labels (encodedRow_stored a W hW hrow)
  refine ⟨paid,out,hr,?_,htape,hstack,hpc,hstop,hcost⟩
  let q := shortest E adjacency a s t
  let encode := GraphRelaxationRefinement.encode label
  change GraphDiscoveryProgram.StoredOption (eraseState out).heap (eraseState out).registers.d (q.map encode) at hout
  refine ⟨q.map encode,hout,?_,?_⟩
  · rw [← result_eq E adjacency a s t]
    change interpret (q.map encode) = result q
    cases q <;> rfl
  · intro f hf
    change f ∈ q.map encode at hf
    obtain ⟨v,hv,rfl⟩ := Option.mem_map.mp hf
    exact shortest_den E adjacency a s t hv

end DirectedFlowCutGap.IntegerDistanceFromPhysical
