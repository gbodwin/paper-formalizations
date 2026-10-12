import DirectedFlowCutGap.GraphRecoveryRefinement
import DirectedFlowCutGap.GraphDiscoveryBounds

namespace DirectedFlowCutGap.GraphRecoveryController
open BinaryArithmetic BinaryRational GraphWalkExtension

theorem at_edge_length {adjacency : List Bits} {rows : List Fraction} {sw target u : Bits}
    {old : List GraphDiscoveryProgram.Entry} {q : Walk} {k : ℕ}
    (ho : ∀ x∈old,x.2.edges.length ≤ k)
    (hq : GraphDiscoveryProgram.atVertex adjacency rows sw target u old=some q) :
    q.edges.length ≤ k+1 := by
  unfold GraphDiscoveryProgram.atVertex at hq
  split at hq
  · cases Option.some.inj hq
    simp [GraphDiscoveryProgram.zero]
  · obtain ⟨x,hx,rfl⟩ := GraphRelaxationProgram.scan_witness hq
    simpa only [GraphWalkExtension.result,List.length_cons] using Nat.add_le_add_right (ho x hx) 1

theorem pass_edge_length (adjacency : List Bits) (rows : List Fraction) (sw target : Bits)
    (old : List GraphDiscoveryProgram.Entry) (vs : List Bits) (k : ℕ)
    (ho : ∀ x∈old,x.2.edges.length ≤ k) :
    ∀ x∈GraphDiscoveryProgram.pass adjacency rows sw target old vs,x.2.edges.length ≤ k+1 := by
  induction vs with
  | nil => simp [GraphDiscoveryProgram.pass]
  | cons u us ih =>
    intro x hx
    simp only [GraphDiscoveryProgram.pass] at hx
    cases hq : GraphDiscoveryProgram.atVertex adjacency rows sw target u old with
    | none => exact ih x (by simpa only [hq] using hx)
    | some q =>
      simp only [hq,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact at_edge_length ho hq
      · exact ih x hx

theorem rounds_edge_length (vs adjacency : List Bits) (rows : List Fraction) (sw target : Bits)
    (fuel : List Bits) :
    ∀ x∈GraphDiscoveryProgram.rounds vs adjacency rows sw target fuel,x.2.edges.length ≤ fuel.length := by
  induction fuel with
  | nil => simp [GraphDiscoveryProgram.rounds,GraphDiscoveryProgram.zero]
  | cons u us ih => exact pass_edge_length adjacency rows sw target _ vs us.length ih

theorem minimize_edge_length {vs adjacency : List Bits} {rows : List Fraction} {sw target u : Bits}
    {q : Walk} (hq : GraphDiscoveryProgram.minimize vs adjacency rows sw target u=some q) :
    q.edges.length ≤ vs.length := by
  obtain ⟨x,hx,rfl⟩ := GraphDiscoveryProgram.lookup_witness hq
  exact rounds_edge_length vs adjacency rows sw target vs x hx

end DirectedFlowCutGap.GraphRecoveryController
