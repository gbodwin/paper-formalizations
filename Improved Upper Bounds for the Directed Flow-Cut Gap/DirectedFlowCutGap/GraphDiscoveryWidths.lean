import DirectedFlowCutGap.GraphRoundData

/-! Actual canonical fractions grow only linearly with the number of rounds.
This follows from each real retained winner being a single one-edge extension. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational BinaryFractionalRows GraphWalkExtension

theorem bounded_mono {q : Fraction} {B W : ℕ} (h : StoredBounded q B) (le : B ≤ W) :
    StoredBounded q W := ⟨h.1.trans le,h.2.trans le⟩

theorem vertex_width {adjacency : List Bits} {rows : List Fraction} {sw target u : Bits}
    {old : List Entry} {q : Walk} {B W : ℕ}
    (hB : 1 ≤ B) (hr : ∀ x∈rows,StoredBounded x B) (hi : value u<rows.length)
    (ho : ∀ x∈old,StoredBounded x.2.cost W)
    (hq : atVertex adjacency rows sw target u old=some q) : StoredBounded q.cost (B+W+2) := by
  unfold atVertex at hq
  split at hq
  · cases Option.some.inj hq
    simp [zero,BinaryRational.zero,StoredBounded]
  · obtain ⟨x,hx,rfl⟩ := GraphRelaxationProgram.scan_witness hq
    exact add_stored_bounded (stored_raw_bound (GraphRelaxationProgram.outgoing_width rows sw u B hB hr hi))
      (stored_raw_bound (ho x hx))

theorem pass_width {adjacency : List Bits} {rows : List Fraction} {sw target : Bits}
    {old : List Entry} {vertices : List Bits} {B W : ℕ}
    (hB : 1 ≤ B) (hr : ∀ x∈rows,StoredBounded x B)
    (hi : ∀ u∈vertices,value u<rows.length) (ho : ∀ x∈old,StoredBounded x.2.cost W) :
    ∀ x∈pass adjacency rows sw target old vertices,StoredBounded x.2.cost (B+W+2) := by
  induction vertices with
  | nil => simp [pass]
  | cons u us ih =>
    intro x hx
    simp only [pass] at hx
    cases hq : atVertex adjacency rows sw target u old with
    | none =>
      simp only [hq] at hx
      exact ih (fun v hv => hi v (by simp [hv])) x hx
    | some q =>
      simp only [hq,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact vertex_width hB hr (hi u (by simp)) ho hq
      · exact ih (fun v hv => hi v (by simp [hv])) x hx

def roundWidth (B k : ℕ) : ℕ := 1+k*(B+2)

theorem round_width {vertices adjacency : List Bits} {rows : List Fraction} {sw target : Bits}
    (fuel : List Bits) {B : ℕ} (hB : 1 ≤ B) (hr : ∀ x∈rows,StoredBounded x B)
    (hi : ∀ u∈vertices,value u<rows.length) :
    ∀ x∈rounds vertices adjacency rows sw target fuel,StoredBounded x.2.cost (roundWidth B fuel.length) := by
  induction fuel with
  | nil =>
    intro x hx
    simp only [rounds,List.mem_singleton] at hx
    subst x;simp [roundWidth,zero,BinaryRational.zero,StoredBounded]
  | cons u us ih =>
    have hw := pass_width (adjacency:=adjacency) (sw:=sw) (target:=target) hB hr hi ih
    have he : B+roundWidth B us.length+2=roundWidth B (u::us).length := by
      simp only [roundWidth,List.length_cons];ring
    simpa only [rounds,he] using hw

theorem pass_length (adjacency : List Bits) (rows : List Fraction) (sw target : Bits)
    (old : List Entry) (vertices : List Bits) :
    (pass adjacency rows sw target old vertices).length ≤ vertices.length := by
  induction vertices with
  | nil => simp [pass]
  | cons u us ih =>
    simp only [pass,List.length_cons]
    cases atVertex adjacency rows sw target u old <;> simp only [List.length_cons] <;> omega

theorem round_length (vertices adjacency : List Bits) (rows : List Fraction) (sw target : Bits)
    (fuel : List Bits) : (rounds vertices adjacency rows sw target fuel).length ≤ max 1 vertices.length := by
  cases fuel with
  | nil => simp [rounds]
  | cons u us => exact (pass_length adjacency rows sw target _ vertices).trans (Nat.le_max_right _ _)

end DirectedFlowCutGap.GraphDiscoveryProgram
