import DirectedFlowCutGap.GraphDiscoveryBounds
import DirectedFlowCutGap.GraphMinimizeConstruction

/-! A polynomial instruction bound for all real rounds and the same-table
lookup. The common width is derived from input bit lengths and round count. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational BinaryFractionalRows GraphWalkExtension

def roundBudget (m k W N S : ℕ) : ℕ := k*(passBudget m (max 1 m) W N S+11)+13

theorem rounds_bound (vertices adjacency : List Bits) (rows : List Fraction) (sw target : Bits)
    (fuel : List Bits) (B W N k : ℕ) (hB : 1 ≤ B) (hBW : B ≤ W)
    (hwidth : roundWidth B k ≤ W) (hr : ∀ q∈rows,StoredBounded q B)
    (ht : target.length ≤ B) (it : value target ≤ N)
    (hi : ∀ u∈vertices,value u<rows.length)
    (hv : ∀ u∈vertices,u.length ≤ B ∧ value u ≤ N) (hk : fuel.length ≤ k) :
    roundSteps vertices adjacency rows sw target fuel ≤ roundBudget vertices.length fuel.length W N sw.length := by
  have hW : 1 ≤ W := hB.trans hBW
  have hrW : ∀ q∈rows,StoredBounded q W := fun q hq => bounded_mono (hr q hq) hBW
  have htW := ht.trans hBW
  have hvW : ∀ u∈vertices,u.length ≤ W ∧ value u ≤ N := fun u hu => ⟨(hv u hu).1.trans hBW,(hv u hu).2⟩
  induction fuel with
  | nil => simp [roundSteps,roundBudget]
  | cons u us ih =>
    have hus : us.length ≤ k := by simpa using Nat.le_trans (Nat.le_succ us.length) hk
    have hh := ih hus
    have hcost := round_width (vertices:=vertices) (adjacency:=adjacency) (sw:=sw) (target:=target) us hB hr hi
    have hmono : roundWidth B us.length ≤ W :=
      (Nat.add_le_add_left (Nat.mul_le_mul_right (B+2) hus) 1).trans hwidth
    have hx : ∀ x∈rounds vertices adjacency rows sw target us,GraphRelaxationProgram.EntryBound W N x := by
      intro x hx
      have hc := bounded_mono (hcost x hx) hmono
      rcases round_label us hx with h|h
      · exact ⟨by simpa [h] using htW,by simpa [h] using it,hc⟩
      · exact ⟨(hvW x.1 h).1,(hvW x.1 h).2,hc⟩
    have hp := pass_bound adjacency rows sw target (rounds vertices adjacency rows sw target us)
      vertices W N (max 1 vertices.length) hW hrW htW hi hvW hx (round_length vertices adjacency rows sw target us)
    simp only [roundSteps,roundBudget,List.length_cons,Nat.add_mul] at *
    omega

def discoveryWidth (m B : ℕ) : ℕ := B+roundWidth B m

def discoveryBudget (m B N S : ℕ) : ℕ :=
  roundBudget m m (discoveryWidth m B) N S+
    lookupBudget (max 1 m) (discoveryWidth m B)+6

theorem minimize_bound (vertices adjacency : List Bits) (rows : List Fraction) (sw target u : Bits)
    (B N : ℕ) (hB : 1 ≤ B) (hr : ∀ q∈rows,StoredBounded q B)
    (ht : target.length ≤ B) (it : value target ≤ N) (hu : u.length ≤ B)
    (hi : ∀ v∈vertices,value v<rows.length)
    (hv : ∀ v∈vertices,v.length ≤ B ∧ value v ≤ N) :
    minimizeSteps vertices adjacency rows sw target u+1 ≤ discoveryBudget vertices.length B N sw.length := by
  let W := discoveryWidth vertices.length B
  have hBW : B ≤ W := Nat.le_add_right _ _
  have hwidth : roundWidth B vertices.length ≤ W := Nat.le_add_left _ _
  have hrnd := rounds_bound vertices adjacency rows sw target vertices B W N vertices.length hB hBW
    hwidth hr ht it hi hv le_rfl
  have hcost := round_width (vertices:=vertices) (adjacency:=adjacency) (sw:=sw) (target:=target) vertices hB hr hi
  have hx : ∀ x∈rounds vertices adjacency rows sw target vertices,x.1.length ≤ W ∧ StoredBounded x.2.cost W := by
    intro x hx
    refine ⟨?_,bounded_mono (hcost x hx) hwidth⟩
    rcases round_label vertices hx with h|h
    · simpa [h] using ht.trans hBW
    · exact (hv x.1 h).1.trans hBW
  have hl := lookup_bound u (rounds vertices adjacency rows sw target vertices) W (hu.trans hBW) hx
  have hlen := round_length vertices adjacency rows sw target vertices
  have hm : lookupBudget (rounds vertices adjacency rows sw target vertices).length W ≤
      lookupBudget (max 1 vertices.length) W := by
    unfold lookupBudget
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) _
  have hl := hl.trans hm
  simp only [minimizeSteps,discoveryBudget]
  simpa only [Nat.add_assoc] using Nat.add_le_add_right (Nat.add_le_add hrnd hl) 6

end DirectedFlowCutGap.GraphDiscoveryProgram
