import DirectedFlowCutGap.BinaryFractionalDispatch
import DirectedFlowCutGap.BinaryFractionalGraphBounds

/-!
# Charges of original-input degeneracy dispatch

All stopping branches are bounded: infeasible endpoint demands, a free cut,
and the positive subproblem. The proof charges the actual zero-bit scans,
endpoint-preserving adjacency construction, and every performed path query.
-/
namespace DirectedFlowCutGap.BinaryFractionalDispatchBounds
open BinaryRational BinaryFractionalRows BinaryFractionalWalkOracle
open BinaryFractionalWalkBounds BinaryFractionalGraphOracle BinaryFractionalGraphBounds
open BinaryFractionalDispatch IntegralNetworkFlow
variable {n m B : ℕ}

def zeroMaskBound (m B : ℕ) : ℕ := m*(4*(B+1)+11)+EncodedRoundingInput.arrayBound m

theorem zeroMask_charge (c : Row m) (hc : ∀ i, StoredBounded (get c i) B) :
    (zeroMask c).2 ≤ zeroMaskBound m B := by
  apply EncodedRoundingInput.tabulate_bound _ (4*(B+1)+11)
  intro i
  have hz := isZero_charge (hc i)
  simp only [read_value,read_charge]
  omega

def keptAdjacencyBound (n : ℕ) : ℕ :=
  n*(52*n+EncodedRoundingInput.arrayBound n)+EncodedRoundingInput.arrayBound n

theorem keptAdjacency_charge (adjacency : Adjacency n) (mask : Vector Bool n) (s t : Fin n) :
    (keptAdjacency adjacency mask s t).2 ≤ keptAdjacencyBound n := by
  apply EncodedRoundingInput.tabulate_bound _ (52*n+EncodedRoundingInput.arrayBound n)
  intro u
  have h := EncodedRoundingInput.tabulate_bound (fun v : Fin n =>
      let a := adjacent adjacency u v
      let zu := EncodedArrayStorage.readCallback mask u
      let zv := EncodedArrayStorage.readCallback mask v
      let ku := !zu.1 || decide (u=s) || decide (u=t)
      let kv := !zv.1 || decide (v=s) || decide (v=t)
      (a.1 && ku && kv,a.2+zu.2+zv.2+20)) 52 (fun _ => by rfl)
  simpa only [Nat.mul_comm n 52] using h

theorem emptyDemand_charge (adjacency : Adjacency n) (ds : List (Pair n)) :
    (emptyDemand adjacency ds).2 ≤ 26*ds.length+1 := by
  induction ds with
  | nil => simp [emptyDemand]
  | cons d ds ih =>
    simp only [emptyDemand,List.length_cons]
    split <;> simp only [adjacent_charge] <;> omega

def findAvoidingBound (n D : ℕ) : ℕ := D*(keptAdjacencyBound n+shortestBound n 1 1+8)+1

theorem findAvoiding_charge (adjacency : Adjacency n) (mask : Vector Bool n)
    (ds : List (Pair n)) : (findAvoiding adjacency mask ds).2 ≤ findAvoidingBound n ds.length := by
  induction ds with
  | nil => simp [findAvoiding,findAvoidingBound]
  | cons d ds ih =>
    have ha := keptAdjacency_charge adjacency mask d.1 d.2
    have hp := shortest_charge (ResidualSearch.Enumeration.fin n)
      (keptAdjacency adjacency mask d.1 d.2).1 (fun _ => (BinaryRational.zero,1))
      (fun _ => zero_stored) (fun _ => le_rfl) d.1 d.2
    simp only [findAvoiding,List.length_cons]
    split <;> unfold findAvoidingBound at * <;> nlinarith

def dispatchBound (n D B : ℕ) : ℕ := 26*D+zeroMaskBound n B+findAvoidingBound n D+9

theorem dispatch_charge (adjacency : Adjacency n) (ds : List (Pair n))
    (c : Row n) (hc : ∀ i, StoredBounded (get c i) B) :
    (dispatch adjacency ds c).2 ≤ dispatchBound n ds.length B := by
  have he := emptyDemand_charge adjacency ds
  have hz := zeroMask_charge c hc
  have hf := findAvoiding_charge adjacency (zeroMask c).1 ds
  unfold dispatch
  dsimp only
  split
  · unfold dispatchBound; omega
  · split <;> unfold dispatchBound <;> omega

theorem positiveIndices_length (c : Row m) (is : List (Fin m)) :
    (positiveIndices c is).1.length ≤ is.length := by
  induction is with
  | nil => simp [positiveIndices]
  | cons i is ih =>
    simp only [positiveIndices,List.length_cons]
    split <;> simp only [List.length_cons] <;> omega

theorem positiveIndices_charge (c : Row m) (hc : ∀ i, StoredBounded (get c i) B)
    (is : List (Fin m)) :
    (positiveIndices c is).2 ≤ is.length*(4*(B+1)+15)+1 := by
  induction is with
  | nil => simp [positiveIndices]
  | cons i is ih =>
    have hz := isZero_charge (hc i)
    simp only [positiveIndices,List.length_cons,read_value,read_charge]
    split <;> nlinarith

def minimumPositiveBound (m B : ℕ) : ℕ := m*(4*(B+1)+23)+argminBound m B 7+5

theorem minimumPositive_charge (c : Row m) (hc : ∀ i, StoredBounded (get c i) B) :
    (minimumPositive c).2 ≤ minimumPositiveBound m B := by
  have hi := positiveIndices_charge c hc (List.finRange m)
  have hl := positiveIndices_length c (List.finRange m)
  simp only [List.length_finRange] at hi hl
  have ha := argmin_charge (read c) (positiveIndices c (List.finRange m)).1
    (fun i _ => ⟨hc i,by simp [read_charge]⟩)
  have hm := argminBound_mono (B := B) (C := 7) hl
  unfold minimumPositive minimumPositiveBound
  nlinarith

end DirectedFlowCutGap.BinaryFractionalDispatchBounds
