import DirectedFlowCutGap.PackingRunCallLift

namespace DirectedFlowCutGap.PackingRun
open BinaryArithmetic BinaryRational BinaryFractionalRows

def startWidth (n B : ℕ) : ℕ :=
  PackingStart.initialWidth B+PackingStart.bestWidth n B+
    PackingGuard.objectiveWidth n (PackingStart.bestWidth n B)+B+2

theorem base_le_start (n B : ℕ) : B≤startWidth n B := by unfold startWidth;omega

theorem start_widths {n : ℕ} (capacity : Row n) (delta : Fraction) (oracle : BinaryFractionalCore.Oracle n)
    (B : ℕ) (scalar : StoredBounded delta B) (caps : ∀ x∈capacity.toList,StoredBounded x B) :
    (∀ x∈(BinaryFractionalCore.start capacity delta oracle).1.weights.toList,StoredBounded x (startWidth n B)) ∧
    StoredBounded (BinaryFractionalCore.start capacity delta oracle).1.bestCost (startWidth n B) ∧
    StoredBounded (BinaryFractionalCore.start capacity delta oracle).1.total (startWidth n B) ∧
    (∀ x∈(BinaryFractionalCore.start capacity delta oracle).1.loads.toList,StoredBounded x (startWidth n B)) := by
  let y := (initial capacity delta).1
  let q := (oracle y).1
  have weights := PackingStart.initial_width capacity delta B scalar caps
  have normalized := PackingStart.best_width y q.mask (PackingStart.initialWidth B) weights
  have small : B≤PackingStart.bestWidth n B := by
    unfold PackingStart.bestWidth NormalizedRow.scalarWidth PackingStart.initialWidth
    nlinarith
  have capBig : ∀ x∈capacity.toList,StoredBounded x (PackingStart.bestWidth n B) :=
    fun x hx => PackingIteration.bounded_mono (caps x hx) small
  have cost := PackingGuard.objective_width capacity.toList (BinaryFractionalRows.normalized y q.mask).1.toList
    (PackingStart.bestWidth n B) (by simp) capBig normalized
  rw [ObjectiveRow.result_eq_objective] at cost
  simp only [Vector.length_toList] at cost
  have hi : PackingStart.initialWidth B≤startWidth n B := by unfold startWidth;omega
  have hc : PackingGuard.objectiveWidth n (PackingStart.bestWidth n B)≤startWidth n B := by unfold startWidth;omega
  have hz : StoredBounded zero (startWidth n B) := by
    have h : 1≤startWidth n B := by unfold startWidth;omega
    simpa only [StoredBounded,zero,List.length_nil,List.length_cons] using And.intro (Nat.zero_le _) h
  refine ⟨?_,?_,hz,?_⟩
  · exact fun x hx => PackingIteration.bounded_mono (weights x hx) hi
  · exact PackingIteration.bounded_mono cost hc
  · intro x hx
    have h : x=zero := (List.mem_replicate.mp (show x∈List.replicate n zero from by simpa only
      [BinaryFractionalCore.start,Vector.toList_replicate] using hx)).2
    rw [h]
    exact hz
end DirectedFlowCutGap.PackingRun
