import DirectedFlowCutGap.VertexPreparationArrays

/-! Widen each retained preparation array to one common dimension bound. -/
namespace DirectedFlowCutGap.VertexPreparationBounds

open EncodedArrayStorage
open BinaryArrayNestedStorage (Grid gridSchedule copyBudget cellBudget copyBudget_mono cellBudget_mono
  flat_bounds grid_bounds)
open ArrayMaterializationLayout (flat copyList copy_counts)
open VertexGraphArrayLayout (graphCode graph_counts)
open VertexPreparationArrays (heavyCode portCode)

theorem flat_le {n bound : ℕ} (h : n≤bound) :
    (flat n).length ≤ copyBudget bound ∧ fresh (flat n) ≤ cellBudget bound := by
  obtain ⟨work,space⟩ := flat_bounds n
  exact ⟨work.trans (copyBudget_mono h),space.trans (cellBudget_mono h)⟩

private theorem grid_le {n bound : ℕ} (h : n≤bound) :
    (gridSchedule n n).length ≤ (bound+1)*copyBudget bound ∧
      fresh (gridSchedule n n) ≤ (bound+1)*cellBudget bound := by
  obtain ⟨work,space⟩ := grid_bounds n
  have grown := Nat.add_le_add_right h 1
  exact ⟨work.trans (Nat.mul_le_mul grown (copyBudget_mono h)),
    space.trans (Nat.mul_le_mul grown (cellBudget_mono h))⟩

theorem graph_le {n bound : ℕ} (h : n≤bound) :
    (graphCode n).length ≤ (bound+3)*copyBudget bound ∧
      fresh (graphCode n) ≤ (bound+3)*cellBudget bound := by
  obtain ⟨work,space⟩ := graph_counts n
  have grown := Nat.add_le_add_right h 3
  exact ⟨work.trans (Nat.mul_le_mul grown (copyBudget_mono h)),
    space.trans (Nat.mul_le_mul grown (cellBudget_mono h))⟩

theorem heavy {n m bound : ℕ} (hn : n≤bound) (hm : m≤bound) :
    (heavyCode n m).length ≤ (bound+6)*copyBudget bound+4*bound+4 ∧
      fresh (heavyCode n m) ≤ (bound+6)*cellBudget bound+bound+2 := by
  obtain ⟨maskWork,maskSpace⟩ := flat_le hn
  obtain ⟨labelWork,labelSpace⟩ := flat_le hm
  obtain ⟨graphWork,graphSpace⟩ := graph_le hm
  obtain ⟨copyWork,copySpace⟩ := copy_counts m
  simp only [heavyCode,List.length_append,fresh_append,copyWork,copySpace,Nat.add_mul] at graphWork graphSpace ⊢
  constructor <;> omega

theorem port {n m bound : ℕ} (h : 3*n≤bound) (hm : m≤bound) :
    (portCode n m).length ≤ (4*bound+10)*copyBudget bound+4*bound+4 ∧
      fresh (portCode n m) ≤ (4*bound+10)*cellBudget bound+bound+2 := by
  have hn : n≤bound := by omega
  obtain ⟨inputWork,inputSpace⟩ := flat_le hn
  obtain ⟨maskWork,maskSpace⟩ := flat_le h
  obtain ⟨gridWork,gridSpace⟩ := grid_le h
  obtain ⟨labelWork,labelSpace⟩ := flat_le hm
  obtain ⟨graphWork,graphSpace⟩ := graph_le hm
  obtain ⟨copyWork,copySpace⟩ := copy_counts m
  simp only [portCode,List.length_append,fresh_append,copyWork,copySpace,Nat.add_mul,Nat.mul_assoc,
    Nat.one_mul] at gridWork gridSpace graphWork graphSpace ⊢
  constructor <;> omega

end DirectedFlowCutGap.VertexPreparationBounds
