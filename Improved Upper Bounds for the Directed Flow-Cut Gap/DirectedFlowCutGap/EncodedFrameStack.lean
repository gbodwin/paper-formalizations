import DirectedFlowCutGap.PackedArrayReservations

/-! Each pending frame has one saved value and one link. The pushes occur
in reverse stack order and the pops follow the actual fold order. -/
namespace DirectedFlowCutGap.EncodedFrameStack

open EncodedArrayStorage

def push {A : Type} (saved : A) : List (Instruction A) := [.reserve 2,.store saved,.storeLink,.advance]

def pop {A : Type} (saved : A) : List (Instruction A) := [.branch,.load saved,.loadLink,.advance]

def trace {A : Type} (pending : List A) : List (Instruction Unit) :=
  ((pending.reverse.flatMap push)++(pending.flatMap pop)).map PackedArraySchedule.shape

private theorem pushes {A : Type} (values : List A) :
    (values.flatMap push).length=4*values.length ∧ fresh (values.flatMap push)=2*values.length := by
  induction values with
  | nil => exact ⟨rfl,rfl⟩
  | cons head tail ih =>
    obtain ⟨copies,cells⟩ := ih
    change (push head++tail.flatMap push).length=4*(tail.length+1) ∧
      fresh (push head++tail.flatMap push)=2*(tail.length+1)
    simp only [List.length_append,fresh_append,copies,cells]
    have firstWork : (push head).length=4 := rfl
    have firstCells : fresh (push head)=2 := rfl
    constructor <;> omega

private theorem pops {A : Type} (values : List A) :
    (values.flatMap pop).length=4*values.length ∧ fresh (values.flatMap pop)=0 := by
  induction values with
  | nil => exact ⟨rfl,rfl⟩
  | cons head tail ih =>
    obtain ⟨copies,cells⟩ := ih
    change (pop head++tail.flatMap pop).length=4*(tail.length+1) ∧ fresh (pop head++tail.flatMap pop)=0
    simp only [List.length_append,fresh_append,copies,cells,Nat.add_zero]
    have lastWork : (pop head).length=4 := rfl
    have lastCells : fresh (pop head)=0 := rfl
    constructor <;> omega

theorem counts {A : Type} (pending : List A) :
    (trace pending).length=8*pending.length ∧ fresh (trace pending)=2*pending.length := by
  obtain ⟨enterWork,enterSpace⟩ := pushes pending.reverse
  obtain ⟨exitWork,exitSpace⟩ := pops pending
  simp only [List.length_reverse] at enterWork enterSpace
  constructor
  · simp only [trace,List.length_map,List.length_append,enterWork,exitWork]
    rw [← Nat.add_mul]
  · simp only [trace,PackedArraySchedule.shape_extent,fresh_append,enterSpace,exitSpace,Nat.add_zero]

end DirectedFlowCutGap.EncodedFrameStack
