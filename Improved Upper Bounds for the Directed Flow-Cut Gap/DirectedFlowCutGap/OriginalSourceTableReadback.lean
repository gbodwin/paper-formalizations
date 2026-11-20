import DirectedFlowCutGap.OriginalSourceFraming
import DirectedFlowCutGap.PhysicalCoverAccess

/-! Read the three retained original tables through their binary heap roots.
The readback charge includes every reference lookup and word traversal. -/
namespace DirectedFlowCutGap.OriginalSourceTableReadback

open BinaryArithmetic ImmutableReferenceSimulation PhysicalCoverAccess
open WordPairTableRead (Table)

def pair (heap : Heap) (root : Bits) : Read (Bits × Bits) := do
  let .pair left right ← access heap root | Read.failure
  let a ← readWord heap left
  let b ← readWord heap right
  pure (a,b)

def table (heap : Heap) (root : Bits) : Read (List (Bits × Bits)) :=
  readList heap (pair heap) heap.length root

private theorem access_nil {heap : Heap} {root : Bits}
    (rep : (eraseHeap heap)[value root]? = some .nil) : (access heap root).1=some .nil := by
  have h := (lookup_refines root heap).trans rep
  change Option.map eraseCell (access heap root).1=some .nil at h
  cases hc : (access heap root).1 with
  | none => rw [hc] at h; cases h
  | some cell =>
    rw [hc] at h
    cases cell with
    | nil => rfl
    | flag _ | pair _ _ => cases h

private theorem access_pair {heap : Heap} {root : Bits} {num den : ℕ}
    (rep : (eraseHeap heap)[value root]? = some (.pair num den)) :
    ∃ a b, (access heap root).1=some (.pair a b) ∧ value a=num ∧ value b=den := by
  have h := (lookup_refines root heap).trans rep
  change Option.map eraseCell (access heap root).1=some (.pair num den) at h
  cases hc : (access heap root).1 with
  | none => rw [hc] at h; cases h
  | some cell =>
    rw [hc] at h
    cases cell with
    | nil | flag _ => cases h
    | pair a b =>
        have he : value a=num ∧ value b=den := Cell.pair.inj (Option.some.inj h)
        exact ⟨a,b,rfl,he⟩

private theorem pair_value {heap : Heap} {root : Bits} {num den : ℕ} {a b : Bits}
    (rep : (eraseHeap heap)[value root]? = some (.pair num den))
    (left : BooleanTableRead.BoolList (eraseHeap heap) num a)
    (right : BooleanTableRead.BoolList (eraseHeap heap) den b) : (pair heap root).1=some (a,b) := by
  obtain ⟨x,y,found,vx,vy⟩ := access_pair rep
  have lhs : (readWord heap x).1=some a := by
    rw [readWord_value,vx]
    exact PhysicalCoverReader.readWord_eq left
  have rhs : (readWord heap y).1=some b := by
    rw [readWord_value,vy]
    exact PhysicalCoverReader.readWord_eq right
  simp only [pair,Read.bind_value,found,lhs,rhs,Option.bind_some,Read.pure_value]

private theorem length_lt {heap : NaturalHeap} {root : ℕ} {rows : List (Bits × Bits)}
    (rep : Table heap root rows) : rows.length<heap.length := by
  apply PhysicalCoverReader.spine_short (root:=root)
  induction rep with
  | nil atNil => exact .nil atNil
  | cons atRoot _ _ _ _ tail => exact .cons atRoot tail

private theorem readList_value {heap : Heap} {root : ℕ} {rows : List (Bits × Bits)}
    (rep : Table (eraseHeap heap) root rows) (fuel : ℕ) (size : rows.length<fuel)
    (bits : Bits) (addr : value bits=root) :
    (readList heap (pair heap) fuel bits).1=some rows := by
  induction rep generalizing fuel bits with
  | nil atNil =>
      cases fuel with
      | zero => simp at size
      | succ fuel =>
          have h := access_nil (show (eraseHeap heap)[value bits]?=some .nil by rwa [addr])
          simp only [readList,readListWith,Read.bind_value,h,Option.bind_some,Read.pure_value]
  | @cons root item tail num den a b rest atRoot atItem left right children ih =>
      cases fuel with
      | zero => simp at size
      | succ fuel =>
          obtain ⟨x,y,found,vx,vy⟩ := access_pair (show (eraseHeap heap)[value bits]?=some (.pair item tail) by rwa [addr])
          have h := pair_value (show (eraseHeap heap)[value x]?=some (.pair num den) by rwa [vx]) left right
          have small : rest.length<fuel := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using size
          have reads := ih fuel small y vy
          simp only [readList] at reads
          simp only [readList,readListWith,Read.bind_value,found,Option.bind_some,h,reads,Read.pure_value]

theorem table_value {heap : Heap} {root : Bits} {rows : List (Bits × Bits)}
    (rep : Table (eraseHeap heap) (value root) rows) : (table heap root).1=some rows := by
  have h := length_lt rep
  simp only [eraseHeap,List.length_map] at h
  exact readList_value rep _ h _ rfl

theorem pair_paid {heap : Heap} {root : Bits} {B : ℕ} (hh : heap.Bounded B) (hr : root.length≤B) :
    (pair heap root).2 ≤ cellBound heap.length B+wordBound heap.length B+wordBound heap.length B := by
  rw [Nat.add_assoc]
  unfold pair
  apply Read.bind_bound (access_charge hh hr)
  intro cell found
  cases cell with
  | nil | flag _ => exact Nat.zero_le _
  | pair a b =>
      have pointers : a.length≤B ∧ b.length≤B := lookup_bounded hh found
      apply Read.bind_bound (readWord_charge hh pointers.1)
      intro x hx
      apply (Read.bind_bound (readWord_charge hh pointers.2) (later:=0) (fun _ _ => Nat.le_refl 0)).trans
      omega

def tableBudget {R : Type*} [Semiring R] (records width : R) : R :=
  let cell := 64*(records+1)*(width+1)
  let word := records*(cell+cell)
  records*(cell+(cell+word+word))

theorem table_paid {heap : Heap} {root : Bits} {B : ℕ} (hh : heap.Bounded B) (hr : root.length≤B) :
    (table heap root).2≤tableBudget heap.length B :=
  readList_charge hh (fun _ hw => pair_paid hh hw) _ _ hr

end DirectedFlowCutGap.OriginalSourceTableReadback
