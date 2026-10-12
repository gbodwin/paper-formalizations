import DirectedFlowCutGap.PackingGuardExecution

namespace DirectedFlowCutGap.PackingStart
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem choice_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {q : BinaryFractionalCore.Choice n} (h : OracleChoice.StoredChoice heap root label q) (ext : NaturalHeap) :
    OracleChoice.StoredChoice (heap++ext) root label q := by
  obtain ⟨a,b,hp,ha,hb⟩ := h
  exact ⟨a,b,lookup_extend hp ext,boolList_extend ha ext,boolList_extend hb ext⟩

theorem events_extend {n : ℕ} {heap : NaturalHeap} {label : Fin n → Bits}
    {root : ℕ} {es : List (BinaryFractionalCore.Event n)}
    (h : EventList heap label root es) (ext : NaturalHeap) : EventList (heap++ext) label root es := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp he hc ha _ ih =>
    exact .cons (lookup_extend hp ext) (lookup_extend he ext)
      (choice_extend hc ext) (stored_extend ha ext) ih

theorem state_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {s : BinaryFractionalCore.State n} (h : StateRecord heap root label s) (ext : NaturalHeap) :
    StateRecord (heap++ext) root label s := by
  obtain ⟨a,b,c,d,e,f,k1,k2,k3,k4,h0,h1,h2,h3,h4,weights,best,cost,total,loads,events⟩ := h
  exact ⟨a,b,c,d,e,f,k1,k2,k3,k4,lookup_extend h0 ext,lookup_extend h1 ext,
    lookup_extend h2 ext,lookup_extend h3 ext,lookup_extend h4 ext,list_extend weights ext,
    list_extend best ext,stored_extend cost ext,stored_extend total ext,list_extend loads ext,
    events_extend events ext⟩
end DirectedFlowCutGap.PackingStart

namespace DirectedFlowCutGap.PackingGuard
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem state_guard {n : ℕ} (capacity : Row n) (s : BinaryFractionalCore.State n)
    (label : Fin n → Bits) {heap : NaturalHeap} {a b : ℕ}
    (row : StoredList heap a capacity.toList) (rep : PackingStart.StateRecord heap b label s)
    (next c d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ ext oneRoot objectiveRoot flagRoot,ext.length=cells capacity.toList s.weights.toList ∧
      NaturalRun program (steps capacity.toList s.weights.toList)
        (state heap next a b c d [] source 470) []
        (state (heap++ext) (next+ext.length) oneRoot objectiveRoot (next+1) flagRoot [] source 480) ∧
      (heap++ext)[flagRoot]?=some (.flag (BinaryRational.le one (objective capacity s.weights).1).1) ∧
      Context (heap++ext) (next+1) a b c ∧ PackingStart.StateRecord (heap++ext) b label s ∧
      Stored (heap++ext) objectiveRoot (objective capacity s.weights).1 := by
  have retained := rep
  obtain ⟨weights,best,cost,total,loads,events,k1,k2,k3,k4,current,_,_,_,_,values,_⟩ := rep
  obtain ⟨ext,oneRoot,objectiveRoot,flagRoot,len,high,flag,context,value⟩ :=
    guard_high row current values (by simp) next c d hn source
  rw [ObjectiveRow.result_eq_objective] at flag value
  exact ⟨ext,oneRoot,objectiveRoot,flagRoot,len,high,flag,context,PackingStart.state_extend retained ext,value⟩
end DirectedFlowCutGap.PackingGuard
