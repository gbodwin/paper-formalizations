import DirectedFlowCutGap.ActualEnumeratedPacking
import DirectedFlowCutGap.SourceRowTableProgram

/-! The actual source-table decoder already allocates precisely the rational
record and demand-occurrence layouts consumed by the packing caller. These
lemmas interpret those same cells; they allocate nothing and change no word. -/
namespace DirectedFlowCutGap.PackingSource
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor WordPairTableRead DemandCollection

theorem capacity {heap : NaturalHeap} {p : ℕ} {rows : List Fraction}
    (h : Table heap p (IndexedRationalRead.fields rows)) :
    CanonicalRationalSum.StoredList heap p rows := by
  induction rows generalizing p with
  | nil =>
    cases h with
    | nil hp => exact .nil hp
  | cons x xs ih =>
    cases h with
    | cons hp hx hn hd ht =>
      exact .cons hp ⟨_,_,hx,hn,hd⟩ (ih ht)

/-- The original decoder's list cell is the occurrence address and its item
cell is the endpoint record, including duplicate and skipped demand queries. -/
theorem demand_occurrences {heap : NaturalHeap} {p : ℕ} {pairs : List (Bits × Bits)}
    (h : Table heap p pairs) :
    ∃ xs, DemandList heap p xs ∧
      List.Forall₂ (fun x pair => x.sourceWord=pair.1 ∧ x.targetWord=pair.2) xs pairs := by
  induction h with
  | nil hp => exact ⟨[],.nil hp,.nil⟩
  | @cons root item tail num den a b rest hp hv hn hd ht ih =>
    obtain ⟨xs,hxs,hpairs⟩ := ih
    exact ⟨⟨a,b,item,root⟩::xs,.cons rfl hp ⟨num,den,hv,hn,hd⟩ hxs,
      .cons ⟨rfl,rfl⟩ hpairs⟩

theorem encoded_demands {n : ℕ} (label : Fin n → Bits)
    {heap : NaturalHeap} {p : ℕ} (ds : List (BinaryFractionalWalkOracle.Pair n))
    (h : Table heap p (ds.map (fun d => (label d.1,label d.2)))) :
    ∃ xs, DemandList heap p xs ∧ List.Forall₂ (EncodesDemand label) xs ds := by
  obtain ⟨xs,hxs,hpairs⟩ := demand_occurrences h
  refine ⟨xs,hxs,?_⟩
  clear h hxs
  induction ds generalizing xs with
  | nil => cases hpairs; exact .nil
  | cons d ds ih =>
    cases hpairs with
    | cons hd ht => exact .cons hd (ih _ ht)

end DirectedFlowCutGap.PackingSource
