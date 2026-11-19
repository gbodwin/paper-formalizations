import DirectedFlowCutGap.CandidateRefreshProgram

/-! Bounds for referenced words and the growth of the immutable heap. -/

namespace DirectedFlowCutGap.ControllerWordWidth

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open RetainedGridState
open RetainedMassTableProgram (DataRows sum)

theorem word_unique {heap : NaturalHeap} {root : ℕ} {xs ys : Bits}
    (a : BoolList heap root xs) (b : BoolList heap root ys) : xs=ys := by
  induction a generalizing ys with
  | nil read =>
    cases b with
    | nil => rfl
    | cons pair _ _ => rw [read] at pair; cases pair
  | cons pair flag _ ih =>
    cases b with
    | nil read => rw [pair] at read; cases read
    | cons other test tail =>
      obtain ⟨rfl,rfl⟩ := Cell.pair.inj (Option.some.inj (pair.symm.trans other))
      have eq := Cell.flag.inj (Option.some.inj (flag.symm.trans test))
      rw [eq,ih tail]

private theorem address_lt {heap : NaturalHeap} {i : ℕ} {cell : Cell ℕ} (seen : heap[i]?=some cell) :
    i<heap.length := by
  by_contra outside
  rw [List.getElem?_eq_none (Nat.le_of_not_lt outside)] at seen
  cases seen

private theorem spine_addresses {heap : NaturalHeap} {root : ℕ} {word : Bits} (h : BoolList heap root word) :
    ∃ visited : Finset ℕ,visited⊆Finset.range heap.length ∧ visited.card=word.length+1 ∧
      ∀ p∈visited,∃ suffix,BoolList heap p suffix ∧ suffix.length≤word.length := by
  induction h with
  | @nil root read =>
    refine ⟨{root},?_,by simp,?_⟩
    · intro i mem
      have eq : i=root := Finset.mem_singleton.mp mem
      exact Finset.mem_range.mpr (eq ▸ address_lt read)
    · intro i mem
      have eq : i=root := Finset.mem_singleton.mp mem
      subst i
      exact ⟨[],.nil read,le_rfl⟩
  | @cons root head tail x xs read flag spine ih =>
    obtain ⟨visited,inside,count,values⟩ := ih
    have rootRep : BoolList heap root (x::xs) := .cons read flag spine
    have fresh : root∉visited := by
      intro repeated
      obtain ⟨suffix,rep,len⟩ := values root repeated
      rw [← word_unique rootRep rep] at len
      simp at len
    refine ⟨insert root visited,?_,?_,?_⟩
    · intro i mem
      rcases Finset.mem_insert.mp mem with rfl | inner
      · exact Finset.mem_range.mpr (address_lt read)
      · exact inside inner
    · simp [Finset.card_insert_of_notMem fresh,count]
    · intro i mem
      rcases Finset.mem_insert.mp mem with rfl | inner
      · exact ⟨x::xs,rootRep,le_rfl⟩
      · obtain ⟨suffix,rep,len⟩ := values i inner
        exact ⟨suffix,rep,len.trans (by simp)⟩

theorem word_length {heap : NaturalHeap} {root : ℕ} {word : Bits} (h : BoolList heap root word) :
    word.length+1≤heap.length := by
  obtain ⟨visited,inside,count,_⟩ := spine_addresses h
  simpa only [count,Finset.card_range] using Finset.card_le_card inside

private theorem tick_heap {C : ℕ} {program : Program C} {s : NaturalState C} {res : Result ℕ C}
    (step : tickNatural program s=some res) : res.state.heap.length ≤ s.heap.length+1 := by
  cases code : program s.pc <;> simp only [tickNatural,code] at step <;>
    repeat' first | split at step | injection step with he; subst res
  all_goals simp_all [allocateNatural]

theorem heap_bound {C k : ℕ} {program : Program C} {s out : NaturalState C} {events : List Event}
    (run : NaturalRun program k s events out) : out.heap.length ≤ s.heap.length+k := by
  induction run with
  | done => simp
  | step tick _ ih =>
    have grow := tick_heap tick
    omega

theorem extension_bound {C k : ℕ} {program : Program C} {s out : NaturalState C} {events : List Event}
    {ext : NaturalHeap} (run : NaturalRun program k s events out) (extension : out.heap=s.heap++ext) : ext.length≤k := by
  have h := heap_bound run
  rw [extension,List.length_append] at h
  omega

private theorem sum_width (rows : List (List Bits)) (flags cut : Bits) (B : ℕ)
    (align : ∀ ws∈rows,ws.length=cut.length) (widths : ∀ ws∈rows,∀ w∈ws,w.length≤B) :
    (sum cut flags rows).length ≤ B+cut.length+rows.length := by
  induction rows generalizing flags with
  | nil => cases flags <;> simp [sum]
  | cons ws rest ih =>
    cases flags with
    | nil => simp [sum]
    | cons active later =>
      have w := RetainedMassRowProgram.result_width ws cut B (widths ws List.mem_cons_self)
      rw [align ws List.mem_cons_self] at w
      have restAlign : ∀ y∈rest,y.length=cut.length := fun y hy => align y (List.mem_cons_of_mem _ hy)
      have restWidths : ∀ y∈rest,∀ t∈y,t.length≤B := fun y hy => widths y (List.mem_cons_of_mem _ hy)
      have t := ih later restAlign restWidths
      let first := RetainedMassRowProgram.sum ws cut
      let tail := sum cut later rest
      have bound : (addCanonical first tail).1.length ≤ max first.length tail.length+1 :=
        (trim_spec (add false first tail).1).2.2.1.trans (add_spec false first tail).2.1
      have maximum : max first.length tail.length≤B+cut.length+rest.length :=
        max_le (w.trans (Nat.le_add_right _ _)) t
      dsimp only [first,tail] at bound maximum
      simp only [sum,List.length_cons]
      split <;> omega

theorem mass_size {n B : ℕ} (counts : Family n) (active : PairFlags n) (cut : Flags n) (words : List (List Bits))
    (data : DataRows counts words) (widths : ∀ ws∈words,∀ w∈ws,w.length≤B) :
    (massNumerator active cut counts).size≤B+n+n*n := by
  let flags := (RetainedMassTableProgram.pairOrder n).map (flag active)
  have align : ∀ ws∈words,ws.length=cut.toList.length := by
    simpa only [Vector.length_toList] using RetainedMassTableProgram.data_aligned data
  have length := sum_width words flags cut.toList B align widths
  rw [Vector.length_toList,RetainedMassTableProgram.data_length data] at length
  have mass : value (sum cut.toList flags words)=massNumerator active cut counts :=
    (RetainedMassTableProgram.mass_value counts active cut data).trans (EncodedRoundingState.mass_value active cut counts)
  rw [← mass]
  exact (Nat.size_le.mpr (value_lt _)).trans length

end DirectedFlowCutGap.ControllerWordWidth
