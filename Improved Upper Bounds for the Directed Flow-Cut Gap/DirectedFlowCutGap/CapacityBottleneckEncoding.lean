import DirectedFlowCutGap.CapacityBottleneckSelection

namespace DirectedFlowCutGap.CapacityBottleneck
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def EncodesSlot {n : ℕ} (label : Fin n → Bits) (capacity : Row n) (mask : Vector Bool n)
    (x : Slot) (i : Fin n) : Prop :=
  x.word=label i ∧ x.score=get capacity i ∧ x.enabled=mask[i.val]

theorem parallel_of_lists {n : ℕ} (label : Fin n → Bits) (capacity : Row n) (mask : Vector Bool n)
    {heap : NaturalHeap} {m v t : ℕ} {is : List (Fin n)}
    (flags : BoolList heap m (is.map fun i => mask[i.val]))
    (vertices : GraphDiscoveryProgram.Vertices heap v (is.map label))
    (table : WordPairTableRead.Table heap t (is.map fun i => ((get capacity i).num,(get capacity i).den))) :
    ∃ xs,Parallel heap m v t xs ∧ List.Forall₂ (EncodesSlot label capacity mask) xs is := by
  induction is generalizing m v t with
  | nil =>
    cases flags with
    | nil hm =>
      cases vertices with
      | nil hv =>
        cases table with
        | nil ht => exact ⟨[],.nil hm hv ht,.nil⟩
  | cons i is ih =>
    cases flags with
    | @cons _ f mt _ _ hm hf hflags =>
      cases vertices with
      | @cons _ word vt _ _ hv hw hvertices =>
        cases table with
        | @cons _ score tt num den _ _ _ ht hr hn hd htable =>
          obtain ⟨xs,hxs,henc⟩ := ih hflags hvertices htable
          exact ⟨⟨mask[i.val],label i,word,get capacity i⟩::xs,
            .cons hm hf hv hw ht ⟨num,den,hr,hn,hd⟩ hxs,.cons ⟨rfl,rfl,rfl⟩ henc⟩

def EncodesItem {n : ℕ} (heap : NaturalHeap) (label : Fin n → Bits) (capacity : Row n)
    (x : RetainedArgminProgram.Item) (i : Fin n) : Prop :=
  x.score=get capacity i ∧ BoolList heap x.payload (label i)

theorem items_encode {n : ℕ} (label : Fin n → Bits) (capacity : Row n) (mask : Vector Bool n)
    {heap : NaturalHeap} {m v t : ℕ} {xs : List Slot} {is : List (Fin n)}
    (input : Parallel heap m v t xs) (encoded : List.Forall₂ (EncodesSlot label capacity mask) xs is)
    (next : ℕ) :
    List.Forall₂ (EncodesItem heap label capacity) (items next xs) (is.filter fun i => mask[i.val]) := by
  induction encoded generalizing m v t next with
  | nil => exact .nil
  | @cons x i xs is hx _ ih =>
    cases input with
    | cons hm hf hv hw ht hq tail =>
      obtain ⟨hwrd,hscore,hflag⟩ := hx
      have htail := ih tail (next+2)
      cases he : x.enabled with
      | false =>
        have hi : mask[i.val]=false := hflag.symm.trans he
        simpa [items,he,hi] using htail
      | true =>
        have hi : mask[i.val]=true := hflag.symm.trans he
        simpa [items,he,hi] using List.Forall₂.cons
          (show EncodesItem heap label capacity ⟨x.score,x.vertexRoot,next+cells xs+3⟩ i from
            ⟨hscore,by simpa [hwrd] using hw⟩) htail

theorem select_identity (xs : List RetainedArgminProgram.Item) :
    RetainedArgminProgram.select xs=
      (BinaryFractionalGraphOracle.argmin (fun x : RetainedArgminProgram.Item => (x.score,0)) xs).1 := by
  have hi : RetainedGraphArgmin.item (fun x : RetainedArgminProgram.Item => (x.score,0))
      RetainedArgminProgram.Item.payload RetainedArgminProgram.Item.address=id := by
    funext x
    cases x
    rfl
  have h := RetainedGraphArgmin.value_refines (fun x : RetainedArgminProgram.Item => (x.score,0))
    RetainedArgminProgram.Item.payload RetainedArgminProgram.Item.address xs
  simpa only [hi,List.map_id,Option.map_id,id_eq] using h

theorem selected_encode {n : ℕ} (label : Fin n → Bits) (capacity : Row n) (mask : Vector Bool n)
    {heap : NaturalHeap} {m v t : ℕ} {xs : List Slot} {is : List (Fin n)}
    (input : Parallel heap m v t xs) (encoded : List.Forall₂ (EncodesSlot label capacity mask) xs is)
    (next : ℕ) :
    DemandCollection.OptionRelated (EncodesItem heap label capacity)
      (RetainedArgminProgram.select (items next xs))
      (BinaryFractionalGraphOracle.argmin (BinaryFractionalGraphOracle.read capacity)
        (is.filter fun i => mask[i.val])).1 := by
  rw [select_identity]
  exact DemandCollection.argminFrom_related (EncodesItem heap label capacity)
    (fun x => (x.score,0)) (BinaryFractionalGraphOracle.read capacity)
    (fun _ _ h => by simpa only [BinaryFractionalGraphOracle.read_value] using h.1)
    (items_encode label capacity mask input encoded next) none none trivial

end DirectedFlowCutGap.CapacityBottleneck
