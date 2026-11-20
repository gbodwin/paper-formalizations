import DirectedFlowCutGap.PackedArrayReservations
import DirectedFlowCutGap.BinaryNaturalView
import DirectedFlowCutGap.EncodedUnitCostReplication

/-! Materialize the ordered index list with a binary index and a binary
allocation pointer. Each node stores one index word and an optional link. -/
namespace DirectedFlowCutGap.BinaryIndexList

open BinaryArithmetic EncodedArrayStorage

structure Node where
  base : Bits
  index : Bits
  link : Option Bits
  deriving Repr

structure Listing where
  nodes : List Node
  stop : Bits
  charge : ℕ
  deriving Repr

def build (index start : Bits) : ℕ → Listing
  | 0 => ⟨[],start,1⟩
  | k+1 =>
    let address := addCanonical start [false,true]
    let next := addCanonical index [true]
    let tail := build next.1 address.1 k
    let link := tail.nodes.head?.map Node.base
    ⟨⟨start,index,link⟩::tail.nodes,tail.stop,tail.charge+address.2+next.2+10⟩

private theorem plus_index (index : Bits) : value (addCanonical index [true]).1=value index+1 :=
  (canonical_values index [true]).1

private theorem plus_address (start : Bits) : value (addCanonical start [false,true]).1=value start+2 :=
  (canonical_values start [false,true]).1

def linked : List Node → Prop
  | [] => True
  | node::later => node.link=later.head?.map Node.base ∧ linked later

theorem list_values (index start : Bits) (count : ℕ) :
    let out := build index start count
    out.nodes.map (fun entry => value entry.index)=List.range' (value index) count ∧
      out.nodes.map (fun entry => value entry.base)=List.range' (value start) count 2 ∧
      value out.stop=value start+2*count ∧ linked out.nodes := by
  induction count generalizing index start with
  | zero => simp [build,linked]
  | succ k ih =>
    obtain ⟨indices,places,extent,links⟩ := ih (addCanonical index [true]).1 (addCanonical start [false,true]).1
    refine ⟨?_,?_,?_,?_⟩
    · simp only [build,List.map_cons,List.range'_succ,indices,plus_index]
    · simp only [build,List.map_cons,List.range'_succ,places,plus_address]
    · simp only [build,extent,plus_address,Nat.mul_succ]
      omega
    · exact ⟨rfl,links⟩

def reservations (count : ℕ) : List (Instruction Unit) := List.replicate count (.reserve 2)

private theorem reservation_values (start count : ℕ) :
    allocateTrace start (reservations count)=(start+2*count,(List.range' start count 2).map (fun base => (base,2))) := by
  induction count generalizing start with
  | zero => simp [reservations,allocateTrace]
  | succ k ih =>
    simp only [reservations,List.replicate_succ,allocateTrace,List.range'_succ,List.map_cons]
    rw [show List.replicate k (Instruction.reserve (α := Unit) 2)=reservations k from rfl,ih]
    simp only [Nat.mul_succ]
    congr 1
    omega

theorem placed (index start : Bits) (count : ℕ) :
    let out := build index start count
    (value out.stop,out.nodes.map (fun n => (value n.base,2)))=allocateTrace (value start) (reservations count) := by
  obtain ⟨_,places,extent,_⟩ := list_values index start count
  rw [reservation_values]
  dsimp only
  rw [extent,← places,List.map_map,Function.comp_def]


/-- Increments of the index and address plus the per-node link and record work. -/
def chargeBound (count width : ℕ) : ℕ := count*(64*(width+2)+10)+1

theorem charge_le (index start : Bits) (count : ℕ) {B : ℕ}
    (first : index.length≤B) (address : start.length≤B)
    (indexEnd : (value index+count).size≤B) (addressEnd : (value start+2*count).size≤B) :
    (build index start count).charge≤chargeBound count B := by
  induction count generalizing index start with
  | zero => simp [build,chargeBound]
  | succ k ih =>
    let next := addCanonical index [true]
    let place := addCanonical start [false,true]
    have valueIndex : value next.1=value index+1 := plus_index _
    have valueAddress : value place.1=value start+2 := plus_address _
    have indexWidth : next.1.length=(value index+1).size := (canonical_values index [true]).2.2.1
    have addressWidth : place.1.length=(value start+2).size := (canonical_values start [false,true]).2.2.1
    have two : 2≤B := (Nat.size_le_size (show 2≤value start+2*(k+1) by omega)).trans addressEnd
    have added : place.2≤32*(B+2) := (canonical_charges address (show ([false,true] : Bits).length≤B from two)).1
    have one : ([true] : Bits).length ≤ B := (show ([true] : Bits).length ≤ 2 from by decide).trans two
    have incremented : next.2≤32*(B+2) := (canonical_charges first one).1
    have laterIndex : (value next.1+k).size≤B := by
      rw [valueIndex,show value index+1+k=value index+(k+1) by omega]
      exact indexEnd
    have laterAddress : (value place.1+2*k).size≤B := by
      rw [valueAddress,show value start+2+2*k=value start+2*(k+1) by omega]
      exact addressEnd
    have seenIndex : next.1.length≤B := by
      rw [indexWidth,← valueIndex]
      exact (Nat.size_le_size (Nat.le_add_right _ _)).trans laterIndex
    have seenAddress : place.1.length≤B := by
      rw [addressWidth,← valueAddress]
      exact (Nat.size_le_size (Nat.le_add_right _ _)).trans laterAddress
    have tail := ih next.1 place.1 seenIndex seenAddress laterIndex laterAddress
    simp only [build,chargeBound,Nat.succ_mul] at tail ⊢
    change (build next.1 place.1 k).charge+place.2+next.2+10 ≤ _
    omega

def forMask {n : ℕ} (selected : Vector Bool n) (start : ℕ) : Listing :=
  build [] start.bits selected.toArray.size

theorem forMask_values {n : ℕ} (selected : Vector Bool n) (start : ℕ) :
    (forMask selected start).nodes.map (fun cell => value cell.index)=
      (EncodedUnitCostReplication.retainedIndices selected).map Fin.val := by
  have observe := (list_values [] start.bits selected.toArray.size).1
  change (forMask selected start).nodes.map (fun cell => value cell.index)=_ at observe
  rw [observe]
  unfold EncodedUnitCostReplication.retainedIndices
  rw [List.map_map]
  apply List.ext_getElem
  · simp only [List.length_range',List.length_map,List.length_finRange]
  · intro i h1 h2
    simp only [List.getElem_range',List.getElem_map,List.getElem_finRange,Function.comp_def,
      Fin.val_cast,value,zero_add,Nat.one_mul]

theorem forMask_charge {n : ℕ} (selected : Vector Bool n) (start : ℕ) :
    (forMask selected start).charge ≤ chargeBound n (max n.size (start+2*n).size) := by
  have width : selected.toArray.size=n := Vector.size_toArray selected
  unfold forMask
  rw [width]
  exact charge_le [] start.bits n (Nat.zero_le _)
    (by rw [Nat.size_eq_bits_len]; exact (Nat.size_le_size (Nat.le_add_right _ _)).trans (Nat.le_max_right _ _))
    (by simpa only [value,Nat.zero_add] using Nat.le_max_left n.size (start+2*n).size)
    (by simpa only [value_bits] using Nat.le_max_right n.size (start+2*n).size)


/-- Read the represented indices as the original bounded cursor type. -/
def decode (n : ℕ) (nodes : List Node) : Option (List (Fin n)) :=
  nodes.mapM fun node => if h : value node.index<n then some ⟨value node.index,h⟩ else none

private theorem decode_matches {n : ℕ} (nodes : List Node) (indices : List (Fin n))
    (observed : nodes.map (fun node => value node.index)=indices.map Fin.val) : decode n nodes=some indices := by
  induction nodes generalizing indices with
  | nil =>
    cases indices with
    | nil => rfl
    | cons first rest => cases observed
  | cons node rest ih =>
    cases indices with
    | nil => simp only [List.map_cons,List.map_nil,List.cons_ne_nil] at observed
    | cons i tail =>
      obtain ⟨index,restValue⟩ := List.cons.inj (show value node.index::rest.map (fun cell => value cell.index)=
        i.val::tail.map Fin.val from observed)
      have fits : value node.index<n := index.symm ▸ i.isLt
      have first : (⟨value node.index,fits⟩ : Fin n)=i := Fin.ext index
      simp only [decode,List.mapM_cons,dite_eq_left fits,first]
      have after := ih tail restValue
      unfold decode at after
      rw [after]
      rfl

theorem forMask_indices {n : ℕ} (selected : Vector Bool n) (start : ℕ) :
    decode n (forMask selected start).nodes=some (EncodedUnitCostReplication.retainedIndices selected) :=
  decode_matches _ _ (forMask_values selected start)

/-- Compare the stored word with the actual encoded array length before
returning a typed cursor. An invalid node stops the walk. -/
def decodeWithWork {n : ℕ} (limit : Bits) (represents : value limit=n) :
    List Node → Option (List (Fin n)) × ℕ
  | [] => (some [],1)
  | node::later =>
    let observed := BinaryNaturalView.decode node.index
    let test := BinaryArithmetic.compare node.index limit
    if fits : test.less=true then
      let index : Fin n := ⟨observed.1,by
        rw [BinaryNaturalView.decode_value,← represents]
        exact (compare_spec node.index limit).1.mp fits⟩
      let tail := decodeWithWork limit represents later
      (tail.1.map (index::·),observed.2+test.steps+tail.2+8)
    else
      (none,observed.2+test.steps+8)

theorem decodeWithWork_value {n : ℕ} (limit : Bits) (represents : value limit=n) (nodes : List Node) :
    (decodeWithWork limit represents nodes).1=decode n nodes := by
  induction nodes with
  | nil => rfl
  | cons node later ih =>
    have accepted : (BinaryArithmetic.compare node.index limit).less=true ↔ value node.index<n := by
      rw [(compare_spec node.index limit).1,represents]
    by_cases h : value node.index<n
    · rw [decodeWithWork,dite_eq_left (accepted.mpr h)]
      change (decodeWithWork limit represents later).1.map
        (fun tail => (⟨(BinaryNaturalView.decode node.index).1,_⟩ : Fin n)::tail) = _
      rw [ih]
      simp only [decode,List.mapM_cons,dite_eq_left h]
      have index : (⟨(BinaryNaturalView.decode node.index).1,
          (show (BinaryNaturalView.decode node.index).1<n by
            rw [BinaryNaturalView.decode_value]; exact h)⟩ : Fin n)=⟨value node.index,h⟩ :=
        Fin.ext (BinaryNaturalView.decode_value _)
      rw [index]
      cases rest : later.mapM (m := Option)
          (fun cell => if h : value cell.index<n then some (⟨value cell.index,h⟩ : Fin n) else none) <;> rfl
    · rw [decodeWithWork,dite_eq_right (accepted.not.mpr h)]
      simp only [decode,List.mapM_cons,dite_eq_right h]
      rfl

def decodeStep {R : Type*} [Semiring R] (B : R) : R := 16*(B+1)^2+16*(B+1)+8

theorem decodeWithWork_paid {n B : ℕ} (limit : Bits) (represents : value limit=n) (nodes : List Node)
    (lengthFits : limit.length≤B) (indexFits : ∀ node∈nodes, node.index.length≤B) :
    (decodeWithWork limit represents nodes).2 ≤ nodes.length*decodeStep B+1 := by
  induction nodes with
  | nil => simp [decodeWithWork]
  | cons node later ih =>
    have width := indexFits node List.mem_cons_self
    have natural := (BinaryNaturalView.decode_paid node.index).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right width 1) 2))
    have compared := (compare_spec node.index limit).2.2.trans
      (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (max_le width lengthFits) 1))
    have tail := ih (fun next mem => indexFits next (List.mem_cons_of_mem _ mem))
    have per : (BinaryNaturalView.decode node.index).2+(BinaryArithmetic.compare node.index limit).steps+8 ≤ decodeStep B := by
      unfold decodeStep
      omega
    rw [decodeWithWork]
    split <;> simp only [List.length_cons,Nat.add_mul,Nat.one_mul] <;> omega

private theorem build_width (index start : Bits) (count : ℕ) {B : ℕ}
    (first : index.length≤B) (last : (value index+count).size≤B) :
    ∀ node∈(build index start count).nodes, node.index.length≤B := by
  induction count generalizing index start with
  | zero => simp [build]
  | succ k ih =>
    intro node mem
    simp only [build,List.mem_cons] at mem
    rcases mem with equal | tail
    · subst node
      exact first
    · let next := addCanonical index [true]
      have valueNext : value next.1=value index+1 := plus_index _
      have lastNext : (value next.1+k).size≤B := by
        rw [valueNext,show value index+1+k=value index+(k+1) by omega]
        exact last
      have widthNext : next.1.length≤B := by
        change (addCanonical index [true]).1.length≤B
        rw [(canonical_values index [true]).2.2.1]
        exact (Nat.size_le_size (show value index+value [true]≤value next.1+k by
          rw [valueNext]; simp only [value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero]; omega)).trans lastNext
      exact ih next.1 (addCanonical start [false,true]).1 widthNext lastNext node tail

theorem retained_length {n : ℕ} (selected : Vector Bool n) :
    (EncodedUnitCostReplication.retainedIndices selected).length=n := by
  simp [EncodedUnitCostReplication.retainedIndices]

private theorem mask_width {n : ℕ} (selected : Vector Bool n) (start : ℕ) :
    ∀ node∈(forMask selected start).nodes, node.index.length≤n.size := by
  simpa only [forMask,value,Nat.zero_add,Vector.size_toArray] using
    build_width ([] : Bits) start.bits selected.toArray.size (Nat.zero_le n.size)
      (by simp only [value,Nat.zero_add,Vector.size_toArray,le_rfl])

def checkedMask {n : ℕ} (selected : Vector Bool n) (start : ℕ) : Option (List (Fin n)) × ℕ :=
  let limit := BinaryNaturalView.encode selected.toArray.size
  let address := BinaryNaturalView.encode start
  let listing := build [] address.1 selected.toArray.size
  let checked := decodeWithWork limit.1
    ((BinaryNaturalView.encode_value _).trans selected.size_toArray) listing.nodes
  (checked.1,limit.2+address.2+listing.charge+checked.2+4)

theorem checkedMask_value {n : ℕ} (selected : Vector Bool n) (start : ℕ) :
    (checkedMask selected start).1=some (EncodedUnitCostReplication.retainedIndices selected) := by
  unfold checkedMask
  dsimp only
  rw [decodeWithWork_value,BinaryNaturalView.encode_bits]
  exact forMask_indices selected start

def checkedBudget {R : Type*} [Semiring R] (n B : R) : R :=
  n*(64*(B+2)+10+decodeStep B)+32*(B+1)^2+6

theorem checkedMask_paid {n B : ℕ} (selected : Vector Bool n) (start : ℕ)
    (width : n.size≤B) (address : (start+2*n).size≤B) :
    (checkedMask selected start).2 ≤ checkedBudget n B := by
  have startFit := (Nat.size_le_size (Nat.le_add_right start (2*n))).trans address
  have first := (BinaryNaturalView.encode_paid selected.toArray.size).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right
      (by simpa only [Vector.size_toArray] using width) 1) 2))
  have second := (BinaryNaturalView.encode_paid start).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right startFit 1) 2))
  have listing : (forMask selected start).charge ≤ chargeBound n B := by
    apply (forMask_charge selected start).trans
    unfold chargeBound
    gcongr
    exact max_le width address
  have count : (forMask selected start).nodes.length=n := by
    have h := congrArg List.length (forMask_values selected start)
    simpa only [List.length_map,retained_length] using h
  let limit := (BinaryNaturalView.encode selected.toArray.size).1
  have cap : limit.length≤B := by
    simpa only [limit,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len,Vector.size_toArray] using width
  have read := decodeWithWork_paid limit
    ((BinaryNaturalView.encode_value _).trans selected.size_toArray) (forMask selected start).nodes cap
    (fun node mem => (mask_width selected start node mem).trans width)
  rw [count] at read
  unfold checkedMask
  dsimp only
  rw [BinaryNaturalView.encode_bits start]
  change (BinaryNaturalView.encode selected.toArray.size).2+(BinaryNaturalView.encode start).2+
    (forMask selected start).charge+(decodeWithWork limit
      ((BinaryNaturalView.encode_value _).trans selected.size_toArray) (forMask selected start).nodes).2+4 ≤ checkedBudget n B
  unfold chargeBound at listing
  unfold checkedBudget
  rw [Nat.mul_add]
  omega

end DirectedFlowCutGap.BinaryIndexList
