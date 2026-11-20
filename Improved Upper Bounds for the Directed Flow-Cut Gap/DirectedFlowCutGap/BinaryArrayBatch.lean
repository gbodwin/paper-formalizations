import DirectedFlowCutGap.CachedScalarRead
import DirectedFlowCutGap.PackedArrayReservations

/-! Fill one preallocated destination in order while adding each returned
callback fee. The loop computes its callback indexes by binary addition. -/
namespace DirectedFlowCutGap.BinaryArrayBatch

open BinaryArithmetic
open CachedScalarRead (sumMeasured sum_value sum_paid)

private structure Filled (A : Type) where
  data : Array A
  fee : ℕ
  work : ℕ

private def fill {A : Type} {m : ℕ} (callback : Fin m → (A × ℕ) × ℕ)
    (data : Array A) (cursor : Bits) (fee work : ℕ) : (left : ℕ) → value cursor+left=m → Filled A
  | 0, _ => ⟨data,fee,work+3⟩
  | left+1, position =>
      let index := DirectNaturalView.decode cursor
      have here : index.1=value cursor := by
        change (DirectNaturalView.decode cursor).1=value cursor
        rw [DirectNaturalView.decode_eq,BinaryNaturalView.decode_value]
      let result := callback ⟨index.1,by omega⟩
      let item := result.1
      let next := addCanonical cursor [true]
      have advance : value next.1+left=m := by
        rw [(canonical_values cursor [true]).1]
        simp only [value,Bool.toNat_true,Nat.add_zero,Nat.mul_zero]
        omega
      let charge := sumMeasured [fee,item.2]
      fill callback (data.push item.1) next.1 charge.1
        (work+index.2+next.2+charge.2+Nat.size left+cursor.length+10+result.2) left advance

private def suffix {A : Type} {m : ℕ} (f : Fin m → A × ℕ) (left : ℕ) (fits : left ≤ m) : List (A × ℕ) :=
  List.ofFn fun i : Fin left => f ⟨m-left+i.val,by have lt := i.isLt; omega⟩

private theorem suffix_cons {A : Type} {m left : ℕ} (f : Fin m → A × ℕ) (room : left+1 ≤ m)
    (index : Fin m) (atIndex : index.val=m-(left+1)) :
    suffix f (left+1) room=f index::suffix f left (by omega) := by
  unfold suffix
  rw [List.ofFn_succ]
  congr 1
  · congr 1
    apply Fin.ext
    simpa using atIndex.symm
  · congr 1
    funext i
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

private theorem fill_value {A : Type} {m : ℕ} (f : Fin m → (A × ℕ) × ℕ) (data : Array A)
    (cursor : Bits) (fee work left : ℕ) (position : value cursor+left=m) :
    let r := fill f data cursor fee work left position
    let tail := suffix (fun i => (f i).1) left (by omega)
    r.data.toList=data.toList++tail.map Prod.fst ∧ r.fee=fee+(tail.map Prod.snd).sum := by
  induction left generalizing data cursor fee work with
  | zero => simp [fill,suffix]
  | succ left ih =>
      unfold fill
      dsimp only
      let index := DirectNaturalView.decode cursor
      have here : index.1=value cursor := by
        rw [show index=(DirectNaturalView.decode cursor) from rfl,DirectNaturalView.decode_eq,BinaryNaturalView.decode_value]
      let i : Fin m := ⟨index.1,by omega⟩
      let item := (f i).1
      have step := suffix_cons (fun i => (f i).1) (show left+1 ≤ m by omega) i (by dsimp only [i]; omega)
      rw [step]
      simp only [List.map_cons,List.sum_cons]
      have hNext := (canonical_values cursor [true]).1
      have advance : value (addCanonical cursor [true]).1+left=m := by
        rw [hNext]
        simp only [value,Bool.toNat_true,Nat.add_zero,Nat.mul_zero]
        omega
      have done := ih (data.push item.1) (addCanonical cursor [true]).1
        (sumMeasured [fee,item.2]).1
        (work+index.2+(addCanonical cursor [true]).2+(sumMeasured [fee,item.2]).2+
          Nat.size left+cursor.length+10+(f i).2) advance
      simpa only [Array.toList_push,List.append_assoc,List.singleton_append,sum_value,List.sum_cons,List.sum_nil,
        Nat.add_zero,Nat.add_assoc] using done

private def fresh {A : Type} {m : ℕ} (f : Fin m → (A × ℕ) × ℕ) : Filled A :=
  fill f (Array.emptyWithCapacity m) [] 0 0 m (by simp [value])

private theorem fresh_value {A : Type} {m : ℕ} (f : Fin m → (A × ℕ) × ℕ) :
    let entries := List.ofFn (fun i => (f i).1)
    (fresh f).data.toList=entries.map Prod.fst ∧ (fresh f).fee=(entries.map Prod.snd).sum := by
  have result := fill_value f (Array.emptyWithCapacity m) [] 0 0 m (by simp [value])
  simpa only [fresh,suffix,Nat.sub_self,Nat.zero_add,Array.emptyWithCapacity_eq,Array.toList_empty,
    List.nil_append,Fin.eta] using result

def runWithChildWork {A : Type} {m : ℕ} (f : Fin m → (A × ℕ) × ℕ) : (Vector A m × ℕ) × ℕ :=
  let measured := fresh f
  let vector : Vector A m := ⟨measured.data,by
    have length := congrArg List.length (fresh_value f).1
    simpa only [Array.length_toList,List.length_map,List.length_ofFn] using length⟩
  ((vector,measured.fee+8*m+4),measured.work)

theorem runWithChildWork_value {A : Type} {m : ℕ} (f : Fin m → (A × ℕ) × ℕ) :
    (runWithChildWork f).1=(Vector.ofFn (fun i => (f i).1.1),
      ((List.ofFn (fun i => (f i).1)).map Prod.snd).sum+8*m+4) := by
  apply Prod.ext
  · apply Vector.toList_inj.mp
    change (fresh f).data.toList = _
    simpa only [Vector.toList_ofFn,List.map_ofFn,Function.comp_def] using (fresh_value f).1
  · simp only [runWithChildWork,(fresh_value f).2]

def run {A : Type} {m : ℕ} (f : Fin m → A × ℕ) : (Vector A m × ℕ) × ℕ :=
  runWithChildWork fun i => (f i,0)

theorem run_value {A : Type} {m : ℕ} (f : Fin m → A × ℕ) :
    (run f).1=(Vector.ofFn (fun i => (f i).1),((List.ofFn f).map Prod.snd).sum+8*m+4) :=
  runWithChildWork_value (fun i => (f i,0))

theorem child_projection {A : Type} {m : ℕ} (f : Fin m → (A × ℕ) × ℕ) :
    (runWithChildWork f).1=(run (fun i => (f i).1)).1 := by
  rw [runWithChildWork_value,run_value]

private def stepBound (m total : ℕ) : ℕ :=
  16*(m+1)^2+32*(m+2)+(2*(96*(total.size+2)^2+4)+1)+2*m+10

def childBudget (m cap childCap : ℕ) : ℕ := m*(stepBound m (m*cap)+childCap)+3

def controlBudget (m cap : ℕ) : ℕ := childBudget m cap 0

private theorem fill_paid {A : Type} {m cap childCap : ℕ} (f : Fin m → (A × ℕ) × ℕ)
    (callback : ∀ i, (f i).1.2 ≤ cap) (child : ∀ i, (f i).2 ≤ childCap)
    (data : Array A) (cursor : Bits) (fee work left : ℕ) (position : value cursor+left=m)
    (cursorFits : cursor.length ≤ m) (feeFits : fee+left*cap ≤ m*cap) :
    (fill f data cursor fee work left position).work ≤ work+left*(stepBound m (m*cap)+childCap)+3 := by
  induction left generalizing data cursor fee work with
  | zero => simp [fill]
  | succ left ih =>
      let index := DirectNaturalView.decode cursor
      have here : index.1=value cursor := by
        change (DirectNaturalView.decode cursor).1=value cursor
        rw [DirectNaturalView.decode_eq,BinaryNaturalView.decode_value]
      let i : Fin m := ⟨index.1,by omega⟩
      let item := (f i).1
      let next := addCanonical cursor [true]
      let charge := sumMeasured [fee,item.2]
      have nextValue : value next.1=value cursor+1 := by
        simpa only [next,value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero] using
          (canonical_values cursor [true]).1
      have nextPosition : value next.1+left=m := by rw [nextValue]; omega
      have nextWidth : next.1.length ≤ m := by
        have width : next.1.length=(value next.1).size := by
          rw [show value next.1=value cursor+value [true] from (canonical_values cursor [true]).1]
          exact (canonical_values cursor [true]).2.2.1
        rw [width]
        exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
      have itemFee := callback i
      have feeWithin : fee+item.2+left*cap ≤ m*cap := by
        change item.2 ≤ cap at itemFee
        rw [Nat.succ_mul] at feeFits
        omega
      have sumValue : charge.1=fee+item.2 := by
        simp only [charge,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
      have nextFee : charge.1+left*cap ≤ m*cap := by
        rw [sumValue]
        exact feeWithin
      have sumWidth : ([fee,item.2] : List ℕ).sum.size ≤ (m*cap).size := by
        apply Nat.size_le_size
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
        omega
      have decoded : index.2 ≤ 16*(m+1)^2 := by
        change (DirectNaturalView.decode cursor).2 ≤ _
        rw [DirectNaturalView.decode_eq]
        exact (BinaryNaturalView.decode_paid cursor).trans (by gcongr)
      have advanced : next.2 ≤ 32*(m+2) :=
        (canonical_charges cursorFits
          (show ([true] : Bits).length ≤ m by simp only [List.length_cons,List.length_nil]; omega)).1
      have summed : charge.2 ≤ 2*(96*((m*cap).size+2)^2+4)+1 := by
        simpa only [charge,List.length_cons,List.length_nil] using sum_paid _ sumWidth
      have remaining : left.size ≤ m := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
      have spent : index.2+next.2+charge.2+left.size+cursor.length+10 ≤ stepBound m (m*cap) := by
        unfold stepBound
        omega
      let accrued := work+index.2+next.2+charge.2+left.size+cursor.length+10+(f i).2
      have childSpent := child i
      have rest := ih (data.push item.1) next.1 charge.1 accrued nextPosition nextWidth nextFee
      rw [fill]
      change (fill f (data.push item.1) next.1 charge.1 accrued left nextPosition).work ≤ _
      refine rest.trans ?_
      rw [Nat.succ_mul]
      dsimp only [accrued]
      omega

theorem runWithChildWork_paid {A : Type} {m cap childCap : ℕ} (f : Fin m → (A × ℕ) × ℕ)
    (callback : ∀ i, (f i).1.2 ≤ cap) (child : ∀ i, (f i).2 ≤ childCap) :
    (runWithChildWork f).2 ≤ childBudget m cap childCap := by
  have paid := fill_paid f callback child (Array.emptyWithCapacity m) [] 0 0 m
    (by simp [value]) (by simp) (by simp)
  simpa only [runWithChildWork,fresh,childBudget,Nat.zero_add] using paid

theorem run_paid {A : Type} {m cap : ℕ} (f : Fin m → A × ℕ) (callback : ∀ i, (f i).2 ≤ cap) :
    (run f).2 ≤ controlBudget m cap := runWithChildWork_paid _ callback (fun _ => le_rfl)

def childCeiling {R : Type*} [Semiring R] (m cap childCap : R) : R :=
  m*(16*(m+1)^2+32*(m+2)+(2*(96*(m*cap+2)^2+4)+1)+2*m+10+childCap)+3

theorem childBudget_le (m cap childCap : ℕ) : childBudget m cap childCap ≤ childCeiling m cap childCap := by
  have width : (m*cap).size ≤ m*cap := Nat.size_le.mpr Nat.lt_two_pow_self
  unfold childBudget childCeiling stepBound
  gcongr

section Storage

open EncodedArrayStorage (Instruction allocateTrace fresh_append)
open CachedHeapCopies (PushExec pushTrace push_exec)

/-- A modeled copy sequence follows the array pushes, whether or not native
execution can reuse its preallocated storage. -/
inductive PushWalk {A : Type} : Array A → Array A → List (Instruction A) → Prop
  | done (data : Array A) : PushWalk data data []
  | push {before next out : Array A} {x : A} {step tail : List (Instruction A)} :
      PushExec before x next step → PushWalk next out tail → PushWalk before out (step++tail)

private theorem fill_storage {A : Type} {m : ℕ} (f : Fin m → (A × ℕ) × ℕ) (data : Array A)
    (cursor : Bits) (fee work left : ℕ) (position : value cursor+left=m) (size : data.size+left=m) :
    ∃ code,
      PushWalk data (fill f data cursor fee work left position).data code ∧
      code.length ≤ left*(4*m+5) ∧ EncodedArrayStorage.fresh code ≤ left*(m+3) := by
  induction left generalizing cursor fee work data with
  | zero => exact ⟨[],.done data,Nat.zero_le _,Nat.zero_le _⟩
  | succ left ih =>
      rw [fill]
      let index := DirectNaturalView.decode cursor
      have here : index.1=value cursor := by
        change (DirectNaturalView.decode cursor).1=value cursor
        rw [DirectNaturalView.decode_eq,BinaryNaturalView.decode_value]
      let result := f ⟨index.1,by omega⟩
      let item := result.1
      let next := addCanonical cursor [true]
      have advance : value next.1+left=m := by
        rw [show value next.1=value cursor+value [true] from (canonical_values cursor [true]).1]
        simp only [value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero]
        omega
      have pushed : (data.push item.1).size+left=m := by rw [Array.size_push]; omega
      let charge := sumMeasured [fee,item.2]
      let accrued := work+index.2+next.2+charge.2+left.size+cursor.length+10+result.2
      obtain ⟨code,walked,copies,cells⟩ := ih (data.push item.1) next.1 charge.1 accrued advance pushed
      have dataFits : data.size ≤ m := by omega
      refine ⟨pushTrace data item.1++code,.push (push_exec _ _) walked,?_,?_⟩
      · simp only [List.length_append,CachedHeapCopies.push_length,Nat.add_mul,Nat.one_mul]
        omega
      · simp only [fresh_append,CachedHeapCopies.push_cells,Nat.add_mul,Nat.one_mul]
        omega

def StorageModel {A : Type} {m : ℕ} (result : Vector A m) : Prop :=
    ∃ pushes : List (Instruction A),
      PushWalk (Array.emptyWithCapacity m) result.toArray pushes ∧
      let code := (([.reserve (m+2),.storeHeader 0,.storeHeader m] : List (Instruction A))++pushes).map
        PackedArraySchedule.shape
      let copyCap := m*(4*m+5)+3
      let cellCap := m*(m+3)+m+2
      code.length ≤ copyCap ∧ EncodedArrayStorage.fresh code ≤ cellCap ∧
      ∀ start : ℕ,
        let placed := allocateTrace start code
        let width := (start+cellCap).size
        let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
        (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
          binary.charge ≤ BinaryAllocationTrace.chargeBound copyCap width ∧
          ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size ≤ width

theorem runWithChildWork_storage {A : Type} {m : ℕ} (f : Fin m → (A × ℕ) × ℕ) :
    StorageModel (runWithChildWork f).1.1 := by
  obtain ⟨pushes,walked,copies,cells⟩ := fill_storage f (Array.emptyWithCapacity m) [] 0 0 m
    (by simp [value]) (by simp)
  let code := (([.reserve (m+2),.storeHeader 0,.storeHeader m] : List (Instruction A))++pushes).map
    PackedArraySchedule.shape
  let copyCap := m*(4*m+5)+3
  let cellCap := m*(m+3)+m+2
  have work : code.length ≤ copyCap := by
    simp only [code,copyCap,List.length_map,List.length_append,List.length_cons,List.length_nil]
    omega
  have space : EncodedArrayStorage.fresh code ≤ cellCap := by
    rw [show EncodedArrayStorage.fresh code=m+2+EncodedArrayStorage.fresh pushes by
      dsimp only [code]
      rw [PackedArraySchedule.shape_extent,fresh_append]
      rfl]
    dsimp only [cellCap]
    omega
  refine ⟨pushes,walked,work,space,fun start => ?_⟩
  obtain ⟨same,paid,widths⟩ := PackedArrayReservations.binary_layout code start
  have fits : (start+EncodedArrayStorage.fresh code).size ≤ (start+cellCap).size :=
    Nat.size_le_size (Nat.add_le_add_left space start)
  exact ⟨same,paid.trans (by unfold BinaryAllocationTrace.chargeBound; gcongr),
    fun block member offset valid => (widths block member offset valid).trans fits⟩

theorem run_storage {A : Type} {m : ℕ} (f : Fin m → A × ℕ) : StorageModel (run f).1.1 :=
  runWithChildWork_storage (fun i => (f i,0))

end Storage

end DirectedFlowCutGap.BinaryArrayBatch
