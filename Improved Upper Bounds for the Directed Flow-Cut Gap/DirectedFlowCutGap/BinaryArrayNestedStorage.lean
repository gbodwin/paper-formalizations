import DirectedFlowCutGap.BinaryArrayBatch

/-! Interleave each callback's array work with the push of that callback's
returned row. The input to the next push is the preceding array result. -/
namespace DirectedFlowCutGap.BinaryArrayNestedStorage

open BinaryArithmetic EncodedArrayStorage Polynomial
open BinaryArrayBatch (PushWalk StorageModel)
open CachedHeapCopies (PushExec)
open PackedArraySchedule (shape shape_extent)

abbrev Code := List (Instruction Unit)

def copyBudget {R : Type*} [Semiring R] (n : R) : R := n*(4*n+5)+3

def cellBudget {R : Type*} [Semiring R] (n : R) : R := n*(n+3)+n+2

theorem copyBudget_eval (n : Polynomial ℕ) (x : ℕ) :
    (copyBudget n).eval x=copyBudget (n.eval x) := by
  simp only [copyBudget,eval_add,eval_mul,eval_ofNat]

theorem cellBudget_eval (n : Polynomial ℕ) (x : ℕ) :
    (cellBudget n).eval x=cellBudget (n.eval x) := by
  simp only [cellBudget,eval_add,eval_mul,eval_ofNat]

theorem copyBudget_mono {a b : ℕ} (h : a≤b) : copyBudget a≤copyBudget b := by
  unfold copyBudget
  gcongr

theorem cellBudget_mono {a b : ℕ} (h : a≤b) : cellBudget a≤cellBudget b := by
  unfold cellBudget
  gcongr

inductive Interleaved {A : Type} (child : ℕ → Code) :
    Array A → Array A → List (Instruction A) → Code → Prop where
  | done (data : Array A) : Interleaved child data data [] []
  | push {before next out : Array A} {x : A} {step tail : List (Instruction A)} {later : Code} :
      PushExec before x next step → Interleaved child next out tail later →
      Interleaved child before out (step++tail) (child before.size++step.map shape++later)

private theorem push_size {A : Type} {before next : Array A} {x : A} {code : List (Instruction A)}
    (moved : PushExec before x next code) : next.size=before.size+1 := by
  cases moved with
  | write _ copied => simp [copied.output]

private theorem interleave {A : Type} {before out : Array A} {pushes : List (Instruction A)}
    (walked : PushWalk before out pushes) (child : ℕ → Code) (cells copies : ℕ)
    (fit : ∀ i < out.size, (child i).length ≤ copies ∧ fresh (child i) ≤ cells) :
    before.size≤out.size ∧ ∃ code, Interleaved child before out pushes code ∧
      code.length ≤ pushes.length+(out.size-before.size)*copies ∧
      fresh code ≤ fresh pushes+(out.size-before.size)*cells := by
  induction walked with
  | done data => exact ⟨le_rfl,[],.done data,by simp,by simp [fresh]⟩
  | @push before next out a step tail moved _ ih =>
    obtain ⟨inside,later,observed,copy,space⟩ := ih fit
    have advance := push_size moved
    have index : before.size < out.size := by omega
    have bound := fit before.size index
    have difference : out.size-before.size=(out.size-next.size)+1 := by omega
    refine ⟨index.le,child before.size++step.map shape++later,.push moved observed,?_,?_⟩
    · simp only [List.length_append,List.length_map,difference,Nat.add_mul,Nat.one_mul]
      omega
    · simp only [fresh_append,shape_extent,difference,Nat.add_mul,Nat.one_mul]
      omega

/-- The outer header is reserved before any child is called. At each slot,
the admitted storage execution places the child before the parent push. -/
def WithChildren {A : Type} {m : ℕ} (result : Vector A m) (child : ℕ → Code) (code : Code) : Prop :=
  ∃ pushes tail, Interleaved child (Array.emptyWithCapacity m) result.toArray pushes tail ∧
    code=[.reserve (m+2),.storeHeader 0,.storeHeader m]++tail

theorem withChildren {A : Type} {m : ℕ} {result : Vector A m} (storage : StorageModel result)
    (child : ℕ → Code) (cells copies : ℕ)
    (fits : ∀ i < m, (child i).length≤copies ∧ fresh (child i)≤cells) :
    ∃ code, WithChildren result child code ∧
      code.length≤copyBudget m+m*copies ∧ fresh code≤cellBudget m+m*cells := by
  obtain ⟨pushes,walked,count,extent,_⟩ := storage
  obtain ⟨_,tail,done,copied,allocated⟩ := interleave walked child cells copies (by simpa only [Vector.size_toArray])
  let code : Code := [.reserve (m+2),.storeHeader 0,.storeHeader m]++tail
  have empty : (Array.emptyWithCapacity m : Array A).size=0 := by rw [Array.emptyWithCapacity_eq]; rfl
  simp only [Vector.size_toArray,empty,Nat.sub_zero] at copied allocated
  refine ⟨code,⟨pushes,tail,done,rfl⟩,?_,?_⟩
  · simp only [List.length_map,List.length_append,List.length_cons,List.length_nil] at count
    simp only [code,copyBudget,List.length_append,List.length_cons,List.length_nil]
    omega
  · simp only [shape_extent,fresh_append] at extent
    change m+2+fresh pushes≤m*(m+3)+m+2 at extent
    have header : fresh ([.reserve (m+2),.storeHeader 0,.storeHeader m] : Code)=m+2 := by
      simp [fresh,Instruction.fresh]
    simp only [code,fresh_append,header,cellBudget]
    omega

theorem alone {A : Type} {m : ℕ} {result : Vector A m} (storage : StorageModel result) :
    ∃ code, WithChildren result (fun _ => []) code ∧ code.length≤copyBudget m ∧ fresh code≤cellBudget m := by
  simpa only [Nat.mul_zero,Nat.add_zero] using withChildren storage (fun _ => []) 0 0 (by simp [fresh])

def Grid {A : Type} {m n : ℕ} (result : Vector (Vector A n) m) (code : Code) : Prop :=
  ∃ rows : Fin m → Code,
    (∀ i : Fin m, WithChildren result[i.val] (fun _ => []) (rows i)) ∧
    WithChildren result (fun i => if h : i<m then rows ⟨i,h⟩ else []) code

theorem grid {A : Type} {m n : ℕ} (f : Fin m → (Vector A n × ℕ) × ℕ)
    (inner : ∀ i, StorageModel (f i).1.1) :
    let result := (BinaryArrayBatch.runWithChildWork f).1.1
    ∃ code, Grid result code ∧ code.length≤copyBudget m+m*copyBudget n ∧
      fresh code≤cellBudget m+m*cellBudget n := by
  let result := (BinaryArrayBatch.runWithChildWork f).1.1
  have entry (i : Fin m) : result[i.val]=(f i).1.1 := by
    simp only [result,congrArg Prod.fst (BinaryArrayBatch.runWithChildWork_value f),Vector.getElem_ofFn,Fin.eta]
  have schedules (i : Fin m) := alone (inner i)
  choose rows observed lengths cells using schedules
  let child (i : ℕ) := if h : i<m then rows ⟨i,h⟩ else []
  have fits : ∀ i < m, (child i).length≤copyBudget n ∧ fresh (child i)≤cellBudget n := by
    intro i h
    simp only [child,dite_eq_left h]
    exact ⟨lengths ⟨i,h⟩,cells ⟨i,h⟩⟩
  obtain ⟨code,assembled,bound,space⟩ := withChildren (BinaryArrayBatch.runWithChildWork_storage f)
    child (cellBudget n) (copyBudget n) fits
  exact ⟨code,⟨rows,fun i => (entry i).symm ▸ observed i,assembled⟩,bound,space⟩

private def steps (child : ℕ → Code) (index : ℕ) : ℕ → Code
  | 0 => []
  | left+1 => child index++CachedHeapCopies.pushTrace (Array.replicate index ()) ()++steps child (index+1) left

def schedule (m : ℕ) (child : ℕ → Code) : Code :=
  [.reserve (m+2),.storeHeader 0,.storeHeader m]++steps child 0 m

theorem copy_shape {A : Type} (source : List A) :
    (copyTrace source).map shape=copyTrace (List.replicate source.length ()) := by
  induction source with
  | nil => rfl
  | cons head tail ih =>
    simp only [copyTrace,List.map_append,List.length_cons,List.replicate_succ,ih]
    rfl

private theorem push_shape {A : Type} {before next : Array A} {a : A} {code : List (Instruction A)}
    (moved : PushExec before a next code) :
    code.map shape=CachedHeapCopies.pushTrace (Array.replicate before.size ()) () := by
  cases moved with
  | write _ copied =>
    rw [copied.trace_eq]
    simp only [CachedHeapCopies.pushTrace,List.map_append,copy_shape,Array.length_toList,
      Array.size_replicate,Array.toList_replicate]
    rfl

private theorem steps_eq {A : Type} {child : ℕ → Code} {before out : Array A}
    {pushes : List (Instruction A)} {code : Code} (walked : Interleaved child before out pushes code) :
    before.size ≤ out.size ∧ code=steps child before.size (out.size-before.size) := by
  induction walked with
  | done data => exact ⟨le_rfl,by simp only [Nat.sub_self,steps]⟩
  | @push before next out a step tail later moved _ ih =>
    have size := push_size moved
    have difference : out.size-before.size=(out.size-next.size)+1 := by have := ih.1; omega
    refine ⟨by have := ih.1; omega,?_⟩
    rw [difference,steps,push_shape moved,ih.2,size]

theorem schedule_eq {A : Type} {m : ℕ} {result : Vector A m} {child : ℕ → Code} {code : Code}
    (run : WithChildren result child code) : code=schedule m child := by
  obtain ⟨_,tail,walked,rfl⟩ := run
  have empty : (Array.emptyWithCapacity m : Array A).size=0 := by rw [Array.emptyWithCapacity_eq]; rfl
  simp only [schedule,(steps_eq walked).2,empty,Vector.size_toArray,Nat.sub_zero]

private theorem steps_congr (f g : ℕ → Code) (index count : ℕ)
    (eq : ∀ i, index ≤ i → i < index+count → f i=g i) : steps f index count=steps g index count := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
    simp only [steps,eq index le_rfl (by omega)]
    rw [ih (index+1) (fun i lower upper => eq i (by omega) (by omega))]

def gridSchedule (m n : ℕ) : Code := schedule m (fun _ => schedule n (fun _ => []))

theorem grid_schedule_eq {A : Type} {m n : ℕ} {result : Vector (Vector A n) m} {code : Code}
    (run : Grid result code) : code=gridSchedule m n := by
  obtain ⟨rows,children,outer⟩ := run
  rw [schedule_eq outer]
  unfold gridSchedule schedule
  congr 1
  apply steps_congr
  intro i _ fit
  have valid : i < m := by omega
  simp only [dite_eq_left valid]
  exact schedule_eq (children ⟨i,valid⟩)

theorem flat_schedule {A : Type} {m : ℕ} {result : Vector A m} (storage : StorageModel result) :
    WithChildren result (fun _ => []) (schedule m (fun _ => [])) := by
  obtain ⟨_,model,_,_⟩ := alone storage
  exact schedule_eq model ▸ model

theorem grid_schedule {A : Type} {m n : ℕ} (f : Fin m → (Vector A n × ℕ) × ℕ)
    (inner : ∀ i, StorageModel (f i).1.1) :
    Grid (BinaryArrayBatch.runWithChildWork f).1.1 (gridSchedule m n) := by
  obtain ⟨_,model,_,_⟩ := grid f inner
  exact grid_schedule_eq model ▸ model

theorem flat_bounds (n : ℕ) :
    (schedule n (fun _ => [])).length ≤ copyBudget n ∧ fresh (schedule n (fun _ => [])) ≤ cellBudget n := by
  obtain ⟨_,model,ops,space⟩ := alone (BinaryArrayBatch.run_storage (fun _ : Fin n => ((),0)))
  rw [schedule_eq model] at ops space
  exact ⟨ops,space⟩

theorem grid_bounds (n : ℕ) :
    (gridSchedule n n).length ≤ (n+1)*copyBudget n ∧ fresh (gridSchedule n n) ≤ (n+1)*cellBudget n := by
  let row (_ : Fin n) := BinaryArrayBatch.runWithChildWork (fun _ : Fin n => (((),0),0))
  obtain ⟨_,model,ops,space⟩ := grid row (fun _ => BinaryArrayBatch.runWithChildWork_storage _)
  rw [grid_schedule_eq model] at ops space
  simp only [Nat.add_mul,Nat.one_mul]
  omega

end DirectedFlowCutGap.BinaryArrayNestedStorage
