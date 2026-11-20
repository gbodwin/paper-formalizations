import DirectedFlowCutGap.ChargedSourceTables
import DirectedFlowCutGap.EncodedEdgeInput
import DirectedFlowCutGap.DirectNaturalView
import DirectedFlowCutGap.TerminalArrayAssembly
import DirectedFlowCutGap.PackedArraySchedule

/-! Count source decoding after the framed tables have been read. Field
validation, endpoint conversion and vector assembly share one input budget. -/

namespace DirectedFlowCutGap.ChargedSourceAssembly

open BinaryArithmetic EncodedVertexInput
open PhysicalCoverAccess (Read)

private theorem bind_value {A B : Type} (r : Read A) (k : A → Read B) :
    (Read.bind r k).1=r.1.bind (fun a => (k a).1) := Read.bind_value r k

private def scan {A B : Type} (decode : A → Read B) : List A → Read (List B)
  | [] => (some [],1)
  | a::as =>
    let r := Read.bind (decode a) fun b =>
      Read.bind (scan decode as) fun bs => (pure (b::bs) : Read (List B))
    (r.1,r.2+5)

private theorem scan_value {A B : Type} (decode : A → Read B) (xs : List A) :
    (scan decode xs).1=xs.mapM (fun a => (decode a).1) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [scan,bind_value,Read.pure_value,ih,List.mapM_cons]
    rfl

private theorem map_length {A B : Type} (f : A → Option B) {xs : List A} {ys : List B}
    (h : xs.mapM f=some ys) : ys.length=xs.length := by
  induction xs generalizing ys with
  | nil => simpa using congrArg (Option.map List.length) h.symm
  | cons a as ih =>
    cases v : f a with
    | none => simp [v] at h
    | some b =>
      cases rest : as.mapM f with
      | none => simp [v,rest] at h
      | some bs =>
        simp [List.mapM_cons,v,rest] at h
        rw [← h,List.length_cons,List.length_cons,ih rest]

private theorem map_member {A B : Type} (f : A → Option B) {xs : List A} {ys : List B}
    (h : xs.mapM f=some ys) {y : B} (mem : y ∈ ys) : ∃ x ∈ xs, f x=some y := by
  induction xs generalizing ys with
  | nil =>
    have empty : ([] : List B)=ys := Option.some.inj h
    subst ys
    cases mem
  | cons a as ih =>
    cases v : f a with
    | none => simp [v] at h
    | some b =>
      cases rest : as.mapM f with
      | none => simp [v,rest] at h
      | some bs =>
        simp [List.mapM_cons,v,rest] at h
        rw [← h] at mem
        obtain rfl | tail := List.mem_cons.mp mem
        · exact ⟨a,List.mem_cons_self,v⟩
        · obtain ⟨x,m,value⟩ := ih rest tail
          exact ⟨x,List.mem_cons_of_mem _ m,value⟩

private theorem scan_paid {A B : Type} (decode : A → Read B) (xs : List A) (cap : ℕ)
    (bound : ∀ a ∈ xs, (decode a).2 ≤ cap) :
    (scan decode xs).2 ≤ xs.length*(cap+5)+1 := by
  induction xs with
  | nil => simp [scan]
  | cons a as ih =>
    have head := bound a List.mem_cons_self
    have tail := ih (fun x h => bound x (List.mem_cons_of_mem _ h))
    let next (b : B) : Read (List B) := Read.bind (scan decode as) fun bs => pure (b::bs)
    have total := Read.bind_bound head (k:=next) (fun _ _ =>
        Read.bind_bound tail (later:=0) (fun _ _ => Nat.le_refl 0))
    change (Read.bind (decode a) next).2 ≤ cap+(as.length*(cap+5)+1+0) at total
    change (Read.bind (decode a) next).2+5 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private theorem wordValue_paid (bits : Bits) : (DirectNaturalView.decode bits).2 ≤ 16*(bits.length+1)^2 := by
  rw [DirectNaturalView.decode_eq]
  exact BinaryNaturalView.decode_paid bits

private def fraction (r : Row) : Read BinaryRational.Fraction := BinaryRational.fromBits r.1 r.2

private theorem fraction_value (r : Row) : (fraction r).1 = readFraction r := rfl

private def matrixRow (n : ℕ) (r : Row) : Read (Vector Bool n) :=
  let row := if h : r.1.length=n ∧ r.2=[] then some (TerminalArrayAssembly.vector r.1 h.1) else none
  (row,12*(r.1.length+r.2.length+1)+n+6)

private theorem matrixRow_value (n : ℕ) (r : Row) : (matrixRow n r).1=readMatrixRow n r := by
  unfold matrixRow readMatrixRow
  dsimp only
  split <;> simp_all

private def pair (n : ℕ) (r : Row) : Read (Fin n × Fin n) :=
  let a := DirectNaturalView.decode r.1
  let b := DirectNaturalView.decode r.2
  let out := if h : a.1<n ∧ b.1<n then some (⟨a.1,h.1⟩,⟨b.1,h.2⟩) else none
  (out,a.2+b.2+16*(r.1.length+r.2.length+n+1)+20)

private theorem pair_value (n : ℕ) (r : Row) : (pair n r).1=readDemand n r := by
  simp only [pair,readDemand,DirectNaturalView.decode_eq,BinaryNaturalView.decode_value]

private structure Fits (rows : Table) (x : ℕ) : Prop where
  count : rows.length ≤ x
  field : ∀ r ∈ rows, r.1.length ≤ x ∧ r.2.length ≤ x

private theorem size_fits (rows : Table) {x : ℕ} (h : (SourceRowTableProgram.encode rows).length ≤ x) : Fits rows x := by
  induction rows with
  | nil => exact ⟨Nat.zero_le _,by simp⟩
  | cons r rs ih =>
    rcases r with ⟨a,b⟩
    simp only [SourceRowTableProgram.encode,List.length_append,List.length_cons,SelfDelimitedWordProgram.encode_length] at h
    have rest := ih (by omega)
    constructor
    · simp only [List.length_cons]
      have len : rs.length < (SourceRowTableProgram.encode rs).length := by
        simpa only [List.append_nil] using table_prefix_has_fuel rs []
      omega
    · intro q mem
      rcases List.mem_cons.mp mem with rfl | next
      · dsimp only
        omega
      · exact rest.field q next

private theorem read_fits {source tail : Bits} {C M D : Table}
    (read : (ChargedSourceTables.tables source).1=some (C,M,D,tail)) :
    Fits C source.length ∧ Fits M source.length ∧ Fits D source.length := by
  have wire := congrArg List.length (ChargedSourceTables.tables_wire read)
  simp only [PackingSourceInput.encode,List.length_append] at wire
  exact ⟨size_fits C (by omega),size_fits M (by omega),size_fits D (by omega)⟩

private def rowBudget (x : ℕ) : ℕ := 128*(x+1)^2
private def scanBudget (x : ℕ) : ℕ := x*(rowBudget x+5)+1

private theorem fractionBound {C : Table} {x : ℕ} (fits : Fits C x) :
    (scan fraction C).2 ≤ scanBudget x := by
  apply (scan_paid fraction C (rowBudget x) ?_).trans
  · unfold scanBudget
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ fits.count) 1
  · intro r mem
    have h := BinaryRational.fromBits_charge r.1 r.2
    have w := (fits.field r mem).2
    unfold rowBudget fraction
    exact h.trans (by nlinarith)

private theorem matrixBound {M : Table} {n x : ℕ} (hn : n ≤ x) (fits : Fits M x) :
    (scan (matrixRow n) M).2 ≤ scanBudget x := by
  apply (scan_paid (matrixRow n) M (rowBudget x) ?_).trans
  · unfold scanBudget
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ fits.count) 1
  · intro r mem
    have ⟨a,b⟩ := fits.field r mem
    unfold rowBudget matrixRow
    dsimp only
    nlinarith

private theorem pairsBound {D : Table} {n x : ℕ} (hn : n ≤ x) (fits : Fits D x) :
    (scan (pair n) D).2 ≤ scanBudget x := by
  apply (scan_paid (pair n) D (rowBudget x) ?_).trans
  · unfold scanBudget
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ fits.count) 1
  · intro r mem
    obtain ⟨a,b⟩ := fits.field r mem
    have left := (wordValue_paid r.1).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right a 1) 2))
    have right := (wordValue_paid r.2).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right b 1) 2))
    unfold rowBudget pair
    dsimp only
    nlinarith

private def vertexResult (costs : List BinaryRational.Fraction) (matrix : List (Vector Bool costs.length))
    (demands : List (Fin costs.length × Fin costs.length)) : Read EncodedVertexInput.Input :=
  if h : matrix.length=costs.length then
    (some ⟨costs.length,⟨TerminalArrayAssembly.vector matrix h,demands,
      TerminalArrayAssembly.vector costs rfl⟩⟩,0)
  else (none,0)

private def edgeResult (n : ℕ) (costs : List BinaryRational.Fraction) (matrix : List (Vector Bool n))
    (demands : List (Fin n × Fin n)) : Read (Σ n, EncodedEdgeInput.Input n) :=
  if h : costs.length=n*n ∧ matrix.length=n then
    (some ⟨n,⟨TerminalArrayAssembly.vector matrix h.2,demands,
      TerminalArrayAssembly.vector costs h.1⟩⟩,0)
  else (none,0)

private def vertexPayload (C M D : Table) : Read EncodedVertexInput.Input :=
  Read.bind (scan fraction C) fun costs =>
    Read.bind (scan (matrixRow costs.length) M) fun matrix =>
      Read.bind (scan (pair costs.length) D) (vertexResult costs matrix)

private def edgePayload (C M D : Table) : Read (Σ n, EncodedEdgeInput.Input n) :=
  Read.bind (scan fraction C) fun costs =>
    Read.bind (scan (matrixRow M.length) M) fun matrix =>
      Read.bind (scan (pair M.length) D) (edgeResult M.length costs matrix)

def vertexAssembly (C M D : Table) : Read EncodedVertexInput.Input :=
  let counts := vertexPayload C M D
  (counts.1,counts.2+16*(C.length+M.length+D.length+1))

def edgeAssembly (C M D : Table) : Read (Σ n, EncodedEdgeInput.Input n) :=
  let counts := edgePayload C M D
  (counts.1,counts.2+16*(C.length+M.length+D.length+1))

theorem vertexAssembly_value (C M D : Table) : (vertexAssembly C M D).1=EncodedVertexInput.assemble C M D := by
  simp only [vertexAssembly,vertexPayload,bind_value,scan_value,fraction_value,matrixRow_value,pair_value]
  change _ = (C.mapM readFraction).bind (fun costs =>
    ((M.mapM (readMatrixRow costs.length)).bind (fun matrix =>
      (D.mapM (readDemand costs.length)).bind (fun demands =>
        if h : matrix.length=costs.length then
          some (⟨⟨matrix.toArray,by simpa using h⟩,demands,⟨costs.toArray,by simp⟩⟩ : BinaryFractionalGuesses.Input costs.length)
        else none))).map (fun a => (⟨costs.length,a⟩ : EncodedVertexInput.Input)))
  cases c : C.mapM readFraction with
  | none => rfl
  | some costs =>
    simp only [Option.bind_some]
    cases matrix : M.mapM (readMatrixRow costs.length) with
    | none => rfl
    | some rows =>
      cases demands : D.mapM (readDemand costs.length) with
      | none => rfl
      | some ds =>
        by_cases h : rows.length=costs.length <;> simp [vertexResult,h]

theorem edgeAssembly_value (C M D : Table) : (edgeAssembly C M D).1=EncodedEdgeInput.assemble C M D := by
  simp only [edgeAssembly,edgePayload,bind_value,scan_value,fraction_value,matrixRow_value,pair_value]
  change _ = (((C.mapM readFraction).bind (fun costs => (M.mapM (readMatrixRow M.length)).bind (fun matrix =>
    (D.mapM (readDemand M.length)).bind (fun demands =>
      if h : costs.length=M.length*M.length ∧ matrix.length=M.length then
        some (⟨⟨matrix.toArray,by simpa using h.2⟩,demands,⟨costs.toArray,by simpa using h.1⟩⟩ : EncodedEdgeInput.Input M.length)
      else none)))).map fun a => (⟨M.length,a⟩ : Σ n, EncodedEdgeInput.Input n))
  cases c : C.mapM readFraction with
  | none => rfl
  | some costs =>
    cases matrix : M.mapM (readMatrixRow M.length) with
    | none => rfl
    | some rows =>
      cases demands : D.mapM (readDemand M.length) with
      | none => rfl
      | some ds =>
        by_cases h : costs.length=M.length*M.length ∧ rows.length=M.length <;> simp [edgeResult,h]

private def assemblyBudget (x : ℕ) : ℕ := 3*scanBudget x+16*(3*x+1)

private theorem vertexAssembly_paid {C M D : Table} {x : ℕ} (c : Fits C x) (m : Fits M x) (d : Fits D x) :
    (vertexAssembly C M D).2 ≤ assemblyBudget x := by
  unfold vertexAssembly assemblyBudget
  dsimp only
  have ranges : (vertexPayload C M D).2 ≤ scanBudget x+(scanBudget x+scanBudget x+0) := by
    unfold vertexPayload
    apply Read.bind_bound (fractionBound c)
    intro costs h
    have n := map_length _ ((scan_value fraction C).symm ▸ h)
    have hx : costs.length ≤ x := n.trans_le c.count
    have h := Read.bind_bound (matrixBound hx m) (k:=fun matrix =>
      Read.bind (scan (pair costs.length) D) (vertexResult costs matrix)) (fun matrix _ =>
        Read.bind_bound (pairsBound hx d) (later:=0) (fun ds _ => by unfold vertexResult; split <;> exact le_rfl))
    exact h.trans (by omega)
  have cCount := c.count
  have mCount := m.count
  have dCount := d.count
  omega

private theorem edgeAssembly_paid {C M D : Table} {x : ℕ} (c : Fits C x) (m : Fits M x) (d : Fits D x) :
    (edgeAssembly C M D).2 ≤ assemblyBudget x := by
  unfold edgeAssembly assemblyBudget
  dsimp only
  have n := m.count
  have ranges : (edgePayload C M D).2 ≤ scanBudget x+(scanBudget x+scanBudget x+0) := by
    unfold edgePayload
    apply Read.bind_bound (fractionBound c)
    intro costs _
    have h := Read.bind_bound (matrixBound n m) (k:=fun matrix =>
      Read.bind (scan (pair M.length) D) (edgeResult M.length costs matrix)) (fun matrix _ =>
        Read.bind_bound (pairsBound n d) (later:=0) (fun ds _ => by unfold edgeResult; split <;> exact le_rfl))
    exact h.trans (by omega)
  have cCount := c.count
  have dCount := d.count
  omega

private def parseFinish {A : Type} (assemble : Table → Table → Table → Read A) :
    Table × Table × Table × Bits → Read A
  | (c,m,d,tail) => if tail.isEmpty then assemble c m d else (none,0)

private def parseWith {A : Type} (assemble : Table → Table → Table → Read A) (source : Bits) : Read A :=
  let result := Read.bind (ChargedSourceTables.tables source) (parseFinish assemble)
  (result.1,result.2+5)

def vertex (source : Bits) : Read EncodedVertexInput.Input := parseWith vertexAssembly source
def edge (source : Bits) : Read (Σ n, EncodedEdgeInput.Input n) := parseWith edgeAssembly source

theorem vertex_value (source : Bits) : (vertex source).1=EncodedVertexInput.parse source := by
  simp only [vertex,parseWith,bind_value,ChargedSourceTables.tables_value,EncodedVertexInput.parse]
  congr 1
  funext a
  rcases a with ⟨c,m,d,tail⟩
  by_cases h : tail.isEmpty=true <;> simp [parseFinish,h,vertexAssembly_value]

theorem edge_value (source : Bits) : (edge source).1=EncodedEdgeInput.parse source := by
  simp only [edge,parseWith,bind_value,ChargedSourceTables.tables_value,EncodedEdgeInput.parse]
  congr 1
  funext a
  rcases a with ⟨c,m,d,tail⟩
  by_cases h : tail.isEmpty=true <;> simp [parseFinish,h,edgeAssembly_value]

def parseBudget (x : ℕ) : ℕ := 35*x+39+assemblyBudget x

open Polynomial in
noncomputable def parsePolynomial : Polynomial ℕ :=
  C 35*X+C 39+(C 3*(X*(C 128*(X+1)^2+C 5)+1)+C 16*(C 3*X+1))

open Polynomial in
theorem parsePolynomial_eval (x : ℕ) : parsePolynomial.eval x=parseBudget x := by
  simp only [parsePolynomial,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one,parseBudget,assemblyBudget,scanBudget,rowBudget]

private theorem parse_paid {A : Type} (assemble : Table → Table → Table → Read A)
    (bound : ∀ {C M D : Table} {x : ℕ}, Fits C x → Fits M x → Fits D x → (assemble C M D).2 ≤ assemblyBudget x)
    (source : Bits) : (parseWith assemble source).2 ≤ parseBudget source.length := by
  have first := ChargedSourceTables.tables_paid source
  have full := Read.bind_bound first (later:=assemblyBudget source.length)
    (k:=parseFinish assemble) (fun a out => by
    rcases a with ⟨C,M,D,tail⟩
    obtain ⟨c,m,d⟩ := read_fits out
    by_cases h : tail.isEmpty=true
    · simpa only [parseFinish,ite_eq_left h] using bound c m d
    · simp [parseFinish,h])
  change (Read.bind (ChargedSourceTables.tables source) (parseFinish assemble)).2 ≤
    (35*source.length+34)+assemblyBudget source.length at full
  change (Read.bind (ChargedSourceTables.tables source) (parseFinish assemble)).2+5 ≤ _
  unfold parseBudget
  omega

theorem vertex_paid (source : Bits) : (vertex source).2 ≤ parseBudget source.length :=
  parse_paid vertexAssembly vertexAssembly_paid source

theorem edge_paid (source : Bits) : (edge source).2 ≤ parseBudget source.length :=
  parse_paid edgeAssembly edgeAssembly_paid source

private theorem parsed_tables {A : Type} (assemble : Table → Table → Table → Read A)
    {source : Bits} {input : A} (parsed : (parseWith assemble source).1=some input) :
    ∃ C M D : Table, Fits C source.length ∧ Fits M source.length ∧ Fits D source.length ∧
      (assemble C M D).1=some input := by
  simp only [parseWith,bind_value] at parsed
  obtain ⟨tables,read,out⟩ := Option.bind_eq_some_iff.mp parsed
  rcases tables with ⟨C,M,D,tail⟩
  obtain ⟨c,m,d⟩ := read_fits read
  by_cases h : tail.isEmpty=true
  · exact ⟨C,M,D,c,m,d,by simpa only [parseFinish,ite_eq_left h] using out⟩
  · simp [parseFinish,h] at out

private theorem decoded_fields {C : Table} {x : ℕ} {costs : List BinaryRational.Fraction}
    (fits : Fits C x) (read : C.mapM readFraction=some costs) :
    ∀ q ∈ costs, BinaryRational.StoredBounded q x := by
  intro q mem
  obtain ⟨r,rm,result⟩ := map_member readFraction read mem
  have actual := BinaryRational.fromBits_fields r.1 r.2 result
  obtain ⟨a,b⟩ := fits.field r rm
  exact ⟨actual.1 ▸ a,actual.2 ▸ b⟩

theorem vertex_dimensions {n : ℕ} {D : BinaryFractionalGuesses.Input n} {source : Bits}
    (parsed : (vertex source).1=some ⟨n,D⟩) :
    n ≤ source.length ∧ D.demands.length ≤ source.length ∧
      ∀ q ∈ D.costs.toList, BinaryRational.StoredBounded q source.length := by
  obtain ⟨C,M,Q,c,_,q,actual⟩ := parsed_tables vertexAssembly parsed
  simp only [vertexAssembly,vertexPayload,bind_value,scan_value,fraction_value,matrixRow_value,pair_value] at actual
  obtain ⟨costs,rc,next⟩ := Option.bind_eq_some_iff.mp actual
  obtain ⟨matrix,_,next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨demands,rd,out⟩ := Option.bind_eq_some_iff.mp next
  unfold vertexResult at out
  split at out
  · have hc := (map_length readFraction rc).trans_le c.count
    have hd := (map_length _ rd).trans_le q.count
    have hw := decoded_fields c rc
    cases out
    exact ⟨hc,hd,by simpa using hw⟩
  · cases out

theorem edge_dimensions {n : ℕ} {D : EncodedEdgeInput.Input n} {source : Bits}
    (parsed : (edge source).1=some ⟨n,D⟩) :
    n ≤ source.length ∧ D.demands.length ≤ source.length ∧
      ∀ q ∈ D.costs.toList, BinaryRational.StoredBounded q source.length := by
  obtain ⟨C,M,Q,c,m,q,actual⟩ := parsed_tables edgeAssembly parsed
  simp only [edgeAssembly,edgePayload,bind_value,scan_value,fraction_value,matrixRow_value,pair_value] at actual
  obtain ⟨costs,rc,next⟩ := Option.bind_eq_some_iff.mp actual
  obtain ⟨matrix,_,next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨demands,rd,out⟩ := Option.bind_eq_some_iff.mp next
  unfold edgeResult at out
  split at out
  · have hd := (map_length _ rd).trans_le q.count
    have hw := decoded_fields c rc
    cases out
    exact ⟨m.count,hd,by simpa using hw⟩
  · cases out

section Arrays

open EncodedArrayStorage (Instruction fresh fresh_append)

private def arrayCode {A : Type} (values : List A) : List (Instruction Unit) :=
  (TerminalArrayAssembly.schedule values).map PackedArraySchedule.shape

private def workBound (width : ℕ) : ℕ := 2*width^2+21*width+4
private def spaceBound (width : ℕ) : ℕ := width^2+7*width+2

private theorem array_code_paid {A : Type} (values : List A) {width : ℕ} (fits : values.length ≤ width) :
    (arrayCode values).length ≤ workBound width ∧ fresh (arrayCode values) ≤ spaceBound width := by
  obtain ⟨work,space⟩ := TerminalArrayAssembly.space values
  simp only [arrayCode,List.length_map,PackedArraySchedule.shape_extent,workBound,spaceBound]
  exact ⟨work.le.trans (by gcongr),space.trans (by gcongr)⟩

/-- Arrays built by the successful row decoders before the first rejected row. -/
private def matrixCode (n : ℕ) : Table → List (Instruction Unit)
  | [] => []
  | r::rest => match (matrixRow n r).1 with
    | none => []
    | some row => arrayCode row.toList ++ matrixCode n rest

private theorem matrix_code_paid (n : ℕ) (rows : Table) {width : ℕ} (fits : n ≤ width) :
    (matrixCode n rows).length ≤ rows.length*workBound width ∧
      fresh (matrixCode n rows) ≤ rows.length*spaceBound width := by
  induction rows with
  | nil => simp [matrixCode,fresh]
  | cons r rest ih =>
      cases read : (matrixRow n r).1 with
      | none => simp [matrixCode,read,fresh]
      | some row =>
          obtain ⟨work,space⟩ := array_code_paid row.toList (by simpa only [Vector.length_toList] using fits)
          simp only [matrixCode,read,List.length_append,fresh_append,List.length_cons,Nat.add_mul,Nat.one_mul]
          exact ⟨by omega,by omega⟩

private def payloadCode {A : Type} (n : ℕ) (costs : List BinaryRational.Fraction) (rows : Table)
    (finish : List (Vector Bool n) → Read A) : List (Instruction Unit) :=
  matrixCode n rows ++ match (scan (matrixRow n) rows).1 with
  | none => []
  | some matrix => if (finish matrix).1.isSome then arrayCode matrix ++ arrayCode costs else []

private theorem payload_code_paid {A : Type} {n width : ℕ} (costs : List BinaryRational.Fraction)
    (rows : Table) (finish : List (Vector Bool n) → Read A) (size : n ≤ width)
    (costFit : costs.length ≤ width) (rowFit : rows.length ≤ width) :
    (payloadCode n costs rows finish).length ≤ (width+2)*workBound width ∧
      fresh (payloadCode n costs rows finish) ≤ (width+2)*spaceBound width := by
  obtain ⟨work,space⟩ := matrix_code_paid n rows size
  have workRows := work.trans (Nat.mul_le_mul_right _ rowFit)
  have spaceRows := space.trans (Nat.mul_le_mul_right _ rowFit)
  have expand (k : ℕ) : (width+2)*k=width*k+(k+k) := by ring
  unfold payloadCode
  simp only [List.length_append,fresh_append,expand]
  refine ⟨Nat.add_le_add workRows ?_,Nat.add_le_add spaceRows ?_⟩
  all_goals
    split
    · exact Nat.zero_le _
    · rename_i matrix read
      have length : matrix.length ≤ width :=
        (map_length _ ((scan_value (matrixRow n) rows).symm.trans read)).trans_le rowFit
      obtain ⟨rowWork,rowSpace⟩ := array_code_paid matrix length
      obtain ⟨costWork,costSpace⟩ := array_code_paid costs costFit
      split
      · first
        | simpa only [List.length_append] using Nat.add_le_add rowWork costWork
        | simpa only [fresh_append] using Nat.add_le_add rowSpace costSpace
      · exact Nat.zero_le _

/-- This proof-side schedule includes row arrays built on unsuccessful inputs. -/
def vertexArrayCode (C M D : Table) : List (Instruction Unit) :=
  match (scan fraction C).1 with
  | none => []
  | some costs => payloadCode costs.length costs M fun matrix =>
      Read.bind (scan (pair costs.length) D) (vertexResult costs matrix)

def edgeArrayCode (C M D : Table) : List (Instruction Unit) :=
  match (scan fraction C).1 with
  | none => []
  | some costs => payloadCode M.length costs M fun matrix =>
      Read.bind (scan (pair M.length) D) (edgeResult M.length costs matrix)

def copyBudget (width : ℕ) : ℕ := (width+2)*workBound width
def allocationBudget (width : ℕ) : ℕ := (width+2)*spaceBound width

theorem vertex_array_paid {C M D : Table} {width : ℕ} (costs : C.length ≤ width) (rows : M.length ≤ width) :
    (vertexArrayCode C M D).length ≤ copyBudget width ∧ fresh (vertexArrayCode C M D) ≤ allocationBudget width := by
  unfold vertexArrayCode
  split
  · exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  · rename_i values read
    have fits := (map_length _ ((scan_value fraction C).symm.trans read)).trans_le costs
    exact payload_code_paid values M _ fits fits rows

theorem edge_array_paid {C M D : Table} {width : ℕ} (costs : C.length ≤ width) (rows : M.length ≤ width) :
    (edgeArrayCode C M D).length ≤ copyBudget width ∧ fresh (edgeArrayCode C M D) ≤ allocationBudget width := by
  unfold edgeArrayCode
  split
  · exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  · rename_i values read
    have fits := (map_length _ ((scan_value fraction C).symm.trans read)).trans_le costs
    exact payload_code_paid values M _ rows fits rows

end Arrays

end DirectedFlowCutGap.ChargedSourceAssembly
