import DirectedFlowCutGap.PhysicalSourceDispatch

/-! The packed source is emitted directly from typed graph fields. Framing
visits each stored bit, and the demand writer shares one table of labels. -/
namespace DirectedFlowCutGap.BinarySourceSerialization

open BinaryArithmetic BinaryFractionalGuesses

private def word (tail : Bits) : Bits → Bits × ℕ
  | [] => (false::tail,2)
  | b::bs =>
    let rest := word tail bs
    (true::b::rest.1,rest.2+4)

private theorem word_value (tail bs : Bits) :
    (word tail bs).1=SelfDelimitedWordProgram.encode bs++tail := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [word,SelfDelimitedWordProgram.encode,List.cons_append,ih]

private theorem word_paid (tail bs : Bits) : (word tail bs).2=4*bs.length+2 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [word,ih,List.length_cons]
    omega

private def table (tail : Bits) : List (Bits × Bits) → Bits × ℕ
  | [] => (false::tail,2)
  | (a,b)::xs =>
    let rows := table tail xs
    let second := word rows.1 b
    let first := word second.1 a
    (true::first.1,rows.2+second.2+first.2+12)

private theorem table_value (tail : Bits) (xs : List (Bits × Bits)) :
    (table tail xs).1=SourceRowTableProgram.encode xs++tail := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    simp only [table,word_value,ih,SourceRowTableProgram.encode,List.cons_append,List.append_assoc]

private theorem table_length (xs : List (Bits × Bits)) :
    (SourceRowTableProgram.encode xs).length=2*SourceRowTableProgram.bits xs+3*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    simp only [SourceRowTableProgram.encode,SelfDelimitedWordProgram.encode_length,SourceRowTableProgram.bits,
      List.length_cons,List.length_append,ih]
    omega

private theorem table_paid (tail : Bits) (xs : List (Bits × Bits)) :
    (table tail xs).2 ≤ 6*(SourceRowTableProgram.encode xs).length := by
  induction xs with
  | nil => simp [table, SourceRowTableProgram.encode]
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    rw [table_length] at ih ⊢
    simp only [table,word_paid,SourceRowTableProgram.bits,List.length_cons]
    omega

private def labels : ℕ → Bits → List Bits × ℕ
  | 0,_ => ([],4)
  | k+1,acc =>
    let next := increment true acc
    let rest := labels k next.1
    (acc::rest.1,rest.2+next.2+12*(k+2))

private theorem labels_value (k : ℕ) (acc : Bits) : (labels k acc).1=RowVertexScan.words k acc := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih => simp only [labels,RowVertexScan.words,ih]

private theorem labels_paid {width k : ℕ} {acc : Bits} (fits : acc.length+k ≤ width) :
    (labels k acc).2 ≤ k*(20*(width+2))+4 := by
  induction k generalizing acc with
  | zero => simp [labels]
  | succ k ih =>
    have step := increment_spec true acc
    have rest := ih (acc := (increment true acc).1) (by omega)
    simp only [labels,Nat.add_mul,Nat.one_mul]
    omega

private def demandTable {n : ℕ} (words : Vector Bits n) :
    List (BinaryFractionalWalkOracle.Pair n) → List (Bits × Bits) × ℕ
  | [] => ([],4)
  | (s,t)::ds =>
    let rest := demandTable words ds
    ((words[s],words[t])::rest.1,rest.2+24*(n+1))

private theorem demandTable_fields {n : ℕ} (words : Vector Bits n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (eq : ∀ i : Fin n, words[i]=RowVertices.vertexLabel i) :
    (demandTable words ds).1=SourcePacking.demandFields ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [demandTable,SourcePacking.demandFields,List.map_cons,ih,eq]

private theorem demandTable_paid {n : ℕ} (words : Vector Bits n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    (demandTable words ds).2=24*(n+1)*ds.length+4 := by
  induction ds with
  | nil => simp [demandTable]
  | cons d ds ih =>
    simp only [demandTable,ih,List.length_cons,Nat.mul_succ]
    omega

private def labelWords (n : ℕ) : Vector Bits n × ℕ :=
  let words := labels n []
  (⟨words.1.toArray,by rw [List.size_toArray, labels_value, RowVertexScan.words_length]⟩,words.2+12*(n+1))

private theorem labelWords_value (n : ℕ) (i : Fin n) : (labelWords n).1[i]=RowVertices.vertexLabel i := by
  simp [labelWords,RowVertices.vertexLabel,labels_value]

def run {n : ℕ} (D : Input n) : Bits × ℕ :=
  let stored := labelWords n
  let ds := demandTable stored.1 D.demands
  let dem := table [] ds.1
  let mat := table dem.1 (SourcePacking.matrixFields D.adjacency)
  let cap := table mat.1 (SourcePacking.capacityFields D.costs)
  let fieldConstruction := 24*(n+1)^2
  (cap.1,stored.2+ds.2+dem.2+mat.2+cap.2+fieldConstruction+16)

@[simp] theorem run_value {n : ℕ} (D : Input n) : (run D).1=PhysicalSourceDispatch.input D := by
  simp only [run,demandTable_fields _ _ (labelWords_value n),table_value,List.append_nil,
    PhysicalSourceDispatch.input,SourcePacking.encode,PackingSourceInput.encode,List.append_assoc]

def budget {R : Type*} [Semiring R] (x : R) : R := 80*(x+2)^2+16

theorem budget_mono {a b : ℕ} (h : a ≤ b) : budget a ≤ budget b := by
  unfold budget
  gcongr

open Polynomial in
theorem budget_eval (p : Polynomial ℕ) (x : ℕ) :
    (budget p).eval x=budget (p.eval x) := by
  simp only [budget,eval_add,eval_mul,eval_pow,eval_ofNat]

theorem input_dimensions {n : ℕ} (D : Input n) :
    n+1 ≤ (PhysicalSourceDispatch.input D).length := by
  let C := SourcePacking.capacityFields D.costs
  have rows : C.length=n := by simp [C,SourcePacking.capacityFields,IndexedRationalRead.fields]
  have length := table_length C
  change n+1 ≤ (PackingSourceInput.encode C _ _).length
  simp only [PackingSourceInput.encode,List.length_append]
  omega

set_option maxHeartbeats 800000 in
theorem run_paid {n : ℕ} (D : Input n) : (run D).2 ≤ budget (PhysicalSourceDispatch.input D).length := by
  let stored := labelWords n
  let ds := demandTable stored.1 D.demands
  let c := SourcePacking.capacityFields D.costs
  let m := SourcePacking.matrixFields D.adjacency
  let d := SourcePacking.demandFields D.demands
  let L := (PhysicalSourceDispatch.input D).length
  have hd : ds.1=d := demandTable_fields _ _ (labelWords_value n)
  have hL : L=(SourceRowTableProgram.encode c).length+(SourceRowTableProgram.encode m).length+
      (SourceRowTableProgram.encode d).length := by
    change (PackingSourceInput.encode c m d).length=_
    simp only [PackingSourceInput.encode,List.length_append]
  have hc : c.length=n := by simp [c,SourcePacking.capacityFields,IndexedRationalRead.fields]
  have hds : d.length=D.demands.length := by simp [d,SourcePacking.demandFields]
  have hn : n ≤ L := by
    have h := table_length c
    omega
  have hdem : D.demands.length ≤ L := by
    have h := table_length d
    omega
  have hlabel : stored.2 ≤ n*(20*(n+2))+4+12*(n+1) :=
    Nat.add_le_add_right (labels_paid (width:=n) (k:=n) (acc:=[]) (by simp)) _
  have hdc : ds.2=24*(n+1)*D.demands.length+4 := demandTable_paid _ _
  have htd : (table [] ds.1).2 ≤ 6*(SourceRowTableProgram.encode d).length :=
    (table_paid [] ds.1).trans_eq (congrArg (fun xs => 6*(SourceRowTableProgram.encode xs).length) hd)
  have htm := table_paid (table [] ds.1).1 m
  have htc := table_paid (table (table [] ds.1).1 m).1 c
  have hlabel' : n*(20*(n+2))+4+12*(n+1) ≤ L*(20*(L+2))+4+12*(L+1) := by gcongr
  have hdc' : 24*(n+1)*D.demands.length ≤ 24*(L+1)*L := by gcongr
  have hfields : 24*(n+1)^2 ≤ 24*(L+1)^2 := by gcongr
  change stored.2+ds.2+(table [] ds.1).2+(table (table [] ds.1).1 m).2+
    (table (table (table [] ds.1).1 m).1 c).2+24*(n+1)^2+16 ≤ budget L
  have enclosure : L*(20*(L+2))+4+12*(L+1)+24*(L+1)*L+4+6*L+24*(L+1)^2+16 ≤ budget L := by
    unfold budget
    nlinarith only
  omega

end DirectedFlowCutGap.BinarySourceSerialization
