import DirectedFlowCutGap.EncodedVertexInput
import DirectedFlowCutGap.PhysicalCoverAccess

/-! Count the actual parsing of the three framed source tables. The framing
budget pays malformed inputs, including a truncated word or table. -/

namespace DirectedFlowCutGap.ChargedSourceTables

open BinaryArithmetic EncodedVertexInput
open PhysicalCoverAccess (Read)

private def tailLength {A : Type} (r : Read (A × Bits)) : ℕ :=
  (r.1.map (fun a => a.2.length)).getD 0

private theorem bind_value {A B : Type} (r : Read A) (k : A → Read B) :
    (Read.bind r k).1 = r.1.bind (fun a => (k a).1) := Read.bind_value r k

def word : Bits → Read (Bits × Bits)
  | false::rest => (some ([],rest),2)
  | true::b::rest =>
    let r := word rest
    (r.1.map (fun (bits,tail) => (b::bits,tail)),r.2+4)
  | _ => (none,2)

theorem word_value (source : Bits) : (word source).1=readWord source := by
  induction source using word.induct with
  | case1 rest => rfl
  | case2 b rest ih => simp only [word,readWord,ih]
  | case3 source no no' =>
    cases source with
    | nil => rfl
    | cons b rest =>
      cases b
      · exact (no rest rfl).elim
      · cases rest with
        | nil => rfl
        | cons b rest => exact (no' b rest rfl).elim

private theorem word_paid (source : Bits) :
    (word source).2+32*tailLength (word source) ≤ 32*source.length+4 := by
  induction source using word.induct with
  | case1 rest => simp [word,tailLength]; omega
  | case2 b rest ih =>
    cases h : (word rest).1 with
    | none => simp only [word,tailLength,h,Option.map_none,Option.getD_none,List.length_cons] at *; omega
    | some result =>
      rcases result with ⟨bs,tail⟩
      simp only [word,tailLength,h,Option.map_some,Option.getD_some,List.length_cons] at *
      omega
  | case3 source no no' =>
    have h : word source=(none,2) := by
      cases source with
      | nil => rfl
      | cons b rest =>
        cases b
        · exact (no rest rfl).elim
        · cases rest with
          | nil => rfl
          | cons b rest => exact (no' b rest rfl).elim
    rw [h]
    simp [tailLength]

def rows : ℕ → Bits → Read (Table × Bits)
  | 0,_ => (none,2)
  | _+1,[] => (none,2)
  | _+1,false::rest => (some ([],rest),2)
  | fuel+1,true::rest =>
    let r := Read.bind (word rest) fun (a,afterA) =>
      Read.bind (word afterA) fun (b,afterB) =>
        Read.bind (rows fuel afterB) fun (more,tail) =>
          (pure ((a,b)::more,tail) : Read (Table × Bits))
    (r.1,r.2+8)

theorem rows_value (fuel : ℕ) (source : Bits) : (rows fuel source).1=readRows fuel source := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    cases source with
    | nil => rfl
    | cons b rest =>
      cases b
      · rfl
      · simp only [rows,readRows,bind_value,Read.pure_value,word_value,ih]
        rfl

private theorem rows_paid (fuel : ℕ) (source : Bits) :
    (rows fuel source).2+32*tailLength (rows fuel source) ≤ 32*source.length+4 := by
  induction fuel generalizing source with
  | zero => simp [rows,tailLength]
  | succ fuel ih =>
    cases source with
    | nil => simp [rows,tailLength]
    | cons b rest =>
      cases b with
      | false => simp [rows,tailLength]; omega
      | true =>
        have aPaid := word_paid rest
        cases a : (word rest).1 with
        | none =>
          simp [rows,Read.bind,tailLength,a] at *
          omega
        | some aFields =>
          rcases aFields with ⟨w,afterA⟩
          have bPaid := word_paid afterA
          cases b : (word afterA).1 with
          | none =>
            simp [rows,Read.bind,tailLength,a,b] at *
            omega
          | some bFields =>
            rcases bFields with ⟨v,afterB⟩
            have more := ih afterB
            cases tail : (rows fuel afterB).1 with
            | none =>
              simp [rows,Read.bind,tailLength,a,b,tail] at *
              omega
            | some answer =>
              rcases answer with ⟨out,rest'⟩
              simp [rows,Read.bind,tailLength,a,b,tail] at *
              omega

def table (source : Bits) : Read (Table × Bits) :=
  let r := rows source.length source
  (r.1,r.2+source.length+3)

theorem table_value (source : Bits) : (table source).1=readTable source := rows_value _ _

private theorem table_paid (source : Bits) :
    (table source).2+32*tailLength (table source) ≤ 33*source.length+8 := by
  have h := rows_paid source.length source
  change (rows source.length source).2+source.length+3+32*tailLength (rows source.length source) ≤ _
  omega

private theorem table_tail (source : Bits) : tailLength (table source) ≤ source.length := by
  have h := rows_paid source.length source
  change tailLength (rows source.length source) ≤ source.length
  omega

def tables (source : Bits) : Read (Table × Table × Table × Bits) :=
  let r := Read.bind (table source) fun (c,afterC) =>
    Read.bind (table afterC) fun (m,afterM) =>
      Read.bind (table afterM) fun (d,rest) =>
        (pure (c,m,d,rest) : Read (Table × Table × Table × Bits))
  (r.1,r.2+10)

theorem tables_value (source : Bits) : (tables source).1=readTables source := by
  simp only [tables,readTables,bind_value,Read.pure_value,table_value]
  rfl

theorem tables_paid (source : Bits) : (tables source).2 ≤ 35*source.length+34 := by
  have cap := table_paid source
  cases c : (table source).1 with
  | none =>
    simp only [tailLength,c,Option.map_none,Option.getD_none] at cap
    simp [tables,Read.bind,c]
    omega
  | some first =>
    rcases first with ⟨costs,afterC⟩
    have matrix := table_paid afterC
    have tailC := table_tail source
    simp only [tailLength,c,Option.map_some,Option.getD_some] at tailC
    cases m : (table afterC).1 with
    | none =>
      simp only [tailLength,c,m,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none] at cap matrix
      simp [tables,Read.bind,c,m]
      omega
    | some second =>
      rcases second with ⟨adj,afterM⟩
      have demands := table_paid afterM
      have tailM := table_tail afterC
      simp only [tailLength,m,Option.map_some,Option.getD_some] at tailM
      simp only [tailLength,c,m,Option.map_some,Option.getD_some] at cap matrix
      cases d : (table afterM).1 <;> simp [tables,Read.bind,c,m,d] <;> omega

private theorem word_wire {source content rest : Bits} (parsed : (word source).1 = some (content,rest)) :
    source=SelfDelimitedWordProgram.encode content++rest := by
  induction source using word.induct generalizing content rest with
  | case1 tail =>
    simp only [word,Option.some.injEq,Prod.mk.injEq] at parsed
    rcases parsed with ⟨rfl,rfl⟩
    rfl
  | case2 b tail ih =>
    cases h : (word tail).1 with
    | none => simp [word,h] at parsed
    | some data =>
      rcases data with ⟨bits,next⟩
      simp only [word,h,Option.map_some,Option.some.injEq,Prod.mk.injEq] at parsed
      rcases parsed with ⟨rfl,rfl⟩
      rw [ih h]
      rfl
  | case3 source no no' =>
    cases source with
    | nil => simp [word] at parsed
    | cons b tail =>
      cases b
      · exact (no tail rfl).elim
      · cases tail with
        | nil => simp [word] at parsed
        | cons b tail => exact (no' b tail rfl).elim

private theorem rows_wire {fuel : ℕ} {source rest : Bits} {data : Table}
    (parsed : (rows fuel source).1=some (data,rest)) : source=SourceRowTableProgram.encode data++rest := by
  induction fuel generalizing source rest data with
  | zero => simp [rows] at parsed
  | succ fuel ih =>
    cases source with
    | nil => simp [rows] at parsed
    | cons b tail =>
      cases b with
      | false =>
        simp only [rows,Option.some.injEq,Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl,rfl⟩
        rfl
      | true =>
        cases a : (word tail).1 with
        | none => simp [rows,Read.bind,a] at parsed
        | some first =>
          rcases first with ⟨u,afterA⟩
          cases b : (word afterA).1 with
          | none => simp [rows,Read.bind,a,b] at parsed
          | some second =>
            rcases second with ⟨v,afterB⟩
            cases next : (rows fuel afterB).1 with
            | none => simp [rows,Read.bind,a,b,next] at parsed
            | some later =>
              rcases later with ⟨suffixData,endBits⟩
              simp only [rows,Read.bind,a,b,next,Read.pure_value,Option.some.injEq,Prod.mk.injEq] at parsed
              rcases parsed with ⟨rfl,rfl⟩
              rw [word_wire a,word_wire b,ih next]
              simp only [SourceRowTableProgram.encode,List.cons_append,List.append_assoc]

theorem tables_wire {source rest : Bits} {costs matrix demands : Table}
    (parsed : (tables source).1=some (costs,matrix,demands,rest)) :
    source=PackingSourceInput.encode costs matrix demands++rest := by
  cases c : (table source).1 with
  | none => simp [tables,Read.bind,c] at parsed
  | some first =>
    rcases first with ⟨cost,afterC⟩
    cases m : (table afterC).1 with
    | none => simp [tables,Read.bind,c,m] at parsed
    | some second =>
      rcases second with ⟨rows,afterM⟩
      cases d : (table afterM).1 with
      | none => simp [tables,Read.bind,c,m,d] at parsed
      | some third =>
        rcases third with ⟨pairs,tail⟩
        simp only [tables,Read.bind,c,m,d,Read.pure_value,Option.some.injEq,Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl,rfl,rfl,rfl⟩
        rw [rows_wire (fuel:=source.length) c,rows_wire (fuel:=afterC.length) m,rows_wire (fuel:=afterM.length) d]
        simp only [PackingSourceInput.encode,List.append_assoc]

end DirectedFlowCutGap.ChargedSourceTables
