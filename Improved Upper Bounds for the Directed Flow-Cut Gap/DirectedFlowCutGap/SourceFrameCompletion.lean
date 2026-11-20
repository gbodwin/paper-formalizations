import DirectedFlowCutGap.PackingSourceInputExecution

/-! Every source has a three-table framing completion with at most six zero
bits. The padding is a proof witness for the interpreter's exhaustion behavior. -/
namespace DirectedFlowCutGap.SourceFrameCompletion

open BinaryArithmetic

private theorem word_completion (source : Bits) :
    (∃ word rest, source = SelfDelimitedWordProgram.encode word ++ rest) ∨
      ∃ word k, k ≤ 2 ∧ source ++ List.replicate k false = SelfDelimitedWordProgram.encode word := by
  cases source with
  | nil => exact .inr ⟨[],1,by decide,rfl⟩
  | cons marker rest =>
    cases marker with
    | false => exact .inl ⟨[],rest,rfl⟩
    | true =>
      cases rest with
      | nil => exact .inr ⟨[false],2,by decide,rfl⟩
      | cons b tail =>
        rcases word_completion tail with ⟨word,suffix,eq⟩ | ⟨word,k,hk,eq⟩
        · exact .inl ⟨b::word,suffix,by rw [eq]; rfl⟩
        · exact .inr ⟨b::word,k,hk,by simp only [SelfDelimitedWordProgram.encode,List.cons_append,eq]⟩

private theorem word_prefix_shorter {source word rest : Bits}
    (eq : source = SelfDelimitedWordProgram.encode word ++ rest) : rest.length < source.length := by
  rw [eq,List.length_append,SelfDelimitedWordProgram.encode_length]
  omega

private theorem table_completion (source : Bits) :
    (∃ rows rest, source = SourceRowTableProgram.encode rows ++ rest) ∨
      ∃ rows k, k ≤ 4 ∧ source ++ List.replicate k false = SourceRowTableProgram.encode rows := by
  cases source with
  | nil => exact .inr ⟨[],1,by decide,rfl⟩
  | cons marker rest =>
    cases marker with
    | false => exact .inl ⟨[],rest,rfl⟩
    | true =>
      rcases word_completion rest with ⟨a,afterA,ha⟩ | ⟨a,k,hk,ha⟩
      · rcases word_completion afterA with ⟨b,afterB,hb⟩ | ⟨b,k,hk,hb⟩
        · have shorterA := word_prefix_shorter ha
          have shorterB := word_prefix_shorter hb
          rcases table_completion afterB with ⟨rs,tail,ht⟩ | ⟨rs,k,hk,ht⟩
          · exact .inl ⟨(a,b)::rs,tail,by
              simp only [ha,hb,ht,SourceRowTableProgram.encode,List.cons_append,List.append_assoc]⟩
          · exact .inr ⟨(a,b)::rs,k,hk,by
              simp only [ha,hb,List.cons_append,List.append_assoc,ht,SourceRowTableProgram.encode]⟩
        · exact .inr ⟨[(a,b)],k+1,by omega,by
            simp only [ha,List.replicate_add,List.cons_append,List.append_assoc,← List.append_assoc afterA,hb,
              SourceRowTableProgram.encode]
            rfl⟩
      · exact .inr ⟨[(a,[])],k+2,by omega,by
          simp only [List.replicate_add,List.cons_append,← List.append_assoc rest,ha,SourceRowTableProgram.encode]
          simp only [SelfDelimitedWordProgram.encode,List.append_assoc,List.replicate_succ,List.replicate_zero,
            List.cons_append,List.nil_append]⟩
termination_by source.length
decreasing_by simp only [List.length_cons]; omega

theorem all (source : Bits) :
    ∃ k ≤ 6, ∃ costs matrix demands suffix,
      source ++ List.replicate k false = PackingSourceInput.encode costs matrix demands ++ suffix := by
  rcases table_completion source with ⟨costs,afterC,hc⟩ | ⟨costs,k,hk,hc⟩
  · rcases table_completion afterC with ⟨matrix,afterM,hm⟩ | ⟨matrix,k,hk,hm⟩
    · rcases table_completion afterM with ⟨demands,suffix,hd⟩ | ⟨demands,k,hk,hd⟩
      · exact ⟨0,by decide,costs,matrix,demands,suffix,by
          simp only [hc,hm,hd,List.replicate_zero,List.append_nil,PackingSourceInput.encode,List.append_assoc]⟩
      · exact ⟨k,by omega,costs,matrix,demands,[],by
          simp only [hc,hm,List.append_assoc,hd,PackingSourceInput.encode,List.append_nil]⟩
    · exact ⟨k+1,by omega,costs,matrix,[],[],by
        rw [hc,List.replicate_add,List.append_assoc,← List.append_assoc afterC,hm]
        simp [PackingSourceInput.encode,SourceRowTableProgram.encode,List.append_assoc]⟩
  · exact ⟨k+2,by omega,costs,[],[],[],by
      simp only [List.replicate_add,← List.append_assoc source,hc,PackingSourceInput.encode,
        SourceRowTableProgram.encode,List.append_nil]
      simp only [List.append_assoc,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]⟩

private theorem word_unique {a b x y : Bits}
    (eq : SelfDelimitedWordProgram.encode a ++ x = SelfDelimitedWordProgram.encode b ++ y) :
    a = b ∧ x = y := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa [SelfDelimitedWordProgram.encode] using eq
    | cons bit word => simp [SelfDelimitedWordProgram.encode] at eq
  | cons bit word ih =>
    cases b with
    | nil => simp [SelfDelimitedWordProgram.encode] at eq
    | cons bit' word' =>
      simp only [SelfDelimitedWordProgram.encode,List.cons_append,List.cons.injEq,true_and] at eq
      obtain ⟨rfl,rest⟩ := eq
      obtain ⟨rfl,rfl⟩ := ih rest
      exact ⟨rfl,rfl⟩

private theorem table_unique {a b : List (Bits × Bits)} {x y : Bits}
    (eq : SourceRowTableProgram.encode a ++ x = SourceRowTableProgram.encode b ++ y) :
    a = b ∧ x = y := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa [SourceRowTableProgram.encode] using eq
    | cons row rows => simp [SourceRowTableProgram.encode] at eq
  | cons row rows ih =>
    cases b with
    | nil => simp [SourceRowTableProgram.encode] at eq
    | cons row' rows' =>
      have fields : SelfDelimitedWordProgram.encode row.1 ++ (SelfDelimitedWordProgram.encode row.2 ++
          (SourceRowTableProgram.encode rows ++ x)) = SelfDelimitedWordProgram.encode row'.1 ++
          (SelfDelimitedWordProgram.encode row'.2 ++ (SourceRowTableProgram.encode rows' ++ y)) := by
        simpa [SourceRowTableProgram.encode,List.append_assoc] using eq
      obtain ⟨num,second⟩ := word_unique fields
      obtain ⟨den,rest⟩ := word_unique second
      obtain ⟨rfl,rfl⟩ := ih rest
      have same : row = row' := Prod.ext num den
      exact ⟨congrArg (fun r => r::rows) same,rfl⟩

theorem unique {c m d c' m' d' : List (Bits × Bits)} {x y : Bits}
    (eq : PackingSourceInput.encode c m d ++ x = PackingSourceInput.encode c' m' d' ++ y) :
    c = c' ∧ m = m' ∧ d = d' ∧ x = y := by
  simp only [PackingSourceInput.encode,List.append_assoc] at eq
  obtain ⟨rfl,matrix⟩ := table_unique eq
  obtain ⟨rfl,demands⟩ := table_unique matrix
  obtain ⟨rfl,rfl⟩ := table_unique demands
  exact ⟨rfl,rfl,rfl,rfl⟩

end DirectedFlowCutGap.SourceFrameCompletion
