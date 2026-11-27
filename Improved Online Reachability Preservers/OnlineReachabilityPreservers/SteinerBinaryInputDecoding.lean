import OnlineReachabilityPreservers.SteinerBinaryFinOutputWork

/-! Semantics and work for decoding raw binary labels at the solver boundary. -/

namespace OnlineReachabilityPreservers

/-- Successful decoding keeps the values, order, and multiplicities of
all endpoints in the supplied words. -/
theorem decodeBinaryFinArcRowsWithWork_eq_some_iff {n : ℕ} (width : ℕ)
    (words : List (List Bool × List Bool)) (rows : List (Fin n × Fin n)) :
    (decodeBinaryFinArcRowsWithWork (n := n) width words).1 = some rows ↔
      rows.map (fun row => (row.1.val,row.2.val)) =
        words.map (fun row => (binaryWordValue row.1,binaryWordValue row.2)) := by
  induction words generalizing rows with
  | nil => cases rows <;> simp [decodeBinaryFinArcRowsWithWork]
  | cons word rest ih =>
    let a := binaryWordValue word.1
    let b := binaryWordValue word.2
    by_cases good : a < n ∧ b < n
    · let edge : Fin n × Fin n := (⟨a,good.1⟩,⟨b,good.2⟩)
      have head : (decodeBinaryFinArcRowsWithWork (n := n) width (word::rest)).1 =
          ((decodeBinaryFinArcRowsWithWork (n := n) width rest).1.map (edge::·)) := by
        simp only [decodeBinaryFinArcRowsWithWork,decodeBinaryNatWithWork_spec]
        rw [dite_eq_left good]
      rw [head]
      cases rows with
      | nil => simp [Option.map_eq_some_iff]
      | cons row rows =>
        rw [List.map_cons,List.map_cons,List.cons.injEq]
        constructor
        · intro found
          obtain ⟨kept,tail,equal⟩ := Option.map_eq_some_iff.mp found
          have input := List.cons.inj equal
          refine ⟨?_,(ih _).mp (input.2 ▸ tail)⟩
          rw [← input.1]
        · rintro ⟨values,tail⟩
          have rowExact : edge = row := by
            exact Prod.ext (Fin.ext (congrArg Prod.fst values).symm) (Fin.ext (congrArg Prod.snd values).symm)
          exact Option.map_eq_some_iff.mpr ⟨rows,(ih _).mpr tail,by rw [rowExact]⟩
    · have absent : (decodeBinaryFinArcRowsWithWork (n := n) width (word::rest)).1 = none := by
        simp only [decodeBinaryFinArcRowsWithWork,decodeBinaryNatWithWork_spec]
        rw [dite_eq_right good]
      rw [absent]
      cases rows with
      | nil => simp
      | cons row rows =>
        rw [List.map_cons,List.map_cons,List.cons.injEq]
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨values,_⟩
          have left := congrArg Prod.fst values
          have right := congrArg Prod.snd values
          change row.1.val = a at left
          change row.2.val = b at right
          exact (good ⟨left ▸ row.1.isLt,right ▸ row.2.isLt⟩).elim

/-- Every word pair whose two endpoint values fit the finite vertex
type is decoded, including empty input and repeated pairs. -/
theorem decodeBinaryFinArcRowsWithWork_some_iff_valid {n : ℕ} (width : ℕ)
    (words : List (List Bool × List Bool)) :
    (∃ rows, (decodeBinaryFinArcRowsWithWork (n := n) width words).1 = some rows) ↔
      ∀ word ∈ words, binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n := by
  constructor
  · rintro ⟨rows,decoded⟩ word present
    have exactRows := (decodeBinaryFinArcRowsWithWork_eq_some_iff width words rows).mp decoded
    have on : (binaryWordValue word.1,binaryWordValue word.2) ∈
        rows.map (fun row : Fin n × Fin n => (row.1.val,row.2.val)) := by
      rw [exactRows]
      exact List.mem_map_of_mem present
    obtain ⟨row,_,equals⟩ := List.mem_map.mp on
    have left : row.1.val = binaryWordValue word.1 := congrArg Prod.fst equals
    have right : row.2.val = binaryWordValue word.2 := congrArg Prod.snd equals
    exact ⟨left ▸ row.1.isLt,right ▸ row.2.isLt⟩
  · intro valid
    induction words with
    | nil => exact ⟨[],rfl⟩
    | cons word rest ih =>
      have each : ∀ w ∈ rest, binaryWordValue w.1 < n ∧ binaryWordValue w.2 < n :=
        fun w hit => valid w (List.mem_cons_of_mem _ hit)
      obtain ⟨tail,decoded⟩ := ih each
      have bound := valid word (List.mem_cons_self)
      refine ⟨(⟨binaryWordValue word.1,bound.1⟩,⟨binaryWordValue word.2,bound.2⟩)::tail,?_⟩
      apply (decodeBinaryFinArcRowsWithWork_eq_some_iff width (word::rest) _).mpr
      simp only [List.map_cons,List.cons.injEq,true_and]
      exact (decodeBinaryFinArcRowsWithWork_eq_some_iff width rest tail).mp decoded

/-- The work budget applies to every input of the given endpoint width,
including inputs the decoder rejects. -/
theorem decodeBinaryFinArcRowsWithWork_work_le_of_width {n : ℕ} (width : ℕ)
    (words : List (List Bool × List Bool))
    (bounds : ∀ word ∈ words, word.1.length ≤ width ∧ word.2.length ≤ width) :
    (decodeBinaryFinArcRowsWithWork (n := n) width words).2 ≤
      binaryFinArcDecodingWorkBudget words.length width := by
  induction words with
  | nil => simp [decodeBinaryFinArcRowsWithWork,binaryFinArcDecodingWorkBudget]
  | cons word rest ih =>
    have pairWidth := bounds word List.mem_cons_self
    have left := Nat.mul_le_mul_right (2*(width+1)+5) pairWidth.1
    have right := Nat.mul_le_mul_right (2*(width+1)+5) pairWidth.2
    have tail := ih (fun w on => bounds w (List.mem_cons_of_mem _ on))
    simp only [decodeBinaryFinArcRowsWithWork,decodeBinaryNatWithWork_spec]
    split <;> simp only [List.length_cons,binaryFinArcDecodingWorkBudget,Nat.add_mul,Nat.one_mul] at * <;>
      omega

end OnlineReachabilityPreservers
