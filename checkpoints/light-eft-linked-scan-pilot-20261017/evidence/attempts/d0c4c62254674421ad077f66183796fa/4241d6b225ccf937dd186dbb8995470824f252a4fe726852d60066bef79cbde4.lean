import LightEFTSpanners.LinkedDistanceMachine
namespace LightEFTSpanners.LinkedDistance
open RationalDistance
variable (size : ℕ) (M : Matrix) (source target : ℕ) (budget : ℚ)
local notation "go" => transition size M source target budget

 theorem scan_trace (k : ℕ) (d : List Cell) (rs : Matrix) (ds out r l : List Cell) (z : Cell) :
    Executes go (min r.length l.length+1)
      (.scan k d rs ds out r l z) (.row k d rs ds (scan r l z::out)) := by
  induction r generalizing l z with
  | nil => exact Executes.one rfl
  | cons a as ih =>
    cases l with
    | nil => exact Executes.one rfl
    | cons b bs =>
      have h := Executes.cons (step:=go)
        (show go (.scan k d rs ds out (a::as) (b::bs) z)=
          some (.scan k d rs ds out as bs (best (addCell a b) z)) from rfl)
        (ih bs (best (addCell a b) z))
      convert h using 1 <;> simp

 theorem reverse_round_trace (k : ℕ) (xs out : List Cell) :
    Executes go (xs.length+1) (.revRound k xs out) (.round k (xs.reverse++out)) := by
  induction xs generalizing out with
  | nil => exact Executes.one rfl
  | cons x xs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Executes.cons (step:=go) rfl (ih (x::out))

 def rowTicks (d : List Cell) : Matrix → List Cell → ℕ :=
  fun rs => List.rec (motive := fun _ => List Cell → ℕ) (fun _ => 0)
    (fun r _ next ds => match ds with
      | [] => 0
      | _::as => min r.length d.length+3+next as) rs

 theorem rowTicks_nil (d ds : List Cell) : rowTicks d [] ds = 0 := rfl

 theorem rowTicks_cons_nil (d r : List Cell) (rs : Matrix) :
    rowTicks d (r::rs) [] = 0 := rfl

 theorem rowTicks_cons_cons (d r : List Cell) (rs : Matrix) (a : Cell) (as : List Cell) :
    rowTicks d (r::rs) (a::as) = min r.length d.length+3+rowTicks d rs as := rfl

-- Preserve definitional matching in the unchanged trace and arithmetic proofs.
attribute [reducible] rowTicks

 theorem rows_trace (k : ℕ) (d : List Cell) (rs : Matrix) (ds out : List Cell) :
    Executes go (rowTicks d rs ds+out.length+2)
      (.row k d rs ds out) (.round k (out.reverse++rows d rs ds)) := by
  induction rs generalizing ds out with
  | nil =>
    simpa [rowTicks,rows,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using (Executes.one (step:=go)
      (show go (.row k d [] ds out)=some (.revRound k out []) from rfl)).trans
        (reverse_round_trace size M source target budget k out [])
  | cons r rs ih =>
    cases ds with
    | nil =>
      simpa [rowTicks,rows,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using (Executes.one (step:=go)
        (show go (.row k d (r::rs) [] out)=some (.revRound k out []) from rfl)).trans
          (reverse_round_trace size M source target budget k out [])
    | cons a as =>
      have h := (Executes.one (step:=go)
        (show go (.row k d (r::rs) (a::as) out)=some (.scan k d rs as out r d a) from rfl)).trans
          ((scan_trace size M source target budget k d rs as out r d a).trans
            (ih as (scan r d a::out)))
      convert h using 1 <;> simp [rowTicks,rows,List.reverse_cons,List.append_assoc]
      omega

 theorem rowTicks_le (rs : Matrix) (ds d : List Cell) :
    rowTicks d rs ds≤rs.length*(d.length+3) := by
  induction rs generalizing ds with
  | nil => simp [rowTicks]
  | cons r rs ih =>
    cases ds with
    | nil => simp [rowTicks]
    | cons a as =>
      have h := ih as
      have hh := Nat.min_le_right r.length d.length
      simp only [rowTicks,List.length_cons]
      nlinarith

 theorem round_trace (k : ℕ) (d : List Cell) :
    ∃ t, t≤k*(M.length*(d.length+3)+3) ∧
      Executes go t (.round k d) (.round 0 (rounds M k d)) := by
  induction k generalizing d with
  | zero => exact ⟨0,by simp,Executes.refl _⟩
  | succ k ih =>
    obtain ⟨t,ht,he⟩ := ih (rows d M d)
    have hl : (rows d M d).length≤d.length := by rw [rows_length];exact Nat.min_le_right _ _
    have hrow := rows_trace size M source target budget k d M d []
    have h := (Executes.one (step:=go)
      (show go (.round (k+1) d)=some (.row k d M d []) from rfl)).trans (hrow.trans he)
    refine ⟨1+(rowTicks d M d+0+2)+t,?_,?_⟩
    · have hb := rowTicks_le M d d
      have hb' := Nat.mul_le_mul_left M.length (Nat.add_le_add_right hl 3)
      have hb'' := Nat.mul_le_mul_left k (Nat.add_le_add_right hb' 3)
      nlinarith
    · simpa only [List.length_nil,List.reverse_nil,List.nil_append,rounds,Nat.add_assoc] using h

end LightEFTSpanners.LinkedDistance
