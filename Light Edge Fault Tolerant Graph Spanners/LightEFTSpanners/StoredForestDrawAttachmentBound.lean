import LightEFTSpanners.StoredForestDrawAttachment

namespace LightEFTSpanners.StoredForestDrawAttachment
open Controller

theorem reverse_trace (n : ℕ) (bank : StoredDrawLookup.Bank)
    (rs out : List StoredComponentRecord.Input) :
    Trace (transition n bank) (rs.length+1) (.reverse rs out) (.halt (rs.reverse++out)) := by
  induction rs generalizing out with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n bank (.reverse (r::rs) out)=some (.reverse rs (r::out)) from rfl) (ih (r::out))

def steps (n : ℕ) (bank : StoredDrawLookup.Bank) (rs : List Record) : ℕ := scanSteps n bank rs+rs.length+1

theorem attachment_trace (n : ℕ) (bank : StoredDrawLookup.Bank) (rs : List Record) :
    Trace (transition n bank) (steps n bank rs) (.records rs []) (.halt (value n bank rs)) := by
  have a := scan_trace n bank rs []
  simp only [List.append_nil] at a
  have b := reverse_trace n bank (value n bank rs).reverse []
  simpa [steps,value,Nat.add_assoc] using a.trans b

theorem scanSteps_le (n : ℕ) (bank : StoredDrawLookup.Bank) (rs : List Record) :
    scanSteps n bank rs≤rs.length*(bank.length+3)+1 := by
  induction rs with
  | nil => simp [scanSteps_nil]
  | cons r rs ih =>
    have h := StoredDrawLookup.steps_le (key n r) bank
    simp only [scanSteps_cons,List.length_cons,Nat.add_mul]
    omega

def bound (bank : StoredDrawLookup.Bank) (q : ℕ) : ℕ := q*(bank.length+4)+2

theorem steps_le (n : ℕ) (bank : StoredDrawLookup.Bank) (rs : List Record) :
    steps n bank rs≤bound bank rs.length := by
  have h := scanSteps_le n bank rs
  unfold steps bound
  have he : rs.length*(bank.length+4)=rs.length*(bank.length+3)+rs.length := by ring
  rw [he]
  omega
end LightEFTSpanners.StoredForestDrawAttachment
