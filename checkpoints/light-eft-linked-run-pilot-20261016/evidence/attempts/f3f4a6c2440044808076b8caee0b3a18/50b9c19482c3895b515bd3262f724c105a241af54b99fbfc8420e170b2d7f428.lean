import LightEFTSpanners.StoredForestBankExecutable

namespace LightEFTSpanners.StoredForestBank

def drawCount {n : ℕ} (bank : StoredDrawLookup.TypedBank n) : ℕ := (bank.map fun r => r.2.length).sum
def drawCells {n : ℕ} (bank : StoredDrawLookup.TypedBank n) : ℕ :=
  (bank.map fun r => (r.2.map List.length).sum).sum

theorem lookup_count {n : ℕ} (key : ℕ) (bank : StoredDrawLookup.TypedBank n) :
    (StoredDrawLookup.typedValue key bank).length ≤ drawCount bank := by
  induction bank with
  | nil => simp [StoredDrawLookup.typedValue,drawCount]
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    simp only [StoredDrawLookup.typedValue,drawCount,List.map_cons,List.sum_cons]
    split <;> simp_all [drawCount]; omega

theorem lookup_cells {n : ℕ} (key : ℕ) (bank : StoredDrawLookup.TypedBank n) :
    ((StoredDrawLookup.typedValue key bank).map List.length).sum ≤ drawCells bank := by
  induction bank with
  | nil => simp [StoredDrawLookup.typedValue,drawCells]
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    simp only [StoredDrawLookup.typedValue,drawCells,List.map_cons,List.sum_cons]
    split <;> simp_all [drawCells]; omega
end LightEFTSpanners.StoredForestBank
