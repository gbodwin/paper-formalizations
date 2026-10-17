import LightEFTSpanners.StoredComponentVertices

namespace LightEFTSpanners.StoredVertexMinimum
open Controller
inductive State where
  | scan : List ℕ → ℕ → State
  | halt : ℕ → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .scan [] best => some (.halt best)
  | .scan (v::vs) best => some (.scan vs (min best v))
  | .halt _ => none

def value (vs : List ℕ) (best : ℕ) : ℕ := vs.foldl min best

theorem scan_trace (vs : List ℕ) (best : ℕ) :
    Trace transition (vs.length+1) (.scan vs best) (.halt (value vs best)) := by
  induction vs generalizing best with
  | nil => exact Trace.one rfl
  | cons v vs ih =>
    simpa [value] using Trace.cons
      (show transition (.scan (v::vs) best)=some (.scan vs (min best v)) from rfl) (ih (min best v))

theorem value_le (vs : List ℕ) (best : ℕ) : value vs best≤best := by
  induction vs generalizing best with
  | nil => exact le_rfl
  | cons v vs ih => exact (ih (min best v)).trans (min_le_left _ _)

theorem value_le_mem (vs : List ℕ) (best v : ℕ) (hv : v∈vs) : value vs best≤v := by
  induction vs generalizing best with
  | nil => simp at hv
  | cons x xs ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (value_le xs (min best v)).trans (min_le_right _ _)
    · exact ih (min best x) hv

theorem value_mem_or (vs : List ℕ) (best : ℕ) : value vs best=best ∨ value vs best∈vs := by
  induction vs generalizing best with
  | nil => exact Or.inl rfl
  | cons v vs ih =>
    rcases ih (min best v) with he | hm
    · by_cases h : best≤v
      · exact Or.inl (he.trans (min_eq_left h))
      · exact Or.inr (List.mem_cons.mpr (Or.inl (he.trans (min_eq_right (by omega)))))
    · exact Or.inr (List.mem_cons_of_mem _ hm)

theorem value_mem (vs : List ℕ) (best : ℕ) (hb : best∈vs) : value vs best∈vs := by
  rcases value_mem_or vs best with he | hm
  · simpa only [he] using hb
  · exact hm
end LightEFTSpanners.StoredVertexMinimum
