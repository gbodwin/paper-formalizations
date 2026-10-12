import MinorFreeSpanners.FiniteGeometricStreamBound

/-! A finite weighted cover may overlap: nonnegative edge costs are paid at
least once, so summing the actual covering families is an upper bound. -/
namespace MinorFreeSpanners
open Finset

 theorem finite_cover_budget {E I : Type*} [DecidableEq E] [DecidableEq I]
    (edges : Finset E) (indices : Finset I) (family : I → Finset E) (w : E → ℝ)
    (hwE : ∀ e∈edges,0≤w e) (hwF : ∀ i∈indices,∀ e∈family i,0≤w e)
    (hcover : ∀ e∈edges,∃ i∈indices,e∈family i) :
    (∑ e∈edges,w e)≤∑ i∈indices,∑ e∈family i,w e := by
  have hpoint (e : E) (he : e∈edges) : w e≤∑ i∈indices,if e∈family i then w e else 0 := by
    obtain ⟨i,hi,hei⟩ := hcover e he
    have hp := Finset.single_le_sum (s:=indices) (f:=fun i => if e∈family i then w e else 0)
      (fun j _ => by split_ifs;exact hwE e he;exact le_rfl) hi
    simpa [hei] using hp
  calc
    (∑ e∈edges,w e)≤∑ e∈edges,∑ i∈indices,if e∈family i then w e else 0 :=
      Finset.sum_le_sum hpoint
    _=∑ i∈indices,∑ e∈edges,if e∈family i then w e else 0 := Finset.sum_comm
    _≤∑ i∈indices,∑ e∈family i,w e := by
      apply Finset.sum_le_sum
      intro i hi
      rw [←Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun e he => (Finset.mem_filter.mp he).2) (fun e he _ => hwF i hi e he)

end MinorFreeSpanners
