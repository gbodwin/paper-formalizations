import LightEFTSpanners.SampledHostExpectation

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners
variable {V J : Type*} [DecidableEq V] [DecidableEq J]
attribute [local instance] Classical.propDecidable

omit [DecidableEq J] in
theorem approved_record {Q : Finset (Sym2 V)} {w : Sym2 V → ℝ} {t : ℝ} {f h : ℕ}
    {eligible : Sym2 V → Finset J} {host : J → Finset (Sym2 V)}
    {rs : List (Sym2 V × Finset J)} (hg : ApprovedHistory Q w t f h eligible host rs)
    {e : Sym2 V} {A : Finset J} (hm : (e,A)∈rs) : A⊆eligible e ∧ h≤A.card := by
  induction rs with
  | nil => simp at hm
  | cons r rs ih =>
    obtain ⟨d,B⟩ := r
    obtain ⟨hg,hsub,hcard,_⟩ := hg
    rcases List.mem_cons.mp hm with heq | hm
    · cases heq;exact ⟨hsub,hcard⟩
    · exact ih hg hm

/-- Every accepted original edge contributes its weight once to each literal
voting host. The actual admission threshold supplies the multiplicity. -/
theorem voting_weight_incidence (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (f h : ℕ) (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (indices : Finset J) (rs : List (Sym2 V × Finset J))
    (hsub : ∀ e∈rs.map Prod.fst,eligible e⊆indices)
    (hw : ∀ e∈rs.map Prod.fst,0≤w e)
    (hg : ApprovedHistory Q w t f h eligible host rs) :
    (h:ℝ)*(rs.map (fun r => w r.1)).sum≤∑ j∈indices,assignedWeight w j rs := by
  induction rs with
  | nil => simp [assignedWeight]
  | cons r rs ih =>
    obtain ⟨e,A⟩ := r
    obtain ⟨hg,hA,hcard,_⟩ := hg
    have hin (d) (hd : d∈rs.map Prod.fst) : d∈((e,A)::rs).map Prod.fst :=
      List.mem_cons_of_mem e hd
    have hi := ih (fun d hd => hsub d (hin d hd)) (fun d hd => hw d (hin d hd)) hg
    have hwe := hw e (by simp)
    have hAsub : A⊆indices := hA.trans (hsub e (by simp))
    have hfilt : indices.filter (fun j => j∈A)=A := by
      ext j;simp only [mem_filter];exact ⟨And.right,fun hj => ⟨hAsub hj,hj⟩⟩
    have heq : (∑ j∈indices,if j∈A then w e else 0)=(A.card:ℝ)*w e := by
      rw [←sum_filter,hfilt];simp
    have hc : (h:ℝ)≤A.card := by exact_mod_cast hcard
    have hm := mul_le_mul_of_nonneg_right hc hwe
    simp only [List.map_cons,List.sum_cons,assignedWeight,sum_add_distrib,mul_add]
    apply add_le_add _ hi
    apply hm.trans_eq
    calc
      _ = ∑ j∈indices,if j∈A then w e else 0 := heq.symm
      _ = _ := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j∈A <;> simp only [hj,ite_true,ite_false]
end LightEFTSpanners.SampledGreedy
