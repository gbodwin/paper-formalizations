import LightEFTSpanners.SampledPrefixProbability

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners LightSpanners.FiniteSampling
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

noncomputable def retainedWeight (T : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (j : J) (S : Finset (Sym2 V)) (rs : List (Sym2 V × Finset J)) : ℝ :=
  ∑ e∈greedyEdges T w t 0 (selectedList j S rs)\T,w e

noncomputable def expectedRetainedWeight (T : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t p : ℝ) (j : J) (rs : List (Sym2 V × Finset J)) : ℝ :=
  ∑ S∈(rs.map Prod.fst).toFinset.powerset,
    mass (rs.map Prod.fst).toFinset p S*retainedWeight T w t j S rs

 theorem retainedWeight_absent (T : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (j : J) (S : Finset (Sym2 V)) (rs : List (Sym2 V × Finset J))
    (e : Sym2 V) (A : Finset J) (heS : e∉S) :
    retainedWeight T w t j S ((e,A)::rs)=retainedWeight T w t j S rs := by
  simp [retainedWeight,selectedList,heS]

 theorem retainedWeight_insert (T : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (j : J) (S : Finset (Sym2 V)) (rs : List (Sym2 V × Finset J))
    (e : Sym2 V) (A : Finset J) (heT : e∉T) (heR : e∉rs.map Prod.fst) :
    retainedWeight T w t j (insert e S) ((e,A)::rs)=retainedWeight T w t j S rs+
      (if j∈A ∧ ¬FTCovered (edgeGraph (greedyEdges T w t 0 (selectedList j S rs))) w t 0 e
        then w e else 0) := by
  have hfresh := selectedList_insert_fresh j S rs heR
  let E := greedyEdges T w t 0 (selectedList j S rs)
  have heE : e∉E := by
    intro he
    rcases mem_union.mp (greedy_subset T w t 0 _ he) with he | he
    · exact heT he
    · exact heR ((selectedList_sublist j S rs).subset (List.mem_toFinset.mp he))
  have hdiff : insert e E\T=insert e (E\T) := by
    ext d;by_cases hd : d=e <;> simp [hd,heT]
  unfold retainedWeight
  rw [selectedList]
  simp only [mem_insert_self,and_true,hfresh]
  by_cases hj : j∈A
  · simp only [hj,ite_true,greedyEdges,true_and]
    split_ifs with hc
    · simp only [add_zero]
    · change (∑ d∈insert e E\T,w d)=(∑ d∈E\T,w d)+w e
      rw [hdiff,sum_insert (fun hd => heE (mem_sdiff.mp hd).1)]
      ring
  · simp only [hj,ite_false,false_and,add_zero]

/-- Exact one-step expected weight, obtained by splitting the actual finite
Bernoulli sample into the absent and present fresh-edge cases. -/
theorem expectedRetainedWeight_cons (T : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t p : ℝ) (j : J) (rs : List (Sym2 V × Finset J))
    (e : Sym2 V) (A : Finset J) (heT : e∉T) (heR : e∉rs.map Prod.fst) :
    expectedRetainedWeight T w t p j ((e,A)::rs)=expectedRetainedWeight T w t p j rs+
      p*(∑ S∈(rs.map Prod.fst).toFinset.powerset,mass (rs.map Prod.fst).toFinset p S*
        (if j∈A ∧ ¬FTCovered (edgeGraph (greedyEdges T w t 0 (selectedList j S rs))) w t 0 e
          then w e else 0)) := by
  have heU : e∉(rs.map Prod.fst).toFinset := by simpa using heR
  unfold expectedRetainedWeight
  simp only [List.map_cons,List.toFinset_cons]
  rw [sum_powerset_insert heU,mul_sum,←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro S hS
  have hSU := mem_powerset.mp hS
  have heS : e∉S := fun hs => heU (hSU hs)
  rw [mass_insert_absent _ _ _ heU hSU,mass_insert_present _ _ _ heU hSU,
    retainedWeight_absent T w t j S rs e A heS,retainedWeight_insert T w t j S rs e A heT heR]
  ring
end LightEFTSpanners.SampledGreedy
