import MinorFreeSpanners.WeightedBranchingPhase

/-! Pool the actual disjoint branching-group budgets without counting an old
credit or a unit connector twice. Heavy edges between groups are paid once. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable

 theorem finite_union_weight_le {I E : Type*} (P : Finset I) (edges : I → Finset E)
    (w : E → ℝ) (hw : ∀ i∈P,∀ e∈edges i,0≤w e) :
    (∑ e∈P.biUnion edges,w e)≤∑ i∈P,∑ e∈edges i,w e := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert i P hi ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hi]
    have hih := ih (fun j hj => hw j (Finset.mem_insert_of_mem hj))
    have hnon : 0≤∑ e∈edges i∩P.biUnion edges,w e :=
      Finset.sum_nonneg fun e he => hw i (by simp) e (Finset.mem_inter.mp he).1
    have he : (∑ e∈edges i∪P.biUnion edges,w e)+(∑ e∈edges i∩P.biUnion edges,w e) =
        (∑ e∈edges i,w e)+(∑ e∈P.biUnion edges,w e) := Finset.sum_union_inter
    linarith

 theorem branching_phase_conservation {I J E : Type*} [Fintype J]
    (groups : J → Finset I) (heavy bridge : J → Finset E)
    (credit : I → ℝ) (w : E → ℝ) (reserve : J → ℝ) (c : ℝ)
    (hgroups : ∀ i j,i≠j → Disjoint (groups i) (groups j))
    (hbridge : ∀ i j,i≠j → Disjoint (bridge i) (bridge j))
    (hw : ∀ i e,e∈heavy i → 0≤w e)
    (hpay : ∀ i,reserve i+(∑ e∈heavy i,w e)≤
      (∑ v∈groups i,credit v)+c*(∑ e∈bridge i,w e)) :
    (∑ i,reserve i)+(∑ e∈Finset.univ.biUnion heavy,w e)≤
      (∑ v∈Finset.univ.biUnion groups,credit v)+
      c*(∑ e∈Finset.univ.biUnion bridge,w e) := by
  classical
  have hp := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hpay i)
  have hh := finite_union_weight_le Finset.univ heavy w (fun i _ => hw i)
  have hg := Finset.sum_biUnion (s:=Finset.univ) (f:=credit)
    (fun i _ j _ hij => hgroups i j hij)
  have hb := Finset.sum_biUnion (s:=Finset.univ) (f:=w)
    (fun i _ j _ hij => hbridge i j hij)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← hg,← hb] at hp
  linarith

end MinorFreeSpanners
