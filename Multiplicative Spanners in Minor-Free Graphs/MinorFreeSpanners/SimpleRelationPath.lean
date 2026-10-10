import Mathlib.Data.List.Chain
import Mathlib.Data.List.Basic

/-! Actual loop erasure for arbitrary directed finite relation chains.
No symmetry or transitivity of the one-step relation is assumed. -/
namespace MinorFreeSpanners

/-- Reflexive-transitive reachability admits a vertex-simple directed chain
with the same endpoints. Repeated vertices are removed by taking a suffix. -/
theorem exists_simple_relation_path {V : Type*} {R : V → V → Prop} {u v : V}
    (h : Relation.ReflTransGen R u v) :
    ∃ l : List V, (u::l).IsChain R ∧ (u::l).Nodup ∧
      (u::l).getLast (List.cons_ne_nil _ _) = v := by
  classical
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨[],.singleton _,by simp,rfl⟩
  · intro a b hab _ ih
    obtain ⟨l,hchain,hnodup,hlast⟩ := ih
    by_cases ha : a ∈ b::l
    · obtain ⟨s,t,heq⟩ := List.append_of_mem ha
      have hc : (a::t).IsChain R := by
        rw [heq] at hchain
        exact (List.isChain_split.mp hchain).2
      have hn : (a::t).Nodup := by
        rw [heq] at hnodup
        exact (List.nodup_append.mp hnodup).2.1
      refine ⟨t,hc,hn,?_⟩
      have hl' : (s ++ a::t).getLast (by simp) = v := by
        simpa only [← heq] using hlast
      simpa only [List.getLast_append_of_right_ne_nil _ _ (List.cons_ne_nil _ _)] using hl'
    · exact ⟨b::l,.cons_cons hab hchain,List.nodup_cons.mpr ⟨ha,hnodup⟩,
        by simpa only [List.getLast_cons_cons] using hlast⟩

end MinorFreeSpanners
