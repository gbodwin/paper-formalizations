import LightEFTSpanners.MultigraphCutTransport

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V E I : Type*} [Fintype E] [Fintype I]
attribute [local instance] Classical.propDecidable

/-- Actual edge identities joining different non-outside blocks of a vertex
partition. Parallel edges are distinct members; loops never qualify. -/
noncomputable def partitionCrossings (G : Graph V E) (part : V → Option I) : Finset E :=
  univ.filter (fun e => ∃ u v i j,G.IsLink e u v ∧ part u=some i ∧ part v=some j ∧ i≠j)

omit [Fintype E] [Fintype I] in
theorem crossing_link_iff (G : Graph V E) (part : V → Option I)
    {e : E} {u v : V} (h : G.IsLink e u v) :
    (∃ x y i j,G.IsLink e x y ∧ part x=some i ∧ part y=some j ∧ i≠j) ↔
      ∃ i j,part u=some i ∧ part v=some j ∧ i≠j := by
  constructor
  · rintro ⟨x,y,i,j,hxy,hx,hy,hij⟩
    rcases h.eq_and_eq_or_eq_and_eq hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨i,j,hx,hy,hij⟩
    · exact ⟨j,i,hy,hx,Ne.symm hij⟩
  · rintro ⟨i,j,hu,hv,hij⟩
    exact ⟨u,v,i,j,h,hu,hv,hij⟩

/-- Summing all non-outside block cuts counts each internal crossing edge
exactly twice and each outside boundary edge exactly once. This is the actual
multigraph counting identity behind the partition budget in CS09 Lemma 2.5. -/
theorem partition_cut_sum (G : Graph V E) (part : V → Option I) :
    (∑ i : I,(G.edgeCut {v | part v=some i}).toFinset.card)=
      2*(partitionCrossings G part).card+(G.edgeCut {v | part v=none}).toFinset.card := by
  classical
  have hc (S : Set E) : S.toFinset.card=∑ e : E,if e∈S then 1 else 0 := by simp
  have hp : (partitionCrossings G part).card=
      ∑ e : E,if ∃ u v i j,G.IsLink e u v ∧ part u=some i ∧ part v=some j ∧ i≠j then 1 else 0 := by
    simp [partitionCrossings]
  simp only [hc,hp,Finset.mul_sum,← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e∈G.edgeSet
  · obtain ⟨u,v,h⟩ := Graph.exists_isLink_of_mem_edgeSet he
    simp only [h.mem_edgeCut_iff,Set.mem_ofPred_eq,crossing_link_iff G part h]
    cases hu : part u with
    | none =>
      cases hv : part v with
      | none => simp
      | some j => simp
    | some i =>
      cases hv : part v with
      | none => simp
      | some j =>
        by_cases hij : i=j
        · subst j; simp
        · have hji := Ne.symm hij
          simp only [Option.some.injEq,Option.some_ne_none,not_false_eq_true,
            and_true,or_false,ite_false]
          have hdis (l : I) :
              (if (i=l ∧ j≠l) ∨ (j=l ∧ i≠l) then 1 else 0)=
                (if l=i then 1 else 0)+(if l=j then 1 else 0) := by
            by_cases hl : l=i <;> by_cases hjl : l=j <;> simp_all [eq_comm]
          simp_rw [hdis]
          simp [Finset.sum_add_distrib,hij]
  · have hnot (u v : V) : ¬G.IsLink e u v := fun h => he h.edge_mem
    simp [Graph.edgeCut,hnot]

/-- The exact cut identity converts genuine block-cut lower bounds and a
bounded outside cut into the required Nash-Williams partition inequality.
This counts actual crossing edges; existence of disjoint trees is separate. -/
theorem partition_crossing_budget (G : Graph V E) (part : V → Option I) {k : ℕ}
    (hcuts : ∀ i : I,2*k≤(G.edgeCut {v | part v=some i}).toFinset.card)
    (hout : (G.edgeCut {v | part v=none}).toFinset.card≤2*k) :
    k*(Fintype.card I-1)≤(partitionCrossings G part).card := by
  classical
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun i (_ : i∈(Finset.univ:Finset I)) => hcuts i)
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  rw [partition_cut_sum] at hs
  by_cases hn : Fintype.card I=0
  · simp [hn]
  · have hcard : Fintype.card I-1+1=Fintype.card I := by omega
    nlinarith
end LightEFTSpanners.MultigraphCuts
