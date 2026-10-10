import LightEFTSpanners.HubPreserver
import LightEFTSpanners.BipartiteForcing
import LightEFTSpanners.ConnectivityOptimum
import Mathlib.Tactic

namespace LightEFTSpanners.CounterfamilyWeight
open SimpleGraph Finset LightSpanners HubPreserver
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
attribute [local instance] Classical.propDecidable

theorem complete_edges :
    (completeBipartiteGraph L R).edgeFinset =
      (univ : Finset (L×R)).image (fun p => s(Sum.inl p.1,Sum.inr p.2)) := by
  ext e
  simp only [mem_edgeFinset,edgeSet_completeBipartiteGraph,Set.mem_range,
    mem_image,mem_univ,true_and]

theorem unit_weight (G : SimpleGraph (L⊕R)) :
    totalWeight G (fun _ => 1) = G.edgeFinset.card := by simp [totalWeight]

theorem complete_weight :
    totalWeight (completeBipartiteGraph L R) (fun _ => 1) =
      (Fintype.card L : ℝ)*Fintype.card R := by
  rw [unit_weight,complete_edges,card_image_of_injective _ cross_injective]
  simp

theorem hub_edges_subset (A : Finset L) (B : Finset R) :
    (graph A B).edgeFinset ⊆
      ((A ×ˢ (univ : Finset R)) ∪ ((univ : Finset L) ×ˢ B)).image
        (fun p => s(Sum.inl p.1,Sum.inr p.2)) := by
  intro e he
  have heG : e ∈ (completeBipartiteGraph L R).edgeSet :=
    (SimpleGraph.edgeSet_mono (graph_le A B)) (mem_edgeFinset.mp he)
  rw [edgeSet_completeBipartiteGraph] at heG
  obtain ⟨⟨a,b⟩,rfl⟩ := heG
  have hh : a∈A ∨ b∈B := by simpa using (mem_edgeFinset.mp he)
  exact mem_image.mpr ⟨(a,b),by simpa using hh,rfl⟩

/-- The actual hub certificate has linear weight, with no denominator oracle. -/
theorem hub_weight_le (A : Finset L) (B : Finset R) :
    totalWeight (graph A B) (fun _ => 1) ≤
      (A.card : ℝ)*Fintype.card R + (Fintype.card L : ℝ)*B.card := by
  have h := card_le_card (hub_edges_subset A B)
  have hu := card_union_le (A ×ˢ (univ : Finset R)) ((univ : Finset L) ×ˢ B)
  rw [card_image_of_injective _ cross_injective] at h
  simp only [card_product,card_univ] at hu
  rw [unit_weight]
  exact_mod_cast h.trans hu

theorem preserver_weight_pos [Nonempty L] [Nonempty R]
    {Q : SimpleGraph (L⊕R)} {f : ℕ}
    (hQ : IsFTConnectivityPreserver (completeBipartiteGraph L R) Q f) :
    0 < totalWeight Q (fun _ => 1) := by
  rw [unit_weight]
  apply Nat.cast_pos.mpr
  apply card_pos.mpr
  rw [edgeFinset_nonempty]
  intro heq
  let a : L := Classical.choice inferInstance
  let b : R := Classical.choice inferInstance
  have hab : (completeBipartiteGraph L R).Reachable (Sum.inl a) (Sum.inr b) :=
    (show (completeBipartiteGraph L R).Adj (Sum.inl a) (Sum.inr b) by simp).reachable
  have hr := (hQ.2 ∅ (by simp) (Sum.inl a) (Sum.inr b)).mp
    (by simpa [afterFaults] using hab)
  simp [afterFaults,heq,reachable_bot] at hr

/-- Every actual stretch-below-three EFT spanner has linearly growing
competitive lightness against the optimal (r-1)-fault denominator. -/
theorem competitive_lower {m r f : ℕ} {t : ℝ}
    (hm : 0 < m) (hr : 0 < r) (hrm : r ≤ m) (ht : t < 3)
    {H Q : SimpleGraph (Fin m ⊕ Fin m)}
    (hH : IsEFTSpanner (completeBipartiteGraph (Fin m) (Fin m)) H (fun _ => 1) t f)
    (hQ : IsMinimumFTPreserver (completeBipartiteGraph (Fin m) (Fin m))
      Q (fun _ => 1) (r-1)) :
    (m : ℝ)/(2*r) ≤ competitiveLightness H Q (fun _ => 1) := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  obtain ⟨A,_,hA⟩ := exists_subset_card_eq (s := (univ : Finset (Fin m))) (by simpa using hrm)
  have hcert : IsFTConnectivityPreserver (completeBipartiteGraph (Fin m) (Fin m))
      (graph A A) (r-1) := isFTPreserver A A (r-1) (by omega) (by omega)
  have hden := (hQ.2 (graph A A) hcert).trans (hub_weight_le A A)
  simp only [hA,Fintype.card_fin] at hden
  have hp := preserver_weight_pos hQ.1
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  unfold competitiveLightness
  rw [BipartiteForcing.eft_eq ht hH,complete_weight]
  simp only [Fintype.card_fin]
  apply (le_div_iff₀ hp).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*r)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden hmR.le]
/-- Explicit source parameters f=k=1, epsilon=3/2, against the true optimal
two-fault denominator. Its existence is proved, not assumed. -/
theorem two_fault_counterfamily (m : ℕ) (hm : 3 ≤ m) :
    ∃ Q : SimpleGraph (Fin m ⊕ Fin m),
      IsMinimumFTPreserver (completeBipartiteGraph (Fin m) (Fin m)) Q (fun _ => 1) 2 ∧
      ∀ H : SimpleGraph (Fin m ⊕ Fin m),
        IsEFTSpanner (completeBipartiteGraph (Fin m) (Fin m)) H
          (fun _ => 1) (5/2) 1 →
        (m : ℝ)/6 ≤ competitiveLightness H Q (fun _ => 1) := by
  obtain ⟨Q,hQ⟩ := exists_minimum_preserver
    (completeBipartiteGraph (Fin m) (Fin m)) (fun _ => 1) 2
  refine ⟨Q,hQ,fun H hH => ?_⟩
  have hb := competitive_lower (r := 3) (by omega) (by decide) hm
    (by norm_num : (5/2:ℝ)<3) hH hQ
  norm_num at hb
  exact hb

/-- Eta=1 changes the denominator to three-fault connectivity, and still
leaves a linear lower bound for every eligible actual output graph. -/
theorem three_fault_counterfamily (m : ℕ) (hm : 4 ≤ m) :
    ∃ Q : SimpleGraph (Fin m ⊕ Fin m),
      IsMinimumFTPreserver (completeBipartiteGraph (Fin m) (Fin m)) Q (fun _ => 1) 3 ∧
      ∀ H : SimpleGraph (Fin m ⊕ Fin m),
        IsEFTSpanner (completeBipartiteGraph (Fin m) (Fin m)) H
          (fun _ => 1) (5/2) 1 →
        (m : ℝ)/8 ≤ competitiveLightness H Q (fun _ => 1) := by
  obtain ⟨Q,hQ⟩ := exists_minimum_preserver
    (completeBipartiteGraph (Fin m) (Fin m)) (fun _ => 1) 3
  refine ⟨Q,hQ,fun H hH => ?_⟩
  have hb := competitive_lower (r := 4) (by omega) (by decide) hm
    (by norm_num : (5/2:ℝ)<3) hH hQ
  norm_num at hb
  exact hb
end LightEFTSpanners.CounterfamilyWeight
