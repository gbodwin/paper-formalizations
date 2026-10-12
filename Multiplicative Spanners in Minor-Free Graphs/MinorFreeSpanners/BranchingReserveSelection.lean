import MinorFreeSpanners.WeightedBranchingClusters

/-! Select a bounded set of real path vertices whose original credits fund
an intrinsic diameter reserve; a genuine branching neighbor remains outside. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem branching_reserve_selection {I : Type*} [Fintype I]
    (H : SimpleGraph I) (hH : H.IsAcyclic) (d credit : I → ℝ)
    (S : Finset I) (L D c b : ℝ) (s : ℕ)
    (hcore : BranchingCore H (fun i => d i+1) L (D+1) S)
    (hc : 0≤c) (hd1 : ∀ i∈S,1≤d i)
    (hcred : ∀ i∈S,c*d i≤credit i) (hbase : ∀ i∈S,c*b≤credit i)
    (hsize : L+D≤s*b) :
    ∃ R : Finset I,∃ z∈S,∃ radius : ℝ,
      0≤radius ∧ radius≤L+D ∧ R⊆S ∧ R.card≤s ∧ z∉R ∧
      (∀ i j,∀ p : H.Walk i j,p.IsPath →
        (∀ v∈p.support,v∈S) → pathMass d p+p.length≤radius) ∧
      c*radius≤(∑ i∈R,credit i)+c*(internalEdges H S).card := by
  classical
  obtain ⟨x,N,hNcard,hNadj,hNS⟩ := hcore.2.1
  have hne : S.Nonempty := ⟨x,hNS (by simp)⟩
  obtain ⟨i,hi,j,hj,p,hp,hps,hmax⟩ := exists_max_mass_path H hH S hne (fun i => d i+1)
  obtain ⟨z,hzN,hzp⟩ := three_neighbors_off_path H hH x N hNadj hNcard p hp
  have hzS : z∈S := hNS (Finset.mem_insert_of_mem hzN)
  let radius := pathMass d p+p.length
  have hradpos : 0≤radius := by
    have hm : 0≤pathMass d p := Finset.sum_nonneg (fun v hv => le_trans (by norm_num) (hd1 v (hps v (List.mem_toFinset.mp hv))))
    exact add_nonneg hm (Nat.cast_nonneg _)
  have hrad : radius≤L+D := by
    have hh := hcore.2.2.2 i j p hp hps
    rw [pathMass_add_one d p hp] at hh
    dsimp [radius]
    linarith
  have hbound : ∀ a b,∀ q : H.Walk a b,q.IsPath →
      (∀ v∈q.support,v∈S) → pathMass d q+q.length≤radius := by
    intro a b q hq hqs
    have hh := hmax a b q hq hqs
    rw [pathMass_add_one d q hq,pathMass_add_one d p hp] at hh
    dsimp [radius]
    linarith
  let P := p.support.toFinset
  have hPS : P⊆S := fun v hv => hps v (List.mem_toFinset.mp hv)
  have hzP : z∉P := by simpa [P] using hzp
  have hcn : 0≤c*(internalEdges H S).card := mul_nonneg hc (Nat.cast_nonneg _)
  by_cases hsmall : P.card≤s
  · refine ⟨P,z,hzS,radius,hradpos,hrad,hPS,hsmall,hzP,hbound,?_⟩
    have he := internalEdges_card_lower H S hcore.1 hne
    have hpcard := Finset.card_le_card hPS
    dsimp [P] at hpcard
    rw [List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support] at hpcard
    have hplen : p.length≤(internalEdges H S).card := by omega
    have hm := mul_le_mul_of_nonneg_left (show (p.length:ℝ)≤(internalEdges H S).card by exact_mod_cast hplen) hc
    have hn : c*pathMass d p≤∑ v∈P,credit v := by
      unfold pathMass
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun v hv => hcred v (hPS hv)
    dsimp [radius]
    nlinarith
  · obtain ⟨R,hRP,hRcard⟩ := Finset.exists_subset_card_eq (show s≤P.card by omega)
    refine ⟨R,z,hzS,radius,hradpos,hrad,hRP.trans hPS,by omega,fun hz => hzP (hRP hz),hbound,?_⟩
    have hsum : (R.card:ℝ)*(c*b)≤∑ i∈R,credit i := by
      calc
        _ = ∑ _i∈R,c*b := by simp
        _ ≤ _ := Finset.sum_le_sum fun i hi => hbase i (hPS (hRP hi))
    have hrb := mul_le_mul_of_nonneg_left (hrad.trans hsize) hc
    rw [hRcard] at hsum
    nlinarith

end MinorFreeSpanners
