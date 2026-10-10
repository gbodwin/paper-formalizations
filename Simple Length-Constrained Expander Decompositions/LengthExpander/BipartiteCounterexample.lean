import LengthExpander.RealParameterArboricity
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! A finite family exposing the source's missing integer-domain qualifier:
K_{a,a} is literally 5/2-parallel-greedy but needs linearly many forests. -/
namespace LengthExpander.SourceCorrections
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

private theorem injective_labels_matching {V : Type*} {G : SimpleGraph V}
    {index : Sym2 V → ℕ} (hinj : Function.Injective index) : MatchingLabels G index := by
  intro u v z _ _ hi
  rcases Sym2.eq_iff.mp (hinj hi) with he | he
  · exact he.1
  · exact he.1.trans he.2

private theorem triangle_free_earlierFar_two {V : Type*} (G : SimpleGraph V)
    (ht : ∀ u v z, G.Adj u v → G.Adj v z → ¬ G.Adj u z) (index : Sym2 V → ℕ) :
    EarlierFar G index 2 := by
  intro u v huv p hp he
  cases p with
  | nil => exact G.irrefl huv
  | @cons u x v hux p =>
    cases p with
    | nil =>
      have hi := he s(u,v) (by simp)
      exact Nat.lt_irrefl _ hi
    | @cons x z v hxz q =>
      cases q with
      | nil => exact ht u x v hux hxz huv
      | cons h q => simp only [Walk.length_cons] at hp; omega

/-- Each edge can be its own matching batch; injective labels explicitly
supply that ordered partition. The real threshold is exactly 5/2. -/
theorem completeBipartite_real_parallelGreedy (a : ℕ) :
    ∃ index : Sym2 (Fin a ⊕ Fin a) → ℕ,
      Function.Injective index ∧ IsRealParallelGreedy (completeBipartiteGraph (Fin a) (Fin a)) index (5/2) := by
  classical
  let index (e : Sym2 (Fin a ⊕ Fin a)) := (Fintype.equivFin _ e).val
  have hinj : Function.Injective index := Fin.val_injective.comp (Fintype.equivFin _).injective
  refine ⟨index,hinj,?_⟩
  apply (real_parallelGreedy_iff_floor (by norm_num : (0:ℝ) ≤ 5/2)).mpr
  have hf : ⌊(5:ℝ)/2⌋₊ = 2 := (Nat.floor_eq_iff (by norm_num)).mpr (by norm_num)
  rw [hf]
  refine ⟨injective_labels_matching hinj,triangle_free_earlierFar_two _ ?_ index⟩
  intro u v z huv hvz
  cases u <;> cases v <;> cases z <;> simp_all

theorem completeBipartite_edge_count (a : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin a)).edgeFinset.card = a^2 := by
  classical
  have he := encard_edgeSet_completeBipartiteGraph (W₁ := Fin a) (W₂ := Fin a)
  simp only [Set.encard,ENat.card_eq_coe_fintype_card,Fintype.card_fin] at he
  have hc : Fintype.card (completeBipartiteGraph (Fin a) (Fin a)).edgeSet = a*a := by exact_mod_cast he
  simpa [edgeFinset,Set.toFinset_card,pow_two] using hc

private theorem acyclic_edges_le_pred_card {V : Type*} [Fintype V] [Nonempty V]
    (F : SimpleGraph V) (hF : F.IsAcyclic) : F.edgeFinset.card ≤ Fintype.card V-1 := by
  classical
  obtain ⟨T,hFT,_,hT⟩ := (connected_top : (⊤ : SimpleGraph V).Connected).exists_isTree_le_of_le_of_isAcyclic le_top hF
  have hm : F.edgeFinset.card ≤ T.edgeFinset.card := Finset.card_le_card (by simpa using hFT)
  have hc := hT.card_edgeFinset
  omega

/-- Every actual forest cover of K_{a,a} needs K(2a-1)>=a².
This lower bound and the real-threshold witness hold for every a>0. -/
theorem completeBipartite_forest_cover_lower_bound (a K : ℕ) (ha : 0 < a)
    (P : Fin K → SimpleGraph (Fin a ⊕ Fin a)) (hacyc : ∀ i, (P i).IsAcyclic)
    (hcover : ∀ u v, (completeBipartiteGraph (Fin a) (Fin a)).Adj u v →
      ∃ i, (P i).Adj u v) : a^2 ≤ K*(2*a-1) := by
  classical
  letI : NeZero a := ⟨Nat.ne_of_gt ha⟩
  have hsubset : (completeBipartiteGraph (Fin a) (Fin a)).edgeFinset ⊆
      univ.biUnion (fun i => (P i).edgeFinset) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨i,hi⟩ := hcover u v (by simpa using he)
      exact mem_biUnion.mpr ⟨i,mem_univ _,by simpa using hi⟩
  have hc := (Finset.card_le_card hsubset).trans (card_biUnion_le)
  have hs : (∑ i : Fin K, (P i).edgeFinset.card) ≤ ∑ _ : Fin K, (2*a-1) := by
    apply sum_le_sum
    intro i _
    simpa [Fintype.card_sum,two_mul] using acyclic_edges_le_pred_card (P i) (hacyc i)
  rw [completeBipartite_edge_count] at hc
  simpa using hc.trans hs

theorem completeBipartite_forest_cover_linear (a K : ℕ) (ha : 0 < a)
    (P : Fin K → SimpleGraph (Fin a ⊕ Fin a)) (hacyc : ∀ i, (P i).IsAcyclic)
    (hcover : ∀ u v, (completeBipartiteGraph (Fin a) (Fin a)).Adj u v →
      ∃ i, (P i).Adj u v) : a ≤ 2*K := by
  have h := completeBipartite_forest_cover_lower_bound a K ha P hacyc hcover
  have hm := Nat.mul_le_mul_left K (Nat.sub_le (2*a) 1)
  nlinarith

/-- No uniform constant times n^(4/5) bounds forest covers of this family.
At the fixed real threshold 5/2, the additional factor s is just a constant. -/
theorem no_uniform_four_fifths_forest_bound :
    ¬ ∃ c : ℝ, 0 ≤ c ∧ ∀ a : ℕ, 0 < a →
      ∃ (K : ℕ) (P : Fin K → SimpleGraph (Fin a ⊕ Fin a)),
        (∀ i, (P i).IsAcyclic) ∧
        (∀ u v, (completeBipartiteGraph (Fin a) (Fin a)).Adj u v → ∃ i, (P i).Adj u v) ∧
        (K:ℝ) ≤ c*(2*(a:ℝ))^((4:ℝ)/5) := by
  rintro ⟨c,hc,hbound⟩
  obtain ⟨b,hb⟩ := exists_nat_gt (max 1 (4*c))
  have hb1 : (1:ℝ) < b := (le_max_left _ _).trans_lt hb
  have hb4 : 4*c < (b:ℝ) := (le_max_right _ _).trans_lt hb
  have hbp : 0 < b := by exact_mod_cast (show (0:ℝ) < b by linarith)
  have hbpr : (0:ℝ) < b := by exact_mod_cast hbp
  let a := b^5
  have hap : 0 < a := pow_pos hbp _
  obtain ⟨K,P,hacyc,hcover,hK⟩ := hbound a hap
  have hlin : (a:ℝ) ≤ 2*(K:ℝ) := by
    exact_mod_cast completeBipartite_forest_cover_linear a K hap P hacyc hcover
  have htwo : (2:ℝ)^((4:ℝ)/5) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (4:ℝ)/5 ≤ 1)
  have hpow : (2*(a:ℝ))^((4:ℝ)/5) ≤ 2*(a:ℝ)^((4:ℝ)/5) := by
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg a)]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (Nat.cast_nonneg a) _)
  have haPow : (a:ℝ)^((4:ℝ)/5) = (b:ℝ)^4 := by
    dsimp [a]
    push_cast
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg b)]
    norm_num [Real.rpow_natCast]
  rw [haPow] at hpow
  have hweighted := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ 2*c)
  have haEq : (a:ℝ) = (b:ℝ)^5 := by simp [a]
  rw [haEq] at hlin
  have hstrict := mul_lt_mul_of_pos_right hb4 (pow_pos hbpr 4)
  nlinarith

end LengthExpander.SourceCorrections
