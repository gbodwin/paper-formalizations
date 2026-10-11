import MinorFreeSpanners.SelectedScaleDensityIncrement

/-! General-graph density increment with all bounds normalized to the
original input density. Every core, family, graph and minor is constructed
inside the theorem. The explicit constants follow the verified parameter
choice; no source-paper parameter identity is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- A genuine finite alternative at the original density scale. For k>=32
the minor branch at least doubles density, using branches of size at most k.
No packing, cleaning, coverage, bipartite or core certificate is supplied. -/
theorem general_graph_density_increment {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (d0 : ℝ) (hk : 32 ≤ k)
    (hn : 0 < Fintype.card V) (hd0 : (k:ℝ)^3 ≤ d0)
    (hE : d0*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ)) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 12*(k:ℝ)^5*d0 ∧
      0 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      d0/(800000*(k:ℝ)^7)*(S.card:ℝ) ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
      0<n ∧ M.IsBounded k ∧ ((k:ℝ)/16)*d0*n ≤ (Q.edgeFinset.card:ℝ)) := by
  classical
  obtain ⟨d,U,hdd,hU,hcore,hAlt⟩ := selected_scale_density_increment G k d0 (by omega) hn hd0 hE
  have hkR : (32:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hdpos : 0 < d0 := lt_of_lt_of_le (by positivity : (0:ℝ) < (k:ℝ)^3) hd0
  by_cases hlarge : ((k:ℝ)/16)*d0 ≤ d
  · let M : MinorModel (G.induce (U:Set V)) G :=
      MinorModel.ofEmbedding _ G ⟨Subtype.val,Subtype.val_injective⟩ (fun _ _ h => h)
    have hM : M.IsBounded k := by
      intro i
      have he : (M.branch i).toFinset = {i.val} := by
        ext x
        rw [Set.mem_toFinset,Finset.mem_singleton]
        rfl
      rw [he,Finset.card_singleton]
      omega
    have hpos : 0 < Fintype.card U := by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hU
    have hden : (((k:ℝ)/16)*d0)*(Fintype.card U:ℝ) ≤
        ((G.induce (U:Set V)).edgeFinset.card:ℝ) := by
      simpa only [Fintype.card_coe,hcore] using
        mul_le_mul_of_nonneg_right hlarge (Nat.cast_nonneg U.card)
    exact Or.inr (exists_finite_bounded_dense_minor _ G k (((k:ℝ)/16)*d0) M hM hpos hden)
  · rcases hAlt with hs | hm
    · obtain ⟨S,hsize,hpositive,hden⟩ := hs
      have hdscale : d ≤ (k:ℝ)*d0 := by
        have hposprod : 0 ≤ (k:ℝ)*d0 := by positivity
        have hh := lt_of_not_ge hlarge
        nlinarith only [hh,hposprod]
      have hsizeScale := mul_le_mul_of_nonneg_left hdscale (show 0 ≤ 12*(k:ℝ)^4 by positivity)
      have hsize' : (S.card:ℝ) ≤ 12*(k:ℝ)^5*d0 := by nlinarith only [hsize,hsizeScale]
      have hratio := div_le_div_of_nonneg_right hdd (show 0 ≤ 800000*(k:ℝ)^7 by positivity)
      exact Or.inl ⟨S,hsize',hpositive,(mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg S.card)).trans hden⟩
    · obtain ⟨n,Q,M,hpos,hM,hden⟩ := hm
      have hscale := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdd (show 0 ≤ (k:ℝ)/16 by positivity)) (Nat.cast_nonneg n)
      exact Or.inr ⟨n,Q,M,hpos,hM,hscale.trans hden⟩

end MinorFreeSpanners
