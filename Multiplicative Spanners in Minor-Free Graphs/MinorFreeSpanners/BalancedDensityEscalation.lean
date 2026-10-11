import MinorFreeSpanners.SharpGeneralGraphIncrement

/-! Actual finite minor iteration retaining the product of branch widths.
The density loss per iteration is 1-16/k, independent of the chosen width. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def BalancedDensityWitness {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (d : ℝ) (t : ℕ) : Prop :=
  ∃ j : ℕ, j<t ∧ ∃ W n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
    0<W ∧ 0<n ∧ M.IsBounded W ∧
    (2:ℝ)^j*d ≤ (1-16/(k:ℝ))^j*W*d ∧
    ((1-16/(k:ℝ))^j*W*d)*n ≤ (Q.edgeFinset.card:ℝ) ∧
    ∃ S : Finset (Fin n),
      (S.card:ℝ) ≤ 12*(k:ℝ)^5*((1-16/(k:ℝ))^j*W*d) ∧
      0 < ((Q.induce (S:Set (Fin n))).edgeFinset.card:ℝ) ∧
      ((1-16/(k:ℝ))^j*W*d)/(800000*(k:ℝ)^7)*(S.card:ℝ) ≤
        ((Q.induce (S:Set (Fin n))).edgeFinset.card:ℝ)

def BalancedDensityStage {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (d : ℝ) (t : ℕ) : Prop :=
  ∃ W n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
    0<W ∧ 0<n ∧ M.IsBounded W ∧
    (2:ℝ)^t*d ≤ (1-16/(k:ℝ))^t*W*d ∧
    ((1-16/(k:ℝ))^t*W*d)*n ≤ (Q.edgeFinset.card:ℝ)

theorem balanced_density_escalation {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (d : ℝ) (hk : 32 ≤ k)
    (hn : 0 < Fintype.card V) (hd : (k:ℝ)^3 ≤ d)
    (hE : d*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ)) (t : ℕ) :
    BalancedDensityWitness G k d t ∨ BalancedDensityStage G k d t := by
  classical
  have hkR : (32:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ)<k := by linarith
  have hdpos : 0<d := lt_of_lt_of_le (by positivity : (0:ℝ)<(k:ℝ)^3) hd
  have ha : (1:ℝ)/2 ≤ 1-16/(k:ℝ) := by
    have hx : 16/(k:ℝ) ≤ 1/2 := (div_le_iff₀ hkpos).mpr (by linarith)
    linarith
  induction t with
  | zero =>
      obtain ⟨n,Q,M,hpos,hM,hden⟩ := exists_finite_bounded_dense_minor G G 1 d
        (MinorModel.identity G) (MinorModel.identity_bounded G) hn hE
      exact Or.inr ⟨1,n,Q,M,by omega,hpos,hM,by simp,by simpa using hden⟩
  | succ t ih =>
      rcases ih with hw | hs
      · obtain ⟨j,hj,W,n,Q,M,hW,hn,hM,hgrowth,hden,S,hsize,hpositive,hS⟩ := hw
        exact Or.inl ⟨j,by omega,W,n,Q,M,hW,hn,hM,hgrowth,hden,S,hsize,hpositive,hS⟩
      · obtain ⟨W,n,Q,M,hW,hn,hM,hgrowth,hden⟩ := hs
        let δ : ℝ := (1-16/(k:ℝ))^t*W*d
        have hδ : (k:ℝ)^3 ≤ δ := by
          have hp : (1:ℝ)≤2^t := one_le_pow₀ (by norm_num)
          dsimp [δ]
          nlinarith only [hd,hdpos,hp,hgrowth]
        have hδ0 : 0≤δ := (by positivity : (0:ℝ)≤(k:ℝ)^3).trans hδ
        obtain hw | hs := sharp_general_graph_density_increment Q k δ hk (by simpa using hn) hδ (by simpa [δ] using hden)
        · obtain ⟨S,hsize,hpositive,hS⟩ := hw
          exact Or.inl ⟨t,by omega,W,n,Q,M,hW,hn,hM,hgrowth,hden,S,hsize,hpositive,hS⟩
        · obtain ⟨m,r,R,N,hkm,hmk,hr,hN,hR⟩ := hs
          have hm : 8 ≤ m := by omega
          have hmR : (8:ℝ)≤m := by exact_mod_cast hm
          have hf : 2 ≤ (m:ℝ)*(1-16/(k:ℝ)) := by nlinarith [mul_nonneg (show (0:ℝ)≤m by positivity) (sub_nonneg.mpr ha)]
          have hg1 := mul_le_mul_of_nonneg_right hf hδ0
          have hg2 := mul_le_mul_of_nonneg_left hgrowth (show (0:ℝ)≤2 by norm_num)
          have hidentity : (1-16/(k:ℝ))^(t+1)*(m*W:ℕ)*d =
              ((m:ℝ)*(1-16/(k:ℝ)))*δ := by dsimp [δ]; push_cast; rw [pow_succ]; ring
          have hnext : (2:ℝ)^(t+1)*d ≤ (1-16/(k:ℝ))^(t+1)*(m*W:ℕ)*d := by
            rw [hidentity,pow_succ]
            dsimp [δ] at hg1
            nlinarith only [hg1,hg2]
          refine Or.inr ⟨m*W,r,R,N.comp M,Nat.mul_pos (by omega) hW,hr,hN.comp N M hM,hnext,?_⟩
          rw [hidentity]
          exact hR

end MinorFreeSpanners
