import MinorFreeSpanners.DensestInducedCore
import MinorFreeSpanners.GeneralDensityTrichotomy

/-! Join the internally selected densest induced core to the genuine general
trichotomy. The input only supplies an original positive density floor and
parameters. Its minimum degree and universal subset-density bound are proved. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Universal original induced-density bounds descend to an actual induced
host using the literal injective vertex map and original image subset. -/
theorem induced_density_upper (G : SimpleGraph V) (U : Finset V) (d : ℝ)
    (h : ∀ W : Finset V, ((G.induce (W:Set V)).edgeFinset.card:ℝ) ≤ d*(W.card:ℝ)) :
    ∀ W : Finset U, (((G.induce (U:Set V)).induce (W:Set U)).edgeFinset.card:ℝ) ≤ d*(W.card:ℝ) := by
  classical
  intro W
  let f : (G.induce (U:Set V)) →g G := (SimpleGraph.Embedding.induce (U:Set V)).toHom
  obtain ⟨hc,he⟩ := induced_witness_map f Subtype.val_injective W
  have heR : (((G.induce (U:Set V)).induce (W:Set U)).edgeFinset.card:ℝ) ≤
      (G.induce ((W.image f:Finset V):Set V)).edgeFinset.card := by exact_mod_cast he
  have hb := h (W.image f)
  rw [hc] at hb
  exact heR.trans hb

/-- The original graph needs no minimum-degree, maximality, family or
universal-density certificate. The selected scale d may exceed d0; the
bipartite branch lies in the displayed actual original induced core. -/
theorem exists_densest_core_trichotomy (G : SimpleGraph V) (k ell : ℕ)
    (K eps1 eps2 d0 : ℝ) (hk : 8 ≤ k) (hell : 4*ell ≤ k)
    (hn : 0 < Fintype.card V) (hK : 4*(k:ℝ)^2 ≤ K) (hd0 : 1 ≤ d0)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d0) (hkd : (k:ℝ) ≤ eps1*d0)
    (hcoef : (3*eps1+4*eps2)*(k:ℝ) ≤ 5)
    (hE : d0*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ)) :
    ∃ d : ℝ, d0 ≤ d ∧ ∃ U : Finset V, U.Nonempty ∧
      ((G.induce (U:Set V)).edgeFinset.card:ℝ)=d*(U.card:ℝ) ∧
      ((∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
        eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
      (∃ X Y : Finset U, ∃ H : SimpleGraph U, H ≤ G.induce (U:Set V) ∧
        H.IsBipartiteWith (X:Set U) (Y:Set U) ∧ X.Nonempty ∧ ell*Y.card ≤ X.card ∧
        ∀ x∈X, d-(2+3*(k:ℝ))*eps1*d ≤ (H.degree x:ℝ)) ∨
      (∃ n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
        0<n ∧ M.IsBounded k ∧ ((k:ℝ)-7)*d*n ≤ (Q.edgeFinset.card:ℝ))) := by
  classical
  obtain ⟨d,hdd,U,hU,he,hmin,hglobal⟩ := exists_densest_induced_core G d0 (by linarith) hn hE
  have hnU : 0 < Fintype.card U := by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hU
  have heU : ((G.induce (U:Set V)).edgeFinset.card:ℝ)=d*(Fintype.card U:ℝ) := by
    simpa only [Fintype.card_coe] using he
  have hqd : 1 ≤ eps2*d := hq.trans (mul_le_mul_of_nonneg_left hdd he2)
  have hkdd : (k:ℝ) ≤ eps1*d := hkd.trans (mul_le_mul_of_nonneg_left hdd he1)
  obtain hs | hb | hm := general_density_trichotomy (G.induce (U:Set V)) k ell K eps1 eps2 d
    hk hell hnU hK (hd0.trans hdd) he1 he1' he2 hqd hkdd hcoef (fun x => (hmin x).le)
    heU (induced_density_upper G U d hglobal)
  · obtain ⟨S,hs,heS⟩ := hs
    let f : (G.induce (U:Set V)) →g G := (SimpleGraph.Embedding.induce (U:Set V)).toHom
    obtain ⟨hc,hcount⟩ := induced_witness_map f Subtype.val_injective S
    have hcR : (((G.induce (U:Set V)).induce (S:Set U)).edgeFinset.card:ℝ) ≤
        (G.induce ((S.image f:Finset V):Set V)).edgeFinset.card := by exact_mod_cast hcount
    exact ⟨d,hdd,U,hU,he,Or.inl ⟨S.image f,by simpa only [hc] using hs,heS.trans hcR⟩⟩
  · exact ⟨d,hdd,U,hU,he,Or.inr (Or.inl hb)⟩
  · obtain ⟨n,Q,M,hpos,hM,hD⟩ := hm
    let f : (G.induce (U:Set V)) →g G := (SimpleGraph.Embedding.induce (U:Set V)).toHom
    exact ⟨d,hdd,U,hU,he,Or.inr (Or.inr ⟨n,Q,M.mapHost f Subtype.val_injective,hpos,
      MinorModel.IsBounded.mapHost M f Subtype.val_injective hM,hD⟩)⟩

end MinorFreeSpanners
