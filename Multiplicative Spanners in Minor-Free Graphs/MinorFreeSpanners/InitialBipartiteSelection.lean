import MinorFreeSpanners.SelectedBipartiteMinor

/-! Construct the initial full mate-free family from a genuinely regular
bipartite host, using the actual small-dense/unmated alternative. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- No initial star family or unmated premise is supplied. The actual
left-regular graph either already contains a small dense witness or selects
and regularizes a literal full family before the bounded minor construction. -/
theorem regular_bipartite_density_increment {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (ell d : ℕ) (k : ℝ)
    (hk : 0 < k) (hell : 1 ≤ ell) (hellk : 4*(ell:ℝ) ≤ k) (hkd : k ≤ d)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hA : A.Nonempty)
    (hsize : ell*B.card ≤ A.card) (hreg : ∀ x ∈ A, G.degree x=d) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 10*k^3*d ∧
      0 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      (d:ℝ)/(400000*k^5)*S.card ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
      0 < n ∧ M.IsBounded (ell+1) ∧
      ((ell:ℝ)-1)*d*n ≤ (Q.edgeFinset.card:ℝ)) := by
  classical
  have hd0 : 0 < d := by exact_mod_cast hk.trans_le hkd
  have hdR : (0:ℝ) < d := by exact_mod_cast hd0
  have hellR : (1:ℝ) ≤ ell := by exact_mod_cast hell
  have hk4 : 4 ≤ k := by linarith
  have he1 : (1:ℝ)/(100*k) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  obtain hs | hu := postle_small_dense_or_unmated G (5*k^2) d
    (1/(100*k)) (1/(100*k^2)) (by nlinarith) (by linarith) (by positivity)
    he1.le (by positivity)
  · obtain ⟨S,hN,hE⟩ := hs
    have hE' : (d:ℝ)^2/(20000*k^3) ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ) := by
      convert hE using 1
      ring
    exact Or.inl ⟨S,bipartite_mate_witness_scale k d S.card
      (G.induce (S:Set V)).edgeFinset.card hk4 hdR (by nlinarith) hE'⟩
  · have hsmall : ∀ x ∈ A, (G.degree x:ℝ) ≤ 5*k^2*d := by
      intro x hx
      rw [hreg x hx]
      have hcoef : (1:ℝ) ≤ 5*k^2 := by nlinarith
      nlinarith
    have hB : ∀ x ∈ A, d ≤ (B.filter fun b => G.Adj x b).card := by
      intro x hx
      have he : B.filter (fun b => G.Adj x b)=G.neighborFinset x := by
        ext b
        simp only [Finset.mem_filter,mem_neighborFinset]
        exact ⟨fun h => h.2,fun h => ⟨hG.mem_of_mem_adj hx h,h⟩⟩
      rw [he,card_neighborFinset_eq_degree,hreg x hx]
    obtain ⟨C,L,hCB,hL,hfull,hfree,hboundary,hne⟩ :=
      unmated_small_left_star_selection G A B ell d (5*k^2) (1/(100*k))
        (1/(100*k^2)) hG hd0 (by positivity) he1 (by positivity) hsize hsmall hu hB
    apply selected_bipartite_dense_or_density_minor G A B C ell d k hk hell hellk
      hkd L hG hCB (hne hA) hL hfull
    · intro b hb
      convert hfree b hb using 1
      ring
    · intro x hx
      exact (hreg x hx).ge
    · intro x hx
      exact Nat.le_floor (hboundary x hx)

end MinorFreeSpanners
