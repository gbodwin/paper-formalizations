import LinearDistancePreservers.LatticeMissedVolume

namespace LinearDistancePreservers.LatticeHull

/-- Sharp lattice-ball vertex growth, with a single dimension-dependent
integer radius factor, uniformly at every positive integer scale. -/
theorem uniform_vertices (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ b : ℕ, 0 < b →
      b^((n+3)*(n+2)) ≤ (vertices (ball (n+3) (C*b^(n+4)))).card := by
  obtain ⟨A,hA,R₀,hmiss⟩ := LatticeCaps.exists_missed_volume_bound n
  have hh := LatticeBody.uniform_vertices_of_missed_bound (n := n+2) (R₀ := R₀)
    (by omega) hA (by
      intro R hR
      convert hmiss R hR using 1 <;> norm_num [Nat.cast_add,Nat.cast_ofNat] <;> ring_nf <;> simp)
  simpa [add_assoc] using hh

end LinearDistancePreservers.LatticeHull
