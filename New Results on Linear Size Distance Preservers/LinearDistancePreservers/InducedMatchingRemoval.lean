import LinearDistancePreservers.MatchingExtremal

/-! A checked translation from induced matchings to mathlib's triangle-removal
theorem. The quantitative conclusion implies `matchingNumber (Fin n) = o(n²)`.
No Ruzsa–Szemerédi estimate is postulated. -/
namespace LinearDistancePreservers
open Finset SimpleGraph TripartiteFromTriangles
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def matchingTriangles (E : Finset (V × V)) (label : V × V → V) :
    Finset (V × V × V) := E.image fun e => (e.1,e.2,label e)

@[simp] theorem mem_matchingTriangles {E : Finset (V × V)} {label : V × V → V}
    {a b c : V} : (a,b,c) ∈ matchingTriangles E label ↔ (a,b) ∈ E ∧ label (a,b) = c := by
  classical
  simp [matchingTriangles, mem_image, Prod.ext_iff, and_assoc]

theorem matchingTriangles_card (E : Finset (V × V)) (label : V × V → V) :
    (matchingTriangles E label).card = E.card := by
  classical
  apply card_image_of_injective
  intro e f h
  exact Prod.ext (congrArg (fun t : V × V × V => t.1) h) (congrArg (fun t : V × V × V => t.2.1) h)

theorem matchingTriangles_explicit {E : Finset (V × V)} {label : V × V → V}
    (h : InducedPartition E label) : ExplicitDisjoint (matchingTriangles E label) where
  inj₀ := by
    intro a b c a' h₁ h₂
    obtain ⟨he, hl⟩ := mem_matchingTriangles.mp h₁
    obtain ⟨hf, hl'⟩ := mem_matchingTriangles.mp h₂
    by_contra ha
    have hn : (a,b) ≠ (a',b) := fun hh => ha (congrArg Prod.fst hh)
    exact (h.induced _ he _ hf (hl.trans hl'.symm) hn b (Or.inr rfl) b (Or.inr rfl)).1 rfl
  inj₁ := by
    intro a b c b' h₁ h₂
    obtain ⟨he, hl⟩ := mem_matchingTriangles.mp h₁
    obtain ⟨hf, hl'⟩ := mem_matchingTriangles.mp h₂
    by_contra hb
    have hn : (a,b) ≠ (a,b') := fun hh => hb (congrArg Prod.snd hh)
    exact (h.induced _ he _ hf (hl.trans hl'.symm) hn a (Or.inl rfl) a (Or.inl rfl)).1 rfl
  inj₂ := by
    intro a b c c' h₁ h₂
    exact (mem_matchingTriangles.mp h₁).2.symm.trans (mem_matchingTriangles.mp h₂).2

theorem matchingTriangles_noAccidental {E : Finset (V × V)} {label : V × V → V}
    (h : InducedPartition E label) : NoAccidental (matchingTriangles E label) where
  eq_or_eq_or_eq := by
    intro a a' b b' c c' h₁ h₂ h₃
    obtain ⟨he, hl⟩ := mem_matchingTriangles.mp h₁
    obtain ⟨hf, hl'⟩ := mem_matchingTriangles.mp h₂
    by_cases hn : (a',b) = (a,b')
    · exact Or.inl (congrArg Prod.fst hn).symm
    · have hs := h.induced _ he _ hf (hl.trans hl'.symm) hn b (Or.inr rfl) a (Or.inl rfl)
      exact False.elim (hs.2 (Or.inr (mem_matchingTriangles.mp h₃).1))

/-- A quantitative induced-matching lemma imported through an explicit
three-part graph: `3n` vertices and exactly one triangle per original edge. -/
theorem InducedPartition.card_lt_of_triangleRemoval {E : Finset (V × V)}
    {label : V × V → V} (h : InducedPartition E label) {ε : ℝ}
    (hε : 0 < ε)
    (hn : 1 < triangleRemovalBound (ε / 9) * (3 * Fintype.card V : ℝ)) :
    (E.card : ℝ) < ε * (Fintype.card V : ℝ)^2 := by
  classical
  let t := matchingTriangles E label
  letI : ExplicitDisjoint t := matchingTriangles_explicit h
  letI : NoAccidental t := matchingTriangles_noAccidental h
  have hcard : (t.card : ℝ) = E.card := by exact_mod_cast matchingTriangles_card E label
  have hN : (Fintype.card (V ⊕ V ⊕ V) : ℝ) = 3 * Fintype.card V := by
    simp only [Fintype.card_sum, Nat.cast_add]
    ring
  have hcap : (E.card : ℝ) ≤ (Fintype.card V : ℝ)^2 := by
    exact_mod_cast (show E.card ≤ Fintype.card V ^ 2 by
      simpa [Fintype.card_prod, pow_two] using card_le_univ E)
  by_contra hnot
  have hdense : (ε / 9) *
      ((Fintype.card V + Fintype.card V + Fintype.card V)^2 : ℕ) ≤ (t.card : ℝ) := by
    push_cast
    rw [hcard]
    nlinarith [le_of_not_gt hnot]
  have hmany := (farFromTriangleFree t hdense).le_card_cliqueFinset
  rw [card_triangles, hN, hcard] at hmany
  have hpos : (0 : ℝ) < Fintype.card V := by
    by_contra hnon
    have hz : (Fintype.card V : ℝ) = 0 := le_antisymm (le_of_not_gt hnon) (Nat.cast_nonneg _)
    norm_num [hz] at hn
  have hsq : 0 < (3 * (Fintype.card V : ℝ))^2 := sq_pos_of_pos (by positivity)
  have hmul := mul_lt_mul_of_pos_right hn hsq
  nlinarith

/-- Explicit subquadratic estimate for the paper's extremal function. -/
theorem matchingNumber_lt_of_triangleRemoval {ε : ℝ} (hε : 0 < ε)
    (hn : 1 < triangleRemovalBound (ε / 9) * (3 * Fintype.card V : ℝ)) :
    (matchingNumber V : ℝ) < ε * (Fintype.card V : ℝ)^2 := by
  classical
  obtain ⟨E, _, hE⟩ := exists_mem_eq_sup (univ : Finset (Finset (V × V))) univ_nonempty
    (fun E => if ∃ label : V × V → V, InducedPartition E label then E.card else 0)
  change matchingNumber V = _ at hE
  rw [hE]
  split_ifs with h
  · obtain ⟨label, hl⟩ := h
    exact hl.card_lt_of_triangleRemoval hε hn
  · have hne : (Fintype.card V : ℝ) ≠ 0 := by intro hz; norm_num [hz] at hn
    simpa using mul_pos hε (sq_pos_of_ne_zero hne)

/-- The usual epsilon/threshold formulation of the induced-matching lemma. -/
theorem matchingNumber_subquadratic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (matchingNumber (Fin n) : ℝ) < ε * (n : ℝ)^2 := by
  have hδ : 0 < triangleRemovalBound (ε / 9) := triangleRemovalBound_pos (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (3 * triangleRemovalBound (ε / 9)))
  refine ⟨N, fun n hn => ?_⟩
  have hN' : 1 < (N : ℝ) * (3 * triangleRemovalBound (ε / 9)) :=
    (div_lt_iff₀ (by positivity)).mp hN
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : 1 < triangleRemovalBound (ε / 9) * (3 * (n : ℝ)) := by nlinarith
  simpa only [Fintype.card_fin] using
    (matchingNumber_lt_of_triangleRemoval (V := Fin n) hε (by simpa using hlarge))

end LinearDistancePreservers
