import LightSpanners.ChordWords

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Every bucket-safe walk uses fewer than n/2 cycle steps. No bound on its
number of chords is needed: the first chord alone bounds the bucket scale. -/
theorem BucketSafe.cycle_steps_lt_half {u v : V} {eps : ℝ} {k i : ℕ} {p : G.Walk u v}
    (h : C.BucketSafe eps k i p) (heps : 0 < eps) (hk : 0 < k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) :
    2*(C.cycleDarts p).length < Fintype.card V := by
  by_cases hchord : C.chordEdges p = []
  · have hn := h.nil_of_no_chords C hchord
    cases hn
    simpa using (lt_of_lt_of_le (by decide : 0 < 3) C.three_le_card)
  have hpos : (0 : ℝ) < 2^i := by positivity
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hkr1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbudget := h.cycle_budget C
  obtain ⟨s,hb,_⟩ := h
  obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ hchord
  have hed : e ∈ p.edges ∧ e ∉ C.cycle.edges := by simpa [chordEdges] using he
  have hi := (hb.2.1 e he).1
  have hwmax : w e < (Fintype.card V : ℝ)/(2*((1+4*eps)*(2*k)-1)) := by
    induction e using Sym2.inductionOn with
    | hf a b =>
      exact C.chord_weight_lt hG (by nlinarith [mul_pos heps hkr])
        ((mem_edgeSet G).mp (p.edges_subset_edgeSet hed.1)) hed.2
  have hden : 0 < 2*((1+4*eps)*(2*k)-1) := by nlinarith [mul_pos heps hkr]
  have hcoeff : 4*eps*k < 2*((1+4*eps)*(2*k)-1) := by
    nlinarith [mul_pos heps hkr]
  have hc := (lt_div_iff₀ hden).mp hwmax
  have ht := mul_le_mul_of_nonneg_right hi hden.le
  have hsmall := mul_lt_mul_of_pos_right hcoeff hpos
  have hfinal : 2*((C.cycleDarts p).length : ℝ) < Fintype.card V := by nlinarith
  exact_mod_cast hfinal

/-- Claim 2, for the actual oriented chord sequences used in its proof.
The result allows different start vertices and different bucket indices.
It imposes neither a simplicity hypothesis nor a chord-count bound. -/
theorem BucketSafe.unique_of_chordDarts {u u' v : V} {eps : ℝ} {k i j : ℕ}
    {p : G.Walk u v} {q : G.Walk u' v}
    (hp : C.BucketSafe eps k i p) (hq : C.BucketSafe eps k j q)
    (heps : 0 < eps) (hk : 0 < k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k)))
    (he : C.chordDarts p = C.chordDarts q) : HEq p q := by
  have hpc := hp.cycle_steps_lt_half C heps hk hG
  have hqc := hq.cycle_steps_lt_half C heps hk hG
  obtain ⟨s,hp,_⟩ := hp
  obtain ⟨t,hq,_⟩ := hq
  have hu := hp.same_start_of_chordDarts C hq he
  subst u'
  apply heq_of_eq
  exact C.walks_eq_of_chordDarts p q hp.1 hq.1 he (by omega)

/-- Same-start/same-end specialization of the heterogeneous Claim 2 result. -/
theorem BucketSafe.eq_of_chordDarts {u v : V} {eps : ℝ} {k i j : ℕ}
    {p q : G.Walk u v}
    (hp : C.BucketSafe eps k i p) (hq : C.BucketSafe eps k j q)
    (heps : 0 < eps) (hk : 0 < k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k)))
    (he : C.chordDarts p = C.chordDarts q) : p = q :=
  eq_of_heq (hp.unique_of_chordDarts C hq heps hk hG he)

end LightSpanners.UnitSpanningCycle
