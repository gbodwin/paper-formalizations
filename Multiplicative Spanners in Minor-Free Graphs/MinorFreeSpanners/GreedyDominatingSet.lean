import MinorFreeSpanners.GreedyNeighborhoodCover

/-! The actual iterative covering construction, with a logarithmic size bound. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

noncomputable def uncovered (G : SimpleGraph V) (B : Finset V) : Finset V :=
  Finset.univ.filter fun x => ∀ v ∈ B, ¬ G.Adj v x

@[simp] theorem uncovered_empty (G : SimpleGraph V) : uncovered G ∅ = Finset.univ := by
  classical
  ext x
  simp [uncovered]

theorem uncovered_insert (G : SimpleGraph V) (B : Finset V) (v : V) :
    uncovered G (insert v B) = uncovered G B \ G.neighborFinset v := by
  classical
  ext x
  simp only [uncovered,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
    Finset.mem_sdiff,mem_neighborFinset]
  constructor
  · intro h
    exact ⟨fun w hw => h w (Or.inr hw),h v (Or.inl rfl)⟩
  · rintro ⟨h,hv⟩ w (rfl | hw)
    · exact hv
    · exact h w hw

/-- Every number of iterations has an actual finite selected vertex set. -/
theorem exists_iterated_cover [Nonempty V] (G : SimpleGraph V) (δ : ℕ)
    (hδ : 0 < δ) (hsize : Fintype.card V ≤ 4*δ)
    (hdeg : ∀ x, δ ≤ G.degree x) (r : ℕ) :
    ∃ B : Finset V, B.card ≤ r ∧
      4^r * (uncovered G B).card ≤ 3^r * Fintype.card V := by
  classical
  induction r with
  | zero => exact ⟨∅,by simp,by simp⟩
  | succ r ih =>
    obtain ⟨B,hB,hU⟩ := ih
    obtain ⟨v,hv⟩ := exists_cover_step G δ hδ hsize hdeg (uncovered G B)
    refine ⟨insert v B,(Finset.card_insert_le v B).trans (Nat.succ_le_succ hB),?_⟩
    rw [uncovered_insert]
    calc
      _ = 4^r * (4 * (uncovered G B \ G.neighborFinset v).card) := by ring
      _ ≤ 4^r * (3 * (uncovered G B).card) := Nat.mul_le_mul_left _ hv
      _ = 3 * (4^r * (uncovered G B).card) := by ring
      _ ≤ 3 * (3^r * Fintype.card V) := Nat.mul_le_mul_left _ hU
      _ = _ := by ring

/-- A genuine open-neighborhood dominating set, constructed without an oracle. -/
theorem exists_small_dominating_set [Nonempty V] (G : SimpleGraph V) (δ : ℕ)
    (hδ : 0 < δ) (hsize : Fintype.card V ≤ 4*δ)
    (hdeg : ∀ x, δ ≤ G.degree x) :
    ∃ B : Finset V, B.card ≤ 4*(Nat.log 2 (Fintype.card V)+1) ∧
      ∀ x, ∃ v ∈ B, G.Adj v x := by
  classical
  let q := Nat.log 2 (Fintype.card V)+1
  obtain ⟨B,hB,hU⟩ := exists_iterated_cover G δ hδ hsize hdeg (4*q)
  have hN : Fintype.card V < 2^q := Nat.lt_pow_succ_log_self (by omega) _
  have hpower : 3^(4*q)*2^q ≤ 4^(4*q) := by
    calc
      _ = (3^4*2)^q := by rw [pow_mul,mul_pow]
      _ ≤ (4^4)^q := Nat.pow_le_pow_left (by norm_num) _
      _ = _ := by rw [pow_mul]
  have hlt : 3^(4*q)*Fintype.card V < 4^(4*q) :=
    (Nat.mul_lt_mul_of_pos_left hN (by positivity)).trans_le hpower
  have hzero : (uncovered G B).card = 0 := by
    by_contra h
    have hp := Nat.mul_le_mul_left (4^(4*q)) (Nat.one_le_iff_ne_zero.mpr h)
    simp only [mul_one] at hp
    omega
  refine ⟨B,hB,?_⟩
  intro x
  by_contra hx
  have hxU : x ∈ uncovered G B := by
    simp only [uncovered,Finset.mem_filter,Finset.mem_univ,true_and]
    simpa only [not_exists,not_and] using hx
  exact (Finset.card_pos.mpr ⟨x,hxU⟩).ne' hzero

end MinorFreeSpanners
