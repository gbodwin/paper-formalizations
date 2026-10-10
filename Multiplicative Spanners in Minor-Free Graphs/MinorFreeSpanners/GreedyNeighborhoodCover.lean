import MinorFreeSpanners.RobustCommonNeighbors
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log

/-! Deterministic neighborhood covering from actual finite incidence counts.
The logarithmic dominating-set construction will iterate this proved step. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [DecidableEq V] in
theorem neighborhood_cover_mass (G : SimpleGraph V) (S : Finset V) :
    (∑ v : V, (S.filter fun x => G.Adj v x).card) = ∑ x ∈ S, G.degree x := by
  classical
  calc
    _ = ∑ v : V, ∑ x ∈ S, if G.Adj v x then 1 else 0 := by
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    _ = ∑ x ∈ S, ∑ v : V, if G.Adj x v then 1 else 0 := by
      rw [Finset.sum_comm]
      simp_rw [G.adj_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter]
      have he : Finset.univ.filter (fun v => G.Adj x v) = G.neighborFinset x := by
        ext v
        simp
      rw [he]
      simp

omit [DecidableEq V] in
/-- An actual vertex covers at least one quarter of every selected set. -/
theorem exists_quarter_cover [Nonempty V] (G : SimpleGraph V) (δ : ℕ)
    (hδ : 0 < δ) (hsize : Fintype.card V ≤ 4*δ)
    (hdeg : ∀ x, δ ≤ G.degree x) (S : Finset V) :
    ∃ v, S.card ≤ 4*(S.filter fun x => G.Adj v x).card := by
  classical
  obtain ⟨v,_,hv⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    (fun v => (S.filter fun x => G.Adj v x).card) Finset.univ_nonempty
  have hlo : δ*S.card ≤ ∑ x ∈ S, G.degree x := by
    calc
      _ = ∑ _x ∈ S, δ := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => hdeg x)
  have hup : (∑ w : V, (S.filter fun x => G.Adj w x).card) ≤
      Fintype.card V*(S.filter fun x => G.Adj v x).card := by
    simpa using Finset.sum_le_sum (fun w hw => hv w hw)
  have hmul : δ*S.card ≤ δ*(4*(S.filter fun x => G.Adj v x).card) := by
    calc
      _ ≤ ∑ x ∈ S, G.degree x := hlo
      _ = ∑ w : V, (S.filter fun x => G.Adj w x).card := (neighborhood_cover_mass G S).symm
      _ ≤ Fintype.card V*(S.filter fun x => G.Adj v x).card := hup
      _ ≤ (4*δ)*(S.filter fun x => G.Adj v x).card := Nat.mul_le_mul_right _ hsize
      _ = _ := by ring
  exact ⟨v,Nat.le_of_mul_le_mul_left hmul hδ⟩

/-- Deleting this actual neighborhood decreases the uncovered cardinality
by a factor of at most three quarters, with integral arithmetic. -/
theorem exists_cover_step [Nonempty V] (G : SimpleGraph V) (δ : ℕ)
    (hδ : 0 < δ) (hsize : Fintype.card V ≤ 4*δ)
    (hdeg : ∀ x, δ ≤ G.degree x) (S : Finset V) :
    ∃ v, 4*(S \ G.neighborFinset v).card ≤ 3*S.card := by
  classical
  obtain ⟨v,hv⟩ := exists_quarter_cover G δ hδ hsize hdeg S
  have he : S.filter (fun x => G.Adj v x) = S ∩ G.neighborFinset v := by
    ext x
    simp
  rw [he] at hv
  have hc := Finset.card_sdiff_add_card_inter S (G.neighborFinset v)
  exact ⟨v,by omega⟩

end MinorFreeSpanners
