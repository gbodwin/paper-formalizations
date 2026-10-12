import MinorFreeSpanners.ExactConnectorPooling

/-! Telescope actual per-level credit inequalities with a literal disjoint
connector history. Earlier connectors contribute only once. A later hierarchy
must supply each phase inequality and its exact disjoint union certificate. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable

 theorem finite_history_ledger {E : Type*} (w : E → ℝ)
    (history fresh : ℕ → Finset E) (cost credit injection : ℕ → ℝ) (c : ℝ)
    (hzero : history 0=∅) (n : ℕ)
    (hdis : ∀ k<n,Disjoint (history k) (fresh k))
    (hnext : ∀ k<n,history (k+1)=history k∪fresh k)
    (hstep : ∀ k<n,cost k+credit (k+1)≤credit k+injection k+c*(∑ e∈fresh k,w e)) :
    (∑ k∈range n,cost k)+credit n≤credit 0+(∑ k∈range n,injection k)+c*(∑ e∈history n,w e) := by
  classical
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    have hp := ih (fun k hk => hdis k (Nat.lt_succ_of_lt hk))
      (fun k hk => hnext k (Nat.lt_succ_of_lt hk)) (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    have hs := hstep n (Nat.lt_succ_self n)
    rw [Finset.sum_range_succ,Finset.sum_range_succ,hnext n (Nat.lt_succ_self n),
      Finset.sum_union (hdis n (Nat.lt_succ_self n))]
    linarith only [hp,hs]

 theorem finite_history_ledger_bound {E : Type*} (w : E → ℝ)
    (history fresh : ℕ → Finset E) (cost credit injection : ℕ → ℝ) (c : ℝ)
    (hzero : history 0=∅) (n : ℕ)
    (hdis : ∀ k<n,Disjoint (history k) (fresh k))
    (hnext : ∀ k<n,history (k+1)=history k∪fresh k)
    (hstep : ∀ k<n,cost k+credit (k+1)≤credit k+injection k+c*(∑ e∈fresh k,w e))
    (hc : 0≤c) (hcredit : 0≤credit n) (tree : Finset E)
    (hsub : history n⊆tree) (hw : ∀ e∈tree,0≤w e) :
    (∑ k∈range n,cost k)≤credit 0+(∑ k∈range n,injection k)+c*(∑ e∈tree,w e) := by
  have hp := finite_history_ledger w history fresh cost credit injection c hzero n hdis hnext hstep
  have hs : (∑ e∈history n,w e)≤∑ e∈tree,w e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e he _ => hw e he)
  have hm := mul_le_mul_of_nonneg_left hs hc
  linarith only [hp,hm,hcredit]

end MinorFreeSpanners
