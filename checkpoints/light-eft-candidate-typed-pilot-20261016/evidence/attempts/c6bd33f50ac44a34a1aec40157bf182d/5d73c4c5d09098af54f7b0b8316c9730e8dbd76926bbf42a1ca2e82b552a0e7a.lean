import LightEFTSpanners.StoredCanonicalHosts

namespace LightEFTSpanners.StoredCanonicalHosts

theorem scanSteps_le (edges : List StoredEdges.Edge) (rs : List Component) (n : ℕ)
    (h : ∀ r∈rs,r.2.length≤n) :
    scanSteps edges rs≤rs.length*(StoredComponentHostFilter.bound n edges.length+2)+1 := by
  induction rs with
  | nil => simp [scanSteps]
  | cons r rs ih =>
    have hr := h r (by simp)
    have ht := ih (fun s hs => h s (by simp [hs]))
    have hb := StoredComponentHostFilter.steps_le r.2 edges
    have hm : StoredComponentHostFilter.bound r.2.length edges.length≤
        StoredComponentHostFilter.bound n edges.length := by
      unfold StoredComponentHostFilter.bound
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    simp only [scanSteps,List.length_cons,Nat.add_mul]
    omega

def bound (n m q : ℕ) : ℕ := q*(StoredComponentHostFilter.bound n m+3)+2

theorem steps_le (edges : List StoredEdges.Edge) (rs : List Component) (n : ℕ)
    (h : ∀ r∈rs,r.2.length≤n) : steps edges rs≤bound n edges.length rs.length := by
  have hs := scanSteps_le edges rs n h
  unfold steps bound
  have he : rs.length*(StoredComponentHostFilter.bound n edges.length+3)=
      rs.length*(StoredComponentHostFilter.bound n edges.length+2)+rs.length := by ring
  rw [he]
  omega
end LightEFTSpanners.StoredCanonicalHosts
