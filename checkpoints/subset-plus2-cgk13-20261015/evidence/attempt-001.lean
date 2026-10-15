import SlackSparsification.Neighborhoods
import Mathlib.Data.Finset.Lattice.Fold

/-! Supporting contracts for CGK13, Lemmas 5–8. Distances to a cluster
are extended naturals; empty clusters and disconnected pairs have distance ∞.
These lemmas do not assert existence of a clustering or a subset spanner. -/
namespace SlackSparsification.SubsetPlusTwo
open Finset SimpleGraph
variable {V : Type*}

/-- Global graph distance to a finite cluster, not distance restricted to a path. -/
noncomputable def clusterEDist (G : SimpleGraph V) (s : V) (C : Finset V) : ℕ∞ :=
  C.inf (G.edist s)

@[simp] theorem clusterEDist_empty (G : SimpleGraph V) (s : V) :
    clusterEDist G s ∅ = ⊤ := by simp [clusterEDist]

theorem clusterEDist_le (G : SimpleGraph V) (s : V) (C : Finset V)
    {v : V} (hv : v ∈ C) : clusterEDist G s C ≤ G.edist s v :=
  Finset.inf_le hv

theorem clusterEDist_attained (G : SimpleGraph V) (s : V) (C : Finset V)
    (hC : C.Nonempty) : ∃ v ∈ C, clusterEDist G s C = G.edist s v :=
  Finset.exists_mem_eq_inf C hC (G.edist s)

theorem clusterEDist_anti {G H : SimpleGraph V} (hGH : G ≤ H) (s : V) (C : Finset V) :
    clusterEDist H s C ≤ clusterEDist G s C := by
  apply Finset.le_inf
  intro v hv
  exact (clusterEDist_le H s C hv).trans (edist_anti hGH)

theorem clusterEDist_eq_top_of_unreachable (G : SimpleGraph V) (s : V) (C : Finset V)
    (h : ∀ v ∈ C, ¬ G.Reachable s v) : clusterEDist G s C = ⊤ := by
  apply top_unique
  apply Finset.le_inf
  intro v hv
  simp [edist_eq_top_of_not_reachable (h v hv)]

/-- A cluster has diameter at most two in the specified graph. -/
def ClusterDiameterTwo (H : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, H.edist a b ≤ 2

theorem diameter_mono {G H : SimpleGraph V} (hGH : G ≤ H) (C : Finset V)
    (hC : ClusterDiameterTwo G C) : ClusterDiameterTwo H C := by
  intro a ha b hb
  exact (edist_anti hGH).trans (hC a ha b hb)

/-- Every cluster member is within two of the global cluster minimum.
This is an inequality, not an equality of path-restricted/global minima. -/
theorem member_edist_le_cluster_add_two (G : SimpleGraph V) (s : V) (C : Finset V)
    (hC : ClusterDiameterTwo G C) {z : V} (hz : z ∈ C) :
    G.edist s z ≤ clusterEDist G s C + 2 := by
  obtain ⟨a, ha, hmin⟩ := clusterEDist_attained G s C ⟨z, hz⟩
  calc
    _ ≤ G.edist s a + G.edist a z := G.edist_triangle
    _ ≤ clusterEDist G s C + 2 := by rw [hmin]; exact add_le_add_left (hC a ha z hz) _

/-- Route through (possibly different) closest cluster vertices. -/
theorem route_through_cluster (H : SimpleGraph V) (s t : V) (C : Finset V)
    (hne : C.Nonempty) (hd : ClusterDiameterTwo H C) :
    H.edist s t ≤ clusterEDist H s C + clusterEDist H t C + 2 := by
  obtain ⟨a, ha, hsa⟩ := clusterEDist_attained H s C hne
  obtain ⟨b, hb, htb⟩ := clusterEDist_attained H t C hne
  calc
    _ ≤ H.edist s a + H.edist a t := H.edist_triangle
    _ ≤ H.edist s a + (H.edist a b + H.edist b t) := add_le_add_left H.edist_triangle _
    _ ≤ H.edist s a + (2 + H.edist t b) := by
      rw [H.edist_comm (u := b) (v := t)]
      exact add_le_add_left (add_le_add_right (hd a ha b hb) _) _
    _ = clusterEDist H s C + clusterEDist H t C + 2 := by rw [hsa, htb]; ac_rfl

/-- The rejection route needs only upper bounds by finite prefix/suffix
lengths at a shared path occurrence. It does not need global equalities. -/
theorem rejection_route (G H : SimpleGraph V) (s t : V) (C : Finset V)
    (hne : C.Nonempty) (hd : ClusterDiameterTwo H C) (a b : ℕ)
    (ha : clusterEDist H s C ≤ a) (hb : clusterEDist H t C ≤ b)
    (hsplit : ((a + b : ℕ) : ℕ∞) = G.edist s t) :
    H.edist s t ≤ G.edist s t + 2 := by
  calc
    _ ≤ clusterEDist H s C + clusterEDist H t C + 2 := route_through_cluster H s t C hne hd
    _ ≤ (a : ℕ∞) + b + 2 := add_le_add_right (add_le_add ha hb) _
    _ = G.edist s t + 2 := by rw [← Nat.cast_add, hsplit]

/-- Unreachable demand pairs require no path purchase, with edist semantics. -/
theorem unreachable_pair_satisfied (G H : SimpleGraph V) (s t : V)
    (h : ¬ G.Reachable s t) : H.edist s t ≤ G.edist s t + 2 := by
  simp [edist_eq_top_of_not_reachable h]

/-- Retaining a shortest prefix to a visited cluster vertex gives the
post-purchase additive-two bound needed for three-improvement charging. -/
theorem first_purchase_bound (G H : SimpleGraph V) (s : V) (C : Finset V)
    (hd : ClusterDiameterTwo G C) {z : V} (hz : z ∈ C)
    (hprefix : H.edist s z ≤ G.edist s z) :
    clusterEDist H s C ≤ clusterEDist G s C + 2 :=
  (clusterEDist_le H s C hz).trans
    (hprefix.trans (member_edist_le_cluster_add_two G s C hd hz))

/-- Once a pair is within two of its finite lower bound, three further
strict decreases are impossible. The initial ∞-to-finite improvement is
separate, giving at most three purchases in total. -/
theorem no_three_further_decreases (b : ℕ) (d₀ d₁ d₂ d₃ : ℕ∞)
    (h₀ : d₀ ≤ (b : ℕ∞) + 2) (h₁ : d₁ < d₀) (h₂ : d₂ < d₁)
    (h₃ : d₃ < d₂) (hb : (b : ℕ∞) ≤ d₃) : False := by
  have hfin : d₀ ≠ ⊤ := ne_top_of_le_ne_top (by simp) h₀
  have hfin₁ : d₁ ≠ ⊤ := ne_top_of_le_ne_top hfin h₁.le
  have hfin₂ : d₂ ≠ ⊤ := ne_top_of_le_ne_top hfin₁ h₂.le
  have hfin₃ : d₃ ≠ ⊤ := ne_top_of_le_ne_top hfin₂ h₃.le
  lift d₀ to ℕ using hfin
  lift d₁ to ℕ using hfin₁
  lift d₂ to ℕ using hfin₂
  lift d₃ to ℕ using hfin₃
  have hn₀ : d₀ ≤ b + 2 := by exact_mod_cast h₀
  have hn₁ : d₁ < d₀ := by exact_mod_cast h₁
  have hn₂ : d₂ < d₁ := by exact_mod_cast h₂
  have hn₃ : d₃ < d₂ := by exact_mod_cast h₃
  have hnb : b ≤ d₃ := by exact_mod_cast hb
  omega

/-- With an infinite global minimum, a subgraph cannot strictly improve it.
In particular no subtraction of ∞ or conversion of ∞ to zero is needed. -/
theorem no_improvement_at_infinite_lower_bound (d e : ℕ∞)
    (hd : (⊤ : ℕ∞) ≤ d) (he : (⊤ : ℕ∞) ≤ e) : ¬ e < d := by
  have hd' : d = ⊤ := top_unique hd
  have he' : e = ⊤ := top_unique he
  simp [hd', he']

end SlackSparsification.SubsetPlusTwo
