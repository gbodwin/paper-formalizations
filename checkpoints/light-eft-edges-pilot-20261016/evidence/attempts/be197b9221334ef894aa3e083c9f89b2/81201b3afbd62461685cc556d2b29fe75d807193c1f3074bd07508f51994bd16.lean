import LightEFTSpanners.StoredForestHostsOriginal

namespace LightEFTSpanners.StoredForestHosts
attribute [local instance] Classical.propDecidable

def family {n q : ℕ} (edges : Fin q → List (Fin n × Fin n)) : Fin q → SimpleGraph (Fin n) :=
  fun i => ExecutableVoting.graph (StoredSample.edgeSet (edges i))

def indices {n q : ℕ} (edges : Fin q → List (Fin n × Fin n)) : List (ForestComponentIndex (family edges)) :=
  (List.finRange q).flatMap fun i => (StoredCanonicalComponents.indices (edges i)).map (Sigma.mk i)

theorem indices_all {n q : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (j : ForestComponentIndex (family edges)) : j∈indices edges := by
  obtain ⟨i,c⟩ := j
  exact List.mem_flatMap.mpr ⟨i,by simp,List.mem_map.mpr ⟨c,StoredCanonicalComponents.indices_all (edges i) c,rfl⟩⟩

theorem indices_nodup {n q : ℕ} (edges : Fin q → List (Fin n × Fin n)) : (indices edges).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _
    exact (StoredCanonicalComponents.indices_nodup (edges i)).map (fun _ _ h => by cases h; rfl)
  · apply (List.nodup_finRange q).imp
    intro i j hij
    apply List.disjoint_left.mpr
    intro x hx hy
    obtain ⟨c,_,hc⟩ := List.mem_map.mp hx
    obtain ⟨d,_,hd⟩ := List.mem_map.mp hy
    exact hij (congrArg Sigma.fst (hc.trans hd.symm))

theorem indices_univ {n q : ℕ} (edges : Fin q → List (Fin n × Fin n)) :
    (indices edges).toFinset=Finset.univ := by
  classical
  exact Finset.eq_univ_of_forall fun j => List.mem_toFinset.mpr (indices_all edges j)

def label (n : ℕ) (i r : ℕ) : ℕ := i*n+r

theorem label_injective {n i j r s : ℕ} (hr : r<n) (hs : s<n)
    (h : label n i r=label n j s) : i=j ∧ r=s := by
  have hn : 0<n := by omega
  have hi : label n i r/n=i := by
    simpa [label,Nat.add_comm,Nat.div_eq_of_lt hr] using Nat.add_mul_div_right r i hn
  have hj : label n j s/n=j := by
    simpa [label,Nat.add_comm,Nat.div_eq_of_lt hs] using Nat.add_mul_div_right s j hn
  have he : i=j := hi.symm.trans ((congrArg (fun x => x/n) h).trans hj)
  subst j
  exact ⟨rfl,by simpa [label] using h⟩
end LightEFTSpanners.StoredForestHosts
