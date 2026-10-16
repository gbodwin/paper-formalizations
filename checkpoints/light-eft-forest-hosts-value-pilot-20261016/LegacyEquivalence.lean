import LightEFTSpanners.StoredForestHosts
namespace LightEFTSpanners.StoredForestHosts.ValueComparison
def value {n : ℕ} : ℕ → List (List (Fin n × Fin n)) → List Record :=
  fun i fs => List.rec (motive := fun _ => ℕ → List Record) (fun _ => [])
    (fun es _ next j => (StoredDiscoveredHosts.value es).map (fun r => (j,r)) ++ next (j+1)) fs i
theorem value_eq_prior {n : ℕ} (i : ℕ) (fs : List (List (Fin n × Fin n))) :
    value i fs = LightEFTSpanners.StoredForestHosts.value i fs := by
  induction fs generalizing i with
  | nil => rfl
  | cons es fs ih =>
    exact congrArg (fun rest => (StoredDiscoveredHosts.value es).map (fun r => (i,r)) ++ rest) (ih (i+1))
#print axioms value_eq_prior
end LightEFTSpanners.StoredForestHosts.ValueComparison
