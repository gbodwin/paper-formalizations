import LightEFTSpanners.StoredForestHosts

namespace LightEFTSpanners.StoredForestHosts
open Controller

def inputBound (n : ℕ) (fs : List (List StoredEdges.Edge)) : ℕ :=
  (fs.map fun es => StoredDiscoveredHosts.bound n es.length+n+3).sum+1

theorem component_count {n : ℕ} (es : List (Fin n × Fin n)) :
    (StoredDiscoveredHosts.value es).length≤n := by
  simpa [StoredDiscoveredHosts.value,StoredCanonicalHosts.value] using
    StoredDiscoveredHosts.records_length es

theorem scan_trace {n : ℕ} (fs : List (List (Fin n × Fin n))) (i : ℕ) (acc : List Record) :
    ∃ k,k ≤ inputBound n (fs.map StoredEdges.encode) ∧
      Trace (transition n) k (.forests i (fs.map StoredEdges.encode) acc)
        (.reverse ((value i fs).reverse++acc) []) := by
  induction fs generalizing i acc with
  | nil => exact ⟨1,by simp [inputBound],Trace.one rfl⟩
  | cons es fs ih =>
    obtain ⟨k,hk,ht⟩ := StoredDiscoveredHosts.full_trace es
    have a := Trace.one (show transition n (.forests i ((StoredEdges.encode es)::fs.map StoredEdges.encode) acc)=
      some (.discover i (fs.map StoredEdges.encode) acc (StoredEdges.encode es) (.components (.range n []))) from rfl)
    have b := discover_lift n i (fs.map StoredEdges.encode) acc (StoredEdges.encode es) ht
    have c := Trace.one (show transition n (.discover i (fs.map StoredEdges.encode) acc (StoredEdges.encode es)
      (.halt (StoredDiscoveredHosts.value es)))=some (.append i (fs.map StoredEdges.encode) acc (StoredDiscoveredHosts.value es)) from rfl)
    have d := append_trace n i (fs.map StoredEdges.encode) acc (StoredDiscoveredHosts.value es)
    obtain ⟨l,hl,hu⟩ := ih (i+1) (((StoredDiscoveredHosts.value es).map (fun r => (i,r))).reverse++acc)
    refine ⟨1+k+1+((StoredDiscoveredHosts.value es).length+1)+l,?_,?_⟩
    · have hc := component_count es
      simp only [inputBound,List.map_cons,List.sum_cons,StoredEdges.encode,List.length_map] at *
      omega
    · simpa [value_cons,List.reverse_append,List.append_assoc,Nat.add_assoc] using
        a.trans (b.trans (c.trans (d.trans hu)))

theorem reverse_trace (n : ℕ) (rs out : List Record) :
    Trace (transition n) (rs.length+1) (.reverse rs out) (.halt (rs.reverse++out)) := by
  induction rs generalizing out with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n (.reverse (r::rs) out)=some (.reverse rs (r::out)) from rfl) (ih (r::out))

theorem value_length {n : ℕ} (fs : List (List (Fin n × Fin n))) (i : ℕ) :
    (value i fs).length≤fs.length*n := by
  induction fs generalizing i with
  | nil => simp [value_nil]
  | cons es fs ih =>
    have hc := component_count es
    have ht := ih (i+1)
    simp only [value_cons,List.length_append,List.length_map,List.length_cons,Nat.add_mul]
    omega
end LightEFTSpanners.StoredForestHosts
