import LightEFTSpanners.StoredReachability

namespace LightEFTSpanners.StoredReachability
open Controller

def values {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (root : Fin n) (vs : List (Fin n)) : List ℕ := (vs.filter (test G root)).map Fin.val

theorem scan_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (root : Fin n) (vs : List (Fin n)) (acc : List ℕ) :
    ∃ k,k≤vs.length*(LinkedDistance.bound n+2)+1 ∧
      Trace (transition n (LinkedDistance.matrixOf G (fun _ => 0)) root.val) k
        (.scan (vs.map Fin.val) acc) (.reverse ((values G root vs).reverse++acc) []) := by
  induction vs generalizing acc with
  | nil => exact ⟨1,by simp,Trace.one rfl⟩
  | cons v vs ih =>
    obtain ⟨k,hk,ht⟩ := LinkedDistance.machine_shortTest G (fun _ => 0) root v 0
    obtain ⟨l,hl,hs⟩ := ih (if test G root v then v.val::acc else acc)
    have a := Trace.one (show transition n (LinkedDistance.matrixOf G (fun _ => 0)) root.val
      (.scan ((v::vs).map Fin.val) acc)=some (.distance v.val (vs.map Fin.val) acc (.init n 0 [])) from rfl)
    have b := distance_lift n (LinkedDistance.matrixOf G (fun _ => 0)) root.val v.val (vs.map Fin.val) acc ht
    have c := Trace.one (show transition n (LinkedDistance.matrixOf G (fun _ => 0)) root.val
      (.distance v.val (vs.map Fin.val) acc (.halt (test G root v)))=
        some (.scan (vs.map Fin.val) (if test G root v then v.val::acc else acc)) from rfl)
    refine ⟨1+k+1+l,?_,?_⟩
    · unfold LinkedDistance.bound at *
      simp only [List.length_cons,Nat.add_mul]
      omega
    · have whole := a.trans (b.trans (c.trans hs))
      cases hb : test G root v <;>
        simpa [values,hb,List.filter_cons,List.reverse_cons,List.append_assoc,Nat.add_assoc] using whole

def bound (n count : ℕ) : ℕ := count*(LinkedDistance.bound n+3)+2

theorem component_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (root : Fin n) (vs : List (Fin n)) :
    ∃ k,k≤bound n vs.length ∧
      Trace (transition n (LinkedDistance.matrixOf G (fun _ => 0)) root.val) k
        (.scan (vs.map Fin.val) []) (.halt (values G root vs)) := by
  obtain ⟨k,hk,ht⟩ := scan_trace G root vs []
  simp only [List.append_nil] at ht
  have hr := reverse_trace n (LinkedDistance.matrixOf G (fun _ => 0)) root.val
    (values G root vs).reverse []
  have hl : (values G root vs).length≤vs.length := by
    simpa [values] using (List.length_filter_le (test G root) vs)
  refine ⟨k+(values G root vs).length+1,?_,?_⟩
  · unfold bound
    have he : vs.length*(LinkedDistance.bound n+3)=vs.length*(LinkedDistance.bound n+2)+vs.length := by
      simp only [Nat.mul_add]
      omega
    rw [he]
    omega
  · simpa [Nat.add_assoc] using ht.trans hr

theorem mem_values {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (root v : Fin n) (vs : List (Fin n)) :
    v.val∈values G root vs ↔ v∈vs ∧ G.Reachable root v := by
  simp only [values,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨u,⟨hu,hr⟩,he⟩
    have huv : u=v := Fin.ext he
    subst u
    exact ⟨hu,(test_iff G root v).mp hr⟩
  · rintro ⟨hv,hr⟩
    exact ⟨v,⟨hv,(test_iff G root v).mpr hr⟩,rfl⟩
end LightEFTSpanners.StoredReachability
