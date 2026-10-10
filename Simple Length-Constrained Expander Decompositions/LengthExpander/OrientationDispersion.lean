import LengthExpander.SparseOrientation
import LengthExpander.ListDemands

/-! A sparse-order alternative to rooted-forest dispersion. Pair incoming
children at each center. A vertex is a child at most K times and is its own
center once, so its total dispersed incidence is at most K+1. At least
half of all original edges survive as dispersed demand units. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def orientationPairs (G : SimpleGraph V) (L : List V) (p : V) : List (V × V) :=
  pairChildren p (orientationChildren G L p).toList

noncomputable def orientationDispersion (G : SimpleGraph V) (L : List V) : Demand V :=
  fun u v => ∑ p, listDemand (orientationPairs G L p) u v

theorem orientationDispersion_size (G : SimpleGraph V) (L : List V) :
    demandSize (orientationDispersion G L) = ∑ p, (orientationPairs G L p).length := by
  classical
  unfold demandSize orientationDispersion
  calc
    _ = ∑ u, ∑ p, ∑ v, listDemand (orientationPairs G L p) u v :=
      sum_congr rfl (fun u _ => sum_comm)
    _ = ∑ p, ∑ u, ∑ v, listDemand (orientationPairs G L p) u v := sum_comm
    _ = _ := sum_congr rfl (fun p _ => listDemand_size _)

theorem orientationDispersion_large (G : SimpleGraph V) (L : List V)
    (hcover : L.toFinset = univ) :
    Fintype.card G.edgeSet ≤ 2*demandSize (orientationDispersion G L) := by
  classical
  rw [← orientationChildren_total G L hcover,orientationDispersion_size,mul_sum]
  apply sum_le_sum
  intro p _
  simpa only [length_toList,orientationPairs] using pairChildren_large p (orientationChildren G L p).toList

theorem orientationDispersion_incidence {K : ℕ} {L : List V}
    (hL : SparseOrder G K L) (hcover : L.toFinset = univ) (u : V) :
    (∑ v, orientationDispersion G L u v) +
      (∑ v, orientationDispersion G L v u) ≤ K+1 := by
  classical
  have hr : (∑ v, orientationDispersion G L u v) =
      ∑ p, ∑ v, listDemand (orientationPairs G L p) u v := sum_comm
  have hc : (∑ v, orientationDispersion G L v u) =
      ∑ p, ∑ v, listDemand (orientationPairs G L p) v u := sum_comm
  rw [hr,hc,← sum_add_distrib]
  simp_rw [listDemand_incidence]
  calc
    _ ≤ ∑ p, ((orientationChildren G L p).toList.count u + if u = p then 1 else 0) :=
      sum_le_sum (fun p _ => pairChildren_count p u _)
    _ = (univ.filter (fun p => u ∈ orientationChildren G L p)).card + 1 := by
      rw [sum_add_distrib]
      simp_rw [count_finset_toList]
      simp
    _ ≤ K+1 := Nat.add_le_add_right (orientationChildren_budget hL hcover u) 1

/-- Distinct endpoint occurrence lists rule out diagonal demand pairs. -/
theorem pair_ne_of_endpoints_nodup {P : List (V × V)}
    (hP : (pairEndpoints P).Nodup) {x y : V} (hxy : (x,y) ∈ P) : x ≠ y := by
  induction P with
  | nil => simp at hxy
  | cons e P ih =>
    rcases e with ⟨u,v⟩
    have hnd : (u::v::pairEndpoints P).Nodup := hP
    rcases List.mem_cons.mp hxy with he | he
    · cases he
      exact fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
    · exact ih (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2 he

theorem orientationDispersion_support {L : List V} {x y : V}
    (hxy : 0 < orientationDispersion G L x y) :
    G.Adj x y ∨ ∃ p, G.Adj x p ∧ G.Adj p y ∧ x ≠ y := by
  classical
  obtain ⟨p,_,hp⟩ := (sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hxy
  have hpair := (listDemand_positive_iff (orientationPairs G L p) x y).mp hp
  have hm := pairChildren_mem p hpair
  have hx : x ∈ orientationChildren G L p := mem_toList.mp hm.1
  rcases hm.2 with hy | hy
  · have hy : y ∈ orientationChildren G L p := mem_toList.mp hy
    refine Or.inr ⟨p,(mem_orientationChildren.mp hx).1,(mem_orientationChildren.mp hy).1.symm,?_⟩
    exact pair_ne_of_endpoints_nodup
      (pairChildren_nodup p (nodup_toList _) (by simpa using orientationChildren_no_self (G := G) L p)) hpair
  · subst y
    exact Or.inl (mem_orientationChildren.mp hx).1

end LengthExpander
