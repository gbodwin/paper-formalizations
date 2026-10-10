import GreedyShortcuts.ChainExcessPotential
import GreedyShortcuts.ChainEntries

/-! Endpoint saturation permits a narrowly stated reverse validity transfer.
This does not assert hereditary minimum-path optimality. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- A walk attaining the endpoint floor visits no other chain. -/
theorem chainSet_eq_endpoints_of_saturated {u v : V} (q : DWalk u v)
    (hq : T.count q = T.endpointFloor u v) :
    T.chainSet q = (label T.chains u).toFinset ∪ (label T.chains v).toFinset := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    rcases Finset.mem_union.mp hc with hu | hv
    · exact (T.mem_chainSet q c).mpr ⟨u,q.start_mem_support,by simpa using hu⟩
    · exact (T.mem_chainSet q c).mpr ⟨v,q.end_mem_support,by simpa using hv⟩
  · exact hq.le

/-- A saturated route between two of the same source's important entries
is valid for that source. The endpoint restriction is essential. -/
theorem saturated_route_transfer {H : Finset (V × V)} {s u v : V}
    (hsu : (s,u)∈T.important) (hsv : (s,v)∈T.important)
    (huv : (u,v)∈T.important) (q : DWalk u v)
    (hq : Allowed (T.graph H u) q) (hcount : T.count q=T.endpointFloor u v) :
    Allowed (T.graph H s) q := by
  classical
  have hset := T.chainSet_eq_endpoints_of_saturated q hcount
  intro d hd
  have hh := hq d hd
  refine ⟨hh.1,?_⟩
  rcases hh.2 with he | hn | hf
  · exact Or.inl he
  · exact Or.inr (Or.inl hn)
  · by_cases hn : label T.chains d.snd=none
    · exact Or.inr (Or.inl hn)
    · obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hn
      have hmem : c∈T.chainSet q := (T.mem_chainSet q c).mpr
        ⟨d.snd,q.dart_snd_mem_support_of_mem_darts hd,hc⟩
      rw [hset] at hmem
      have hlabels : label T.chains u=some c ∨ label T.chains v=some c := by
        simpa using hmem
      have hfirst : first T.chains s d.snd=first T.chains u d.snd := by
        rcases hlabels with hu | hv
        · have hs := (first_constant T.chains s d.snd u (hc.trans hu.symm)).trans
            (T.important_spec hsu).2
          have ht := (first_constant T.chains u d.snd u (hc.trans hu.symm)).trans (T.first_self u)
          exact hs.trans ht.symm
        · have hs := (first_constant T.chains s d.snd v (hc.trans hv.symm)).trans
            (T.important_spec hsv).2
          have ht := (first_constant T.chains u d.snd v (hc.trans hv.symm)).trans
            (T.important_spec huv).2
          exact hs.trans ht.symm
      exact Or.inr (Or.inr (hfirst.trans hf))

/-- A large fixed-source entry-distance gap excludes endpoint saturation
of the corresponding important shortcut choice. -/
theorem unsaturated_of_entry_gap (H : Finset (V × V)) {s u v : V}
    (hsu : (s,u)∈T.important) (hsv : (s,v)∈T.important)
    (huv : (u,v)∈T.important) (hgap : T.distance H s u+2<T.distance H s v) :
    (u,v)∈T.unsaturated H := by
  classical
  refine Finset.mem_filter.mpr ⟨huv,?_⟩
  by_contra hn
  change ¬T.endpointFloor u v<T.distance H u v at hn
  have hsat : T.distance H u v=T.endpointFloor u v :=
    Nat.le_antisymm (by omega) (T.endpointFloor_le_distance H (T.important_spec huv).1)
  obtain ⟨q,hq,hqc⟩ := T.distance_spec H (T.important_spec huv).1
  obtain ⟨p,hp,hpc⟩ := T.distance_spec H (T.important_spec hsu).1
  have hqs := T.saturated_route_transfer hsu hsv huv q hq (hqc.trans hsat)
  have hd := T.distance_le_walk H (T.important_spec hsv).1 (p.append q)
    ((allowed_append _ p q).mpr ⟨hp,hqs⟩)
  have hc := T.count_append_le p q
  have hf := T.endpointFloor_le_two u v
  omega

end GreedyShortcuts.ChainDistance.Context
