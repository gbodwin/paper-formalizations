import GreedyShortcuts.ChainHopCompression

/-! Ordinary-hop correctness for the actual chain Algorithm 2. Its sharper
shortcut cardinality still requires the unresolved cubic-progress argument. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ChainCover
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem first_important {s v : V} (hr : Reachable T.G s v) {c : I}
    (hc : label T.chains v = some c) : (s,first T.chains s v) ∈ T.important := by
  classical
  obtain ⟨i,hi,hiv⟩ := Finset.mem_image.mp (mem_of_label T.chains hc)
  have hne : (reachableIndices T.chains s c).Nonempty :=
    ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hiv] using hr⟩⟩
  exact Finset.mem_image.mpr ⟨(s,c),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩,
    by simp only [first,hc]⟩

/-- Stopping on the actual important pairs suffices for all original reachable
pairs, using a proved cover conversion and the actual supershortcut union. -/
theorem stopped_hop_bound {U D : ℕ} (hcover : IsCover T U)
    {H : Finset (V × V)} (hH : H ⊆ candidates T.G) (hstop : T.stopped D H)
    {s t : V} (hr : Reachable T.G s t) :
    ∃ q : DWalk s t,Allowed (augment T.G (T.base ∪ H)) q ∧ q.length ≤ 2*U+5*D+4 := by
  classical
  rcases covered_tail T hcover hr with ⟨q,hq,hqU⟩ | ⟨v,c,hsv,hvc,r,hrG,hrU⟩
  · exact ⟨q,allowed_mono (fun _ _ h => Or.inl h) hq,by omega⟩
  · have hf := first_spec T.chains T.disjoint s v hsv (by simp [hvc])
    have hpair := T.first_important hsv hvc
    obtain ⟨p,hp,hpL⟩ := T.distance_hop_bound hcover hH hf.1
    have hD := hstop _ hpair
    dsimp only at hD
    obtain ⟨a,ha,ha4,haC⟩ := internal_short T hH hf.2.1 (hf.2.2.trans hvc) hvc
    refine ⟨(p.append a).append r,?_,?_⟩
    · exact (allowed_append _ _ _).mpr ⟨(allowed_append _ _ _).mpr ⟨hp,ha⟩,
        allowed_mono (fun _ _ h => Or.inl h) hrG⟩
    · simp only [Walk.length_append]
      omega

theorem shortcuts_hop_bound {U : ℕ} (hcover : IsCover T U)
    (D : ℕ) (hD : 2 ≤ D) {s t : V} (hr : Reachable T.G s t) :
    ∃ q : DWalk s t,Allowed (augment T.G (T.shortcuts D hD)) q ∧ q.length ≤ 2*U+5*D+4 :=
  T.stopped_hop_bound hcover (T.output_legal D hD) (T.output_stopped D hD) hr

end GreedyShortcuts.ChainDistance.Context
