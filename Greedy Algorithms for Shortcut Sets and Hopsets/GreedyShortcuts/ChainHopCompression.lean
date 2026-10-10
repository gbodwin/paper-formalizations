import GreedyShortcuts.ChainCover
import GreedyShortcuts.ColoredHopBound

/-! Convert the actual normalized chain count to ordinary hop length by
compressing within the finite set of colors of a supplied valid walk. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ChainCover
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem compress_walk {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p) :
    ∃ q : DWalk s t,Allowed (augment T.G (T.base ∪ H)) q ∧
      q.length+1 ≤ (uncovered T p).card+5*T.count p := by
  classical
  have hshort : ∀ u v c,Reachable (augment T.G (T.base ∪ H)) u v →
      label T.chains u = some c → label T.chains v = some c →
      ∃ q : DWalk u v,Allowed (augment T.G (T.base ∪ H)) q ∧ q.length ≤ 4 ∧
        ∀ x ∈ q.support,label T.chains x = some c := by
    intro u v c hr hu hv
    exact internal_short T hH ((reachable_augment_iff T.G _ (T.augmentation_legal hH) u v).mp hr) hu hv
  obtain ⟨q,hq,hlen,hrest⟩ := ColoredHopBound.compress (label T.chains)
    (T.chainSet p) (uncovered T p) 4 hshort p (allowed_mono (fun _ _ h => h.1) hp) (by
      intro v hv
      refine ⟨fun hn => Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv,hn⟩,?_⟩
      intro c hc
      exact Finset.mem_biUnion.mpr ⟨v,List.mem_toFinset.mpr hv,by simp [hc]⟩)
  exact ⟨q,hq,hlen⟩

/-- The cover's uncovered-vertex budget also applies after legal shortcut
insertion. Thus normalized minima yield actual ordinary-hop paths. -/
theorem distance_hop_bound {U : ℕ} (hcover : IsCover T U)
    {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (hr : Reachable T.G s t) :
    ∃ q : DWalk s t,Allowed (augment T.G (T.base ∪ H)) q ∧
      q.length ≤ U+5*T.distance H s t := by
  obtain ⟨p,hp,he⟩ := T.distance_spec H hr
  obtain ⟨q,hq,hlen⟩ := T.compress_walk hH p hp
  have hU := uncovered_le_of_legal T hcover hH p (allowed_mono (fun _ _ h => h.1) hp)
  exact ⟨q,hq,by rw [he] at hlen;omega⟩

end GreedyShortcuts.ChainDistance.Context
