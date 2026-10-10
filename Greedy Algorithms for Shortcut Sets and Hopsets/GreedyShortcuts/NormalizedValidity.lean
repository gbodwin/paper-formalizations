import GreedyShortcuts.NormalizedReachability

/-! Earliest-entry filtering enforces contiguous chain visits in a DAG.
This proves validity and existence; it deliberately does not assert hereditary
optimality of the resulting source-dependent normalized distance. -/
namespace GreedyShortcuts.NormalizedValidity

open Finset SimpleGraph DirectedPaths CanonicalSegments NormalizedReachability ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V]

theorem crossing {F : V → V → Prop} (color : V → Option I) (c : I)
    {u v : V} (p : DWalk u v) (hp : Allowed F p)
    (hu : color u ≠ some c) (hv : color v = some c) :
    ∃ a b,F a b ∧ color a ≠ some c ∧ color b = some c ∧
      Reachable F u a ∧ Reachable F b v := by
  classical
  induction p with
  | nil => exact (hu hv).elim
  | @cons u w v ha p ih =>
    have hh := (allowed_cons F ha p).mp hp
    by_cases hw : color w = some c
    · exact ⟨u,w,hh.1,hu,hw,reachable_refl F u,⟨p,hh.2⟩⟩
    · obtain ⟨a,b,hab,hac,hbc,hwa,hbv⟩ := ih hh.2 hw hv
      exact ⟨a,b,hab,hac,hbc,reachable_trans (reachable_edge hh.1) hwa,hbv⟩

/-- Every visited chain occupies a contiguous interval of the actual walk.
The source-dependent earliest entry may prevent optimal subpaths, but it does
not prevent this contiguity statement. -/
theorem color_convex {G : V → V → Prop} (hG : Acyclic G)
    (color : V → Option I) (first : V → V → V)
    (hfirst : ∀ s v,Reachable G s v → color v ≠ none → Reachable G (first s v) v)
    (hconstant : ∀ s u v,color u = color v → first s u = first s v)
    {s t : V} {p : DWalk s t} (hp : Allowed (filtered G color first s) p)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ p.length)
    (c : I) (hi : color (p.getVert i) = some c) (hk' : color (p.getVert k) = some c) :
    color (p.getVert j) = some c := by
  classical
  by_contra hj
  have hseg := allowed_subwalk hp (segment_isSubwalk p j k hjk)
  obtain ⟨a,b,hab,hac,hbc,hja,hbk⟩ := crossing color c (segment p j k hjk) hseg hj hk'
  have hfirstb : first s b = b := by
    rcases hab.2 with heq | hnone | heq
    · exact (hac (heq.trans hbc)).elim
    · rw [hbc] at hnone
      cases hnone
    · exact heq
  have hpi : Reachable G s (p.getVert i) :=
    ⟨p.take i,allowed_mono (fun _ _ h => h.1) (allowed_subwalk hp (p.isSubwalk_take i))⟩
  have hback : Reachable G b (p.getVert i) := by
    have hh := hfirst s (p.getVert i) hpi (by rw [hi]; simp)
    rw [hconstant s (p.getVert i) b (hi.trans hbc.symm),hfirstb] at hh
    exact hh
  have hjb : Reachable G (p.getVert j) b :=
    reachable_trans (reachable_mono (fun _ _ h => h.1) hja) (reachable_edge hab.1)
  have hij' : Reachable G (p.getVert i) (p.getVert j) :=
    reachable_mono (fun _ _ h => h.1) (reachable_segment hp hij)
  have heq := (acyclic_iff_reachable_antisymm G).mp hG _ _ hij' (reachable_trans hjb hback)
  exact hj (heq ▸ hi)

/-- Every reachable pair has an actual earliest-entry, chain-contiguous walk
under the explicit chain-selector/internal-traversal interface. -/
theorem exists_valid_walk {G : V → V → Prop} (hG : Acyclic G)
    (color : V → Option I) (first : V → V → V)
    (hfirst : ∀ s v,Reachable G s v → color v ≠ none →
      Reachable G s (first s v) ∧ Reachable G (first s v) v ∧ color (first s v) = color v)
    (hconstant : ∀ s u v,color u = color v → first s u = first s v)
    (hinside : ∀ u v,Reachable G u v → color u = color v → color v ≠ none →
      ∃ p : DWalk u v,Allowed G p ∧ ∀ d ∈ p.darts,color d.fst = color d.snd)
    {s t : V} (hr : Reachable G s t) :
    ∃ p : DWalk s t,Allowed (filtered G color first s) p ∧ p.IsPath ∧
      ∀ i j k,i ≤ j → j ≤ k → k ≤ p.length → ∀ c : I,
        color (p.getVert i) = some c → color (p.getVert k) = some c →
          color (p.getVert j) = some c := by
  have hr' := (reachable_filtered_iff hG color first hfirst hinside s t).mpr hr
  let p := canonical (filtered G color first s) s t hr'
  have hp := canonical_optimal (filtered G color first s) s t hr'
  refine ⟨p,hp.1,hp.2.1,?_⟩
  intro i j k hij hjk hk c hi hk'
  exact color_convex hG color first (fun s v hr hc => (hfirst s v hr hc).2.1)
    hconstant hp.1 hij hjk hk c hi hk'

end GreedyShortcuts.NormalizedValidity
