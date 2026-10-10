import GreedyShortcuts.ChainPrefix
import GreedyShortcuts.ChainHopCorrectness

/-! The actual earliest-entry demand for every visited chain occurs on a
valid path. This gives distinct important vertices on fixed-source minima. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- A walk entering a color contains a literal dart entering that color. -/
theorem entering_dart (color : V → Option I) (c : I) {u v : V}
    (p : DWalk u v) (hu : color u ≠ some c) (hv : color v = some c) :
    ∃ d ∈ p.darts,color d.fst ≠ some c ∧ color d.snd = some c := by
  classical
  induction p with
  | nil => exact (hu hv).elim
  | @cons u w v ha p ih =>
    by_cases hw : color w = some c
    · exact ⟨⟨(u,w),ha⟩,by simp,hu,hw⟩
    · obtain ⟨d,hd,hdu,hdv⟩ := ih hw hv
      exact ⟨d,by simp only [Walk.darts_cons,List.mem_cons];exact Or.inr hd,hdu,hdv⟩

variable (T : ChainDistance.Context V I)

theorem first_self (s : V) : first T.chains s s = s := by
  by_cases hc : label T.chains s = none
  · simp only [first,hc]
  · have hf := first_spec T.chains T.disjoint s s (reachable_refl T.G s) hc
    exact (acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hf.2.1 hf.1

/-- Every visited chain's canonical important target is a vertex of this
actual path. It is not supplied by an independent reachability witness. -/
theorem first_mem_support {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    {v : V} (hv : v ∈ p.support) {c : I} (hc : label T.chains v = some c) :
    first T.chains s v ∈ p.support := by
  classical
  by_cases hs : label T.chains s = some c
  · have he := (first_constant T.chains s v s (hc.trans hs.symm)).trans (T.first_self s)
    rw [he]
    exact p.start_mem_support
  · let q := p.takeUntil v hv
    have hq : Allowed (T.graph H s) q := allowed_subwalk hp (p.isSubwalk_takeUntil hv)
    obtain ⟨d,hd,hdu,hdv⟩ := entering_dart (label T.chains) c q hs hc
    have he := (hq d hd).2
    have hdneq : label T.chains d.fst ≠ label T.chains d.snd := by
      intro h;exact hdu (h.trans hdv)
    have hdnone : label T.chains d.snd ≠ none := by simp only [hdv];simp
    have hf := he.resolve_left hdneq |>.resolve_left hdnone
    have hsame := first_constant T.chains s v d.snd (hc.trans hdv.symm)
    rw [hsame,hf]
    exact (Walk.isSubwalk_iff_support_isInfix.mp (p.isSubwalk_takeUntil hv)).subset
      (q.dart_snd_mem_support_of_mem_darts hd)

noncomputable def pathEntries {s t : V} (p : DWalk s t) : Finset V :=
  (T.chainSet p).image (entry T.chains s)

theorem entry_label {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    {c : I} (hc : c ∈ T.chainSet p) :
    label T.chains (entry T.chains s c) = some c := by
  obtain ⟨v,hv,hvc⟩ := (T.mem_chainSet p c).mp hc
  have hsv : Reachable T.G s v :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p.takeUntil v hv,allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk hp (p.isSubwalk_takeUntil hv))⟩
  have hf := (first_spec T.chains T.disjoint s v hsv (by simp [hvc])).2.2
  simpa only [first,hvc] using hf.trans hvc

/-- The path contains exactly one canonical entry for each of its chains. -/
theorem pathEntries_card {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p) :
    (T.pathEntries p).card = T.count p := by
  classical
  apply Finset.card_image_iff.mpr
  intro c hc d hd he
  exact Option.some.inj ((T.entry_label hH p hp hc).symm.trans
    ((congrArg (label T.chains) he).trans (T.entry_label hH p hp hd)))

theorem pathEntries_mem {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    {v : V} (hv : v ∈ T.pathEntries p) :
    v ∈ p.support ∧ (s,v) ∈ T.important := by
  classical
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨u,hu,huc⟩ := (T.mem_chainSet p c).mp hc
  have hsu : Reachable T.G s u :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p.takeUntil u hu,allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk hp (p.isSubwalk_takeUntil hu))⟩
  constructor
  · simpa only [first,huc] using T.first_mem_support hH p hp hu huc
  · simpa only [first,huc] using T.first_important hsu huc

/-- At every actual prefix endpoint of a minimum path, the old distance is
its exact prefix chain count, while keeping the original source. -/
theorem minimum_takeUntil {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (hmin : T.count p = T.distance H s t) {v : V} (hv : v ∈ p.support) :
    T.count (p.takeUntil v hv) = T.distance H s v := by
  apply T.minimum_prefix hH (p.takeUntil v hv) (p.dropUntil v hv)
  · simpa only [p.take_spec hv] using hp
  · simpa only [p.take_spec hv] using hmin

end GreedyShortcuts.ChainDistance.Context
