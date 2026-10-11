import GreedyShortcuts.ChainSaturationCapacity

/-! Endpoint incidence at new excess at most one. The conclusion is restricted
to covered interchain insertions and does not extend to excess two. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem dart_endpoint_exclusions {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (hst : (s,t) ∈ T.important) (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (e : (⊤ : SimpleGraph V).Dart) (he : e ∈ p.darts) {c d : I}
    (hc : label T.chains e.fst = some c) (hd : label T.chains e.snd = some d)
    (hcd : c ≠ d) : label T.chains s ≠ some d ∧ label T.chains t ≠ some c := by
  have hh := hp e he
  have hlabels : label T.chains e.fst ≠ label T.chains e.snd := by
    rw [hc,hd]
    exact fun h => hcd (Option.some.inj h)
  have hfirst : first T.chains s e.snd = e.snd :=
    hh.2.resolve_left hlabels |>.resolve_left (by simp [hd])
  have hsu : Reachable T.G s e.fst :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p.takeUntil e.fst (p.dart_fst_mem_support_of_mem_darts he),
        allowed_mono (fun _ _ h => h.1) (allowed_subwalk hp
          (p.isSubwalk_takeUntil (p.dart_fst_mem_support_of_mem_darts he)))⟩
  have huv : Reachable T.G e.fst e.snd :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp (reachable_edge hh.1)
  have hvt : Reachable T.G e.snd t :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p.dropUntil e.snd (p.dart_snd_mem_support_of_mem_darts he),
        allowed_mono (fun _ _ h => h.1) (allowed_subwalk hp
          (p.isSubwalk_dropUntil (p.dart_snd_mem_support_of_mem_darts he)))⟩
  constructor
  · intro hs
    have hsame := (first_constant T.chains s e.snd s (hd.trans hs.symm)).trans (T.first_self s)
    have hes : e.snd = s := hfirst.symm.trans hsame
    have hse := (acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hsu (by simpa [hes] using huv)
    have heq : some c = some d := hc.symm.trans ((congrArg (label T.chains) hse.symm).trans hs)
    exact hcd (Option.some.inj heq)
  · intro ht
    have hspec := first_spec T.chains T.disjoint s e.fst hsu (by simp [hc])
    have hf : first T.chains s e.fst = t :=
      (first_constant T.chains s e.fst t (hc.trans ht.symm)).trans (T.important_spec hst).2
    have htu : Reachable T.G t e.fst := by simpa only [hf] using hspec.2.1
    have heq := (acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ huv (reachable_trans hvt htu)
    exact hcd (Option.some.inj (hc.symm.trans ((congrArg (label T.chains) heq).trans hd)))

/-- A valid near-floor route using a covered interchain dart has source-tail
or target-head incidence. In the latter case the head is the important target. -/
theorem near_floor_dart_incidence {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (hst : (s,t) ∈ T.important) (p : DWalk s t) (hp : Allowed (T.graph H s) p)
    (hcount : T.count p ≤ T.endpointFloor s t+1)
    (e : (⊤ : SimpleGraph V).Dart) (he : e ∈ p.darts) {c d : I}
    (hc : label T.chains e.fst = some c) (hd : label T.chains e.snd = some d)
    (hcd : c ≠ d) : label T.chains s = some c ∨ t=e.snd := by
  classical
  have hx := T.dart_endpoint_exclusions hH hst p hp e he hc hd hcd
  have incidence : label T.chains s = some c ∨ label T.chains t = some d := by
    by_contra hn
    push Not at hn
    let F := (label T.chains s).toFinset ∪ (label T.chains t).toFinset
    have hcn : c∉F := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hn.1 (by simpa using h)
      · exact hx.2 (by simpa using h)
    have hdn : d∉F := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hx.1 (by simpa using h)
      · exact hn.2 (by simpa using h)
    have hF : F ⊆ T.chainSet p := by
      intro j hj
      rcases Finset.mem_union.mp hj with h | h
      · exact (T.mem_chainSet p j).mpr ⟨s,p.start_mem_support,by simpa using h⟩
      · exact (T.mem_chainSet p j).mpr ⟨t,p.end_mem_support,by simpa using h⟩
    have hsub : insert c (insert d F) ⊆ T.chainSet p :=
      Finset.insert_subset ((T.mem_chainSet p c).mpr
        ⟨e.fst,p.dart_fst_mem_support_of_mem_darts he,hc⟩)
        (Finset.insert_subset ((T.mem_chainSet p d).mpr
          ⟨e.snd,p.dart_snd_mem_support_of_mem_darts he,hd⟩) hF)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hcd,hcn]),Finset.card_insert_of_notMem hdn] at hcard
    change T.endpointFloor s t+1+1 ≤ T.count p at hcard
    omega
  rcases incidence with hs | ht
  · exact Or.inl hs
  · right
    have hlabels : label T.chains e.fst ≠ label T.chains e.snd := by
      rw [hc,hd]
      exact fun h => hcd (Option.some.inj h)
    have hf := (hp e he).2.resolve_left hlabels |>.resolve_left (by simp [hd])
    have hi := (first_constant T.chains s e.snd t (hd.trans ht.symm)).trans (T.important_spec hst).2
    exact hi.symm.trans hf

/-- Any strict improvement to excess at most one has this incidence, with no
upper bound on the old distance. -/
theorem near_floor_improvement_incidence {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v s t : V} {c d : I} (he : (u,v) ∈ candidates T.G)
    (hu : label T.chains u = some c) (hv : label T.chains v = some d) (hcd : c ≠ d)
    (hst : (s,t) ∈ T.important)
    (hnew : T.distance (insert (u,v) H) s t ≤ T.endpointFloor s t+1)
    (hdrop : T.distance (insert (u,v) H) s t < T.distance H s t) :
    label T.chains s = some c ∨ t=v := by
  classical
  have hlegal : insert (u,v) H ⊆ candidates T.G := Finset.insert_subset he hH
  have hr := (T.important_spec hst).1
  obtain ⟨p,hp,hpc⟩ := T.distance_spec (insert (u,v) H) hr
  have hbad : ¬Allowed (T.graph H s) p := by
    intro hh
    have hb := T.distance_le_walk H hr p hh
    omega
  simp only [Allowed,not_forall] at hbad
  obtain ⟨dart,hmem,hnot⟩ := hbad
  have hstep := hp dart hmem
  have hedge : (dart.fst,dart.snd) = (u,v) := by
    rcases hstep.1 with hg | hh
    · exact (hnot ⟨Or.inl hg,hstep.2⟩).elim
    rcases Finset.mem_union.mp hh with hb | hi
    · exact (hnot ⟨Or.inr (Finset.mem_union_left _ hb),hstep.2⟩).elim
    rcases Finset.mem_insert.mp hi with heq | hmem
    · exact heq
    · exact (hnot ⟨Or.inr (Finset.mem_union_right _ hmem),hstep.2⟩).elim
  have hfst : dart.fst = u := congrArg Prod.fst hedge
  have hsnd : dart.snd = v := congrArg Prod.snd hedge
  have hi := T.near_floor_dart_incidence hlegal hst p hp (by omega) dart hmem
    (by simpa only [hfst] using hu) (by simpa only [hsnd] using hv) hcd
  simpa only [hsnd] using hi

/-- A finite incidence budget for arbitrary old distances but new excess at
most one. This deliberately uses the simpler n+r_c*I upper bound. -/
theorem near_floor_improvement_card_le {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} {c d : I} (he : (u,v) ∈ candidates T.G)
    (hu : label T.chains u = some c) (hv : label T.chains v = some d) (hcd : c ≠ d)
    (B : Finset (V × V)) (hB : B ⊆ T.important)
    (hnew : ∀ st∈B,T.distance (insert (u,v) H) st.1 st.2 ≤ T.endpointFloor st.1 st.2+1)
    (hdrop : ∀ st∈B,T.distance (insert (u,v) H) st.1 st.2 < T.distance H st.1 st.2) :
    B.card ≤ (T.chains c).length*Fintype.card I+Fintype.card V := by
  classical
  let X := ((T.chains c).support ×ˢ (Finset.univ : Finset I)).image
    (fun sc => (sc.1,entry T.chains sc.1 sc.2))
  let Y := (Finset.univ : Finset V).image (fun s => (s,v))
  have hsub : B ⊆ X ∪ Y := by
    intro st hs
    rcases T.near_floor_improvement_incidence hH he hu hv hcd (hB hs)
      (hnew st hs) (hdrop st hs) with hsrc | ht
    · apply Finset.mem_union_left
      obtain ⟨⟨s,j⟩,_hmem,heq⟩ := Finset.mem_image.mp (hB hs)
      have hfst : s=st.1 := congrArg Prod.fst heq
      exact Finset.mem_image.mpr ⟨(s,j),Finset.mem_product.mpr
        ⟨by simpa only [hfst] using (mem_of_label T.chains hsrc),Finset.mem_univ _⟩,heq⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨st.1,Finset.mem_univ _,Prod.ext rfl ht.symm⟩
  have hX : X.card ≤ (T.chains c).length*Fintype.card I := by
    calc
      _ ≤ ((T.chains c).support ×ˢ (Finset.univ : Finset I)).card := Finset.card_image_le
      _ = _ := by simp [ChainUnion.Chain.support_card]
  have hY : Y.card ≤ Fintype.card V :=
    (Finset.card_image_le).trans (by simp)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hX hY))

/-- First-positive-layer depletion obeys this actual incidence budget. The
analogous claim at excess layer two is not asserted. -/
theorem first_layer_depletion_le {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} {c d : I} (he : (u,v) ∈ candidates T.G)
    (hu : label T.chains u = some c) (hv : label T.chains v = some d) (hcd : c ≠ d) :
    (T.excessLayer H 1).card-(T.excessLayer (insert (u,v) H) 1).card ≤
      (T.chains c).length*Fintype.card I+Fintype.card V := by
  classical
  let B := T.excessLayer H 1 \ T.excessLayer (insert (u,v) H) 1
  have hB : B ⊆ T.important := fun _ h => (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
  have hn : ∀ st∈B,T.distance (insert (u,v) H) st.1 st.2 ≤ T.endpointFloor st.1 st.2+1 := by
    intro st hs
    have hm := Finset.mem_sdiff.mp hs
    have hnot : ¬1<T.distance (insert (u,v) H) st.1 st.2-T.endpointFloor st.1 st.2 := by
      intro hh
      exact hm.2 (Finset.mem_filter.mpr ⟨hB hs,hh⟩)
    omega
  have hd : ∀ st∈B,T.distance (insert (u,v) H) st.1 st.2 < T.distance H st.1 st.2 := by
    intro st hs
    have hh := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hs).1).2
    have h := hn st hs
    omega
  have hh := T.near_floor_improvement_card_le hH he hu hv hcd B hB hn hd
  have hc : B.card=(T.excessLayer H 1).card-(T.excessLayer (insert (u,v) H) 1).card :=
    Finset.card_sdiff_of_subset (T.excessLayer_antitone 1 (Finset.subset_insert _ _))
  simpa only [hc] using hh

end GreedyShortcuts.ChainDistance.Context
