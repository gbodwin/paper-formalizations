import GreedyShortcuts.ChainEntries

/-! A shortcut to an actual important prefix endpoint saves the same chain
cost on every later endpoint of the original fixed-source minimum path.
This is one-source accounting, not a cubic multi-source charging theorem. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem important_covered {s t : V} (hst : (s,t) ∈ T.important) :
    ∃ c,label T.chains t = some c := by
  classical
  obtain ⟨⟨u,c⟩,huc,he⟩ := Finset.mem_image.mp hst
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  exact ⟨c,(T.entry_spec (Finset.mem_filter.mp huc).2).2⟩

/-- The inserted edge replaces an expensive original-source prefix by a
cost-at-most-two path. The old distance is justified by true prefix optimality,
never by rebasing the source of a subpath. -/
theorem prefix_insertion_saving {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q))
    (hmin : T.count (p.append q) = T.distance H s t)
    (hpair : (s,u) ∈ T.important) :
    T.distance (insert (s,u) H) s t+T.count p ≤ T.distance H s t+2 := by
  classical
  obtain ⟨c,huc⟩ := T.important_covered hpair
  have hsu := (T.important_spec hpair).1
  have hst : Reachable T.G s t :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p.append q,allowed_mono (fun _ _ h => h.1) hpq⟩
  obtain ⟨r,hr,hrc⟩ := T.distance_spec (insert (s,u) H) hsu
  have hrc2 : T.count r≤2 := hrc.le.trans (T.direct_repair H hpair)
  have hq := (allowed_append _ p q).mp hpq |>.2
  have hq' : Allowed (T.graph (insert (s,u) H) s) q :=
    allowed_mono (T.graph_mono (Finset.subset_insert _ _) s) hq
  have hnew := T.distance_le_walk (insert (s,u) H) hst (r.append q)
    ((allowed_append _ r q).mpr ⟨hr,hq'⟩)
  have hsum := T.count_append_covered r q huc
  have hold := T.count_append_exact hH p q hpq
  simp only [huc,Option.toFinset_some,Finset.card_singleton] at hold
  omega

/-- A nontrivial minimum prefix yields a genuine legal closure edge. -/
theorem prefix_candidate {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q))
    (hmin : T.count (p.append q) = T.distance H s t)
    (hpair : (s,u) ∈ T.important) (hcost : 2≤T.count p) :
    (s,u) ∈ candidates T.G := by
  classical
  have hr := (T.important_spec hpair).1
  have hprefix := T.minimum_prefix hH p q hpq hmin
  have hne : s≠u := by
    intro he
    subst u
    have hd := T.distance_le_walk H hr .nil (allowed_nil _ _)
    have hc := T.count_le_vertices (Walk.nil : DWalk s s)
    simp only [Walk.length_nil] at hc
    omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,hr⟩

/-- Natural-subtraction form of the same actual graph saving. -/
theorem prefix_insertion_drop {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (p : DWalk s u) (q : DWalk u t)
    (hpq : Allowed (T.graph H s) (p.append q))
    (hmin : T.count (p.append q) = T.distance H s t)
    (hpair : (s,u) ∈ T.important) :
    T.count p-2 ≤ T.distance H s t-T.distance (insert (s,u) H) s t := by
  have h := T.prefix_insertion_saving hH p q hpq hmin hpair
  omega

/-- Exact whole-potential accounting for legal monotone insertion. -/
theorem potential_drop_sum (H : Finset (V × V)) (e : V × V) :
    T.potential H-T.potential (insert e H) =
      ∑ st ∈ T.important,(T.distance H st.1 st.2-T.distance (insert e H) st.1 st.2) := by
  symm
  exact Finset.sum_tsub_distrib _ (fun st _ =>
    T.distance_antitone st.1 st.2 (Finset.subset_insert _ _))

/-- A distinct one-source family of actual important targets contributes
its true savings to the original raw sum. -/
theorem source_drop_lower_bound (H : Finset (V × V)) (e : V × V)
    (s : V) (targets : Finset V) (saving : ℕ)
    (hpairs : ∀ v ∈ targets,(s,v) ∈ T.important)
    (hsave : ∀ v ∈ targets,saving ≤ T.distance H s v-T.distance (insert e H) s v) :
    targets.card*saving ≤ T.potential H-T.potential (insert e H) := by
  classical
  rw [T.potential_drop_sum]
  let pairs := targets.image (fun v => (s,v))
  have hsub : pairs ⊆ T.important := by
    intro st hst
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hst
    exact hpairs v hv
  calc
    targets.card*saving = ∑ _v ∈ targets,saving := by simp
    _ ≤ ∑ v ∈ targets,(T.distance H s v-T.distance (insert e H) s v) :=
      Finset.sum_le_sum hsave
    _ = ∑ st ∈ pairs,(T.distance H st.1 st.2-T.distance (insert e H) st.1 st.2) := by
      dsimp only [pairs]
      rw [Finset.sum_image]
      intro a _ b _ he
      exact Prod.mk.inj he |>.2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

end GreedyShortcuts.ChainDistance.Context
