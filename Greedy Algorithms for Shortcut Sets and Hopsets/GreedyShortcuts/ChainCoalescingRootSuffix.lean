import GreedyShortcuts.ChainFixedRootSuffix

/-! SOURCE ONLY, UNCOMPILED. A derived additive transition cost permits
the existing consistent tie score to select a genuine coalescing suffix
system in ONE fixed ROOT filter. Original owner minima remain inputs;
their canonical replacements are separately displayed equal-price walks. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def rootStartMarker (v : V) : ℕ :=
  (label T.chains v).toFinset.card

/-- Count only a new covered-chain entry. Uncovered entries and steps
inside one covered chain have cost zero. -/
noncomputable def rootTransitionStep (u v : V) : ℕ :=
  if label T.chains u=label T.chains v ∨ label T.chains v=none then 0 else 1

noncomputable def rootTransitionCount {b W : V} (q : DWalk b W) : ℕ :=
  (q.darts.map (fun d => T.rootTransitionStep d.fst d.snd)).sum

private theorem rootTransition_edge_count {b u : V}
    (h : (⊤ : SimpleGraph V).Adj b u) :
    T.count (.cons h (.nil : DWalk u u))=
      T.rootStartMarker b+T.rootTransitionStep b u := by
  classical
  cases hb : label T.chains b with
  | none =>
    cases hu : label T.chains u with
    | none => simp [count,chainSet,rootStartMarker,rootTransitionStep,hb,hu]
    | some c => simp [count,chainSet,rootStartMarker,rootTransitionStep,hb,hu]
  | some c =>
    cases hu : label T.chains u with
    | none => simp [count,chainSet,rootStartMarker,rootTransitionStep,hb,hu]
    | some d =>
      by_cases he : c=d
      · subst d
        simp [count,chainSet,rootStartMarker,rootTransitionStep,hb,hu]
      · simp [count,chainSet,rootStartMarker,rootTransitionStep,hb,hu,he]

/-- Exact native primary cost, not an assumed weight/count correspondence.
ROOT must originally reach the physical start. Every recursive tail is
still ROOT-filtered; forward rebasing is used only for exact native joins. -/
theorem fixed_root_count_eq_marker_transitions {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W : V} (q : DWalk b W) :
    Reachable T.G root b → Allowed (T.graph H root) q →
      T.count q=T.rootStartMarker b+T.rootTransitionCount q := by
  classical
  induction q with
  | nil =>
    intro _hroot _hq
    simp [count,chainSet,rootStartMarker,rootTransitionCount]
  | @cons b u W h q ih =>
    intro hrootb hwhole
    obtain ⟨hbu,hq⟩ := (allowed_cons _ h q).mp hwhole
    have hbuG : Reachable T.G b u :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨.cons h .nil,(allowed_cons _ h .nil).mpr ⟨hbu.1,allowed_nil _ _⟩⟩
    have hrootu := reachable_trans hrootb hbuG
    have htail := ih hrootu hq
    have hown := T.allowed_rebase hH hrootb (.cons h q) hwhole
    have hjoin := T.count_append_exact hH (.cons h .nil) q hown
    have hj : T.count (.cons h q)+T.rootStartMarker u=
        T.count (.cons h (.nil : DWalk u u))+T.count q := by
      simpa only [Walk.cons_append,Walk.nil_append,rootStartMarker] using hjoin
    have hedge := rootTransition_edge_count T h
    have hs : T.rootTransitionCount (.cons h q)=
        T.rootTransitionStep b u+T.rootTransitionCount q := by
      simp [rootTransitionCount]
    omega

/-- Nonnegative additive weight required by the REAL existing tie-score
interface. The cast is of the already defined native transition step. -/
noncomputable def rootTransitionWeight (u v : V) : ℝ≥0 :=
  (T.rootTransitionStep u v : ℝ≥0)

theorem rootTransitionWeight_sum {b W : V} (q : DWalk b W) :
    (q.darts.map (fun d => (T.rootTransitionWeight d.fst d.snd : ℝ))).sum=
      (T.rootTransitionCount q : ℝ) := by
  induction q with
  | nil => simp [rootTransitionCount]
  | @cons b u W h q ih =>
    calc
      ((Walk.cons h q).darts.map
          (fun d => (T.rootTransitionWeight d.fst d.snd : ℝ))).sum
          = (T.rootTransitionStep b u : ℝ)+
            (q.darts.map (fun d => (T.rootTransitionWeight d.fst d.snd : ℝ))).sum := by
              simp [rootTransitionWeight]
      _ = (T.rootTransitionStep b u : ℝ)+(T.rootTransitionCount q : ℝ) := by rw [ih]
      _ = (T.rootTransitionCount (.cons h q) : ℝ) := by simp [rootTransitionCount]

/-- The graph, transition weight and native secondary edge-code rule are
fixed globally. The only availability input is a genuine route in this
ROOT-filtered graph. No owner/guard-specific favorable tie is selected. -/
noncomputable def rootCanonicalSuffix (H : Finset (V × V)) (root b W : V)
    (hr : Reachable (T.graph H root) b W) : DWalk b W :=
  Classical.choose (exists_optimal (K := (⊤ : SimpleGraph V))
    (T.graph H root) T.rootTransitionWeight b W hr)

theorem rootCanonicalSuffix_optimal (H : Finset (V × V)) (root b W : V)
    (hr : Reachable (T.graph H root) b W) :
    Optimal (T.graph H root) T.rootTransitionWeight
      (T.rootCanonicalSuffix H root b W hr) :=
  Classical.choose_spec (exists_optimal (K := (⊤ : SimpleGraph V))
    (T.graph H root) T.rootTransitionWeight b W hr)

/-- At the literal endpoint the system chooses nil, including zero-cost
ties. This follows from the native optimal path property, not a positive
transition or nonempty suffix hypothesis. -/
theorem rootCanonicalSuffix_self (H : Finset (V × V)) (root W : V)
    (hr : Reachable (T.graph H root) W W) :
    T.rootCanonicalSuffix H root W W hr=(.nil : DWalk W W) := by
  simpa using (Walk.isPath_iff_nil.mp
    (T.rootCanonicalSuffix_optimal H root W W hr).2.1)

/-- The primary tie score truly minimizes NATIVE chain count in the actual
root-reachable domain. The initial covered/uncovered marker is constant
between competitors; no native own-b distance is substituted. -/
theorem rootCanonicalSuffix_native_minimum {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W : V}
    (hrootb : Reachable T.G root b)
    (hr : Reachable (T.graph H root) b W) :
    T.FixedRootSuffixMinimum H root (T.rootCanonicalSuffix H root b W hr) := by
  have ho := T.rootCanonicalSuffix_optimal H root b W hr
  refine ⟨ho.1,?_⟩
  intro r hrr
  have hscore := ho.shortest r hrr
  rw [T.rootTransitionWeight_sum,T.rootTransitionWeight_sum] at hscore
  have hsteps : T.rootTransitionCount (T.rootCanonicalSuffix H root b W hr)≤
      T.rootTransitionCount r := by exact_mod_cast hscore
  have hc := T.fixed_root_count_eq_marker_transitions hH
    (T.rootCanonicalSuffix H root b W hr) hrootb ho.1
  have hrc := T.fixed_root_count_eq_marker_transitions hH r hrootb hrr
  omega

/-- Literal consistency, not merely equal price. The existing native
Optimal.subwalk and Optimal.unique use the SAME fixed additive primary
weight and secondary score for all endpoints. -/
theorem rootCanonicalSuffix_subwalk (H : Finset (V × V)) (root : V)
    {b W u v : V} (hr : Reachable (T.graph H root) b W)
    {q : DWalk u v} (hq : q.IsSubwalk (T.rootCanonicalSuffix H root b W hr)) :
    ∃ hq' : Reachable (T.graph H root) u v,
      q=T.rootCanonicalSuffix H root u v hq' := by
  have ho := (T.rootCanonicalSuffix_optimal H root b W hr).subwalk hq
  exact ⟨⟨q,ho.1⟩,ho.unique
    (T.rootCanonicalSuffix_optimal H root u v ⟨q,ho.1⟩)⟩

/-- A later shared physical vertex has exactly the globally chosen suffix.
Availability at that vertex is supplied by the actual literal subwalk. -/
theorem rootCanonicalSuffix_dropUntil (H : Finset (V × V)) (root : V)
    {b W v : V} (hr : Reachable (T.graph H root) b W)
    (hv : v ∈ (T.rootCanonicalSuffix H root b W hr).support) :
    ∃ hvW : Reachable (T.graph H root) v W,
      (T.rootCanonicalSuffix H root b W hr).dropUntil v hv=
        T.rootCanonicalSuffix H root v W hvW := by
  exact T.rootCanonicalSuffix_subwalk H root hr
    ((T.rootCanonicalSuffix H root b W hr).isSubwalk_dropUntil hv)

/-- Any route-existence proofs select the same literal path, since the
native score has a unique optimal path. -/
theorem rootCanonicalSuffix_proof_irrel (H : Finset (V × V)) (root b W : V)
    (h₁ h₂ : Reachable (T.graph H root) b W) :
    T.rootCanonicalSuffix H root b W h₁=T.rootCanonicalSuffix H root b W h₂ := by
  exact (T.rootCanonicalSuffix_optimal H root b W h₁).unique
    (T.rootCanonicalSuffix_optimal H root b W h₂)

/-- A later vertex of an actual eligible canonical path remains in the
genuine original-root-reachable domain. Its literal suffix is the global
choice there AND is minimum for the same native primary chain count. -/
theorem rootCanonicalSuffix_later_minimum {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W v : V}
    (hrootb : Reachable T.G root b)
    (hr : Reachable (T.graph H root) b W)
    (hv : v ∈ (T.rootCanonicalSuffix H root b W hr).support) :
    ∃ hvW : Reachable (T.graph H root) v W,
      Reachable T.G root v ∧
      (T.rootCanonicalSuffix H root b W hr).dropUntil v hv=
        T.rootCanonicalSuffix H root v W hvW ∧
      T.FixedRootSuffixMinimum H root (T.rootCanonicalSuffix H root v W hvW) := by
  have hp := (T.rootCanonicalSuffix_optimal H root b W hr).1
  have hbv : Reachable T.G b v :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨(T.rootCanonicalSuffix H root b W hr).takeUntil v hv,
        allowed_mono (fun _ _ h => h.1)
          (allowed_subwalk hp
            ((T.rootCanonicalSuffix H root b W hr).isSubwalk_takeUntil hv))⟩
  have hrootv := reachable_trans hrootb hbv
  obtain ⟨hvW,heq⟩ := T.rootCanonicalSuffix_dropUntil H root hr hv
  exact ⟨hvW,hrootv,heq,T.rootCanonicalSuffix_native_minimum hH hrootv hvW⟩

/-- Two genuinely chosen ROOT suffixes that meet at a physical vertex have
the SAME literal remaining walk. No set/cardinality or owner conclusion is
inferred from this compatibility statement. -/
theorem rootCanonicalSuffix_shared_vertex (H : Finset (V × V)) (root : V)
    {b₁ b₂ W v : V}
    (h₁ : Reachable (T.graph H root) b₁ W)
    (h₂ : Reachable (T.graph H root) b₂ W)
    (hv₁ : v ∈ (T.rootCanonicalSuffix H root b₁ W h₁).support)
    (hv₂ : v ∈ (T.rootCanonicalSuffix H root b₂ W h₂).support) :
    (T.rootCanonicalSuffix H root b₁ W h₁).dropUntil v hv₁=
      (T.rootCanonicalSuffix H root b₂ W h₂).dropUntil v hv₂ := by
  obtain ⟨hvW₁,he₁⟩ := T.rootCanonicalSuffix_dropUntil H root h₁ hv₁
  obtain ⟨hvW₂,he₂⟩ := T.rootCanonicalSuffix_dropUntil H root h₂ hv₂
  rw [he₁,he₂]

/-- The genuinely coalescing choice is passed to the ALREADY proved
explicit same-owner splice. Original Q and physical LAST entry/prefix are
kept; the new admitted equal-price walk is displayed separately. -/
theorem ownerLastRootTail_coalescing_replacement {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root x W : V}
    (hx : (root,x) ∈ T.important) {Q : DWalk x W}
    (F : T.OwnerLastRootTail H root x W Q)
    (hmin : T.count Q=T.distance H x W) :
    let r := T.rootCanonicalSuffix H root F.entry W ⟨F.tail,F.rootTail⟩
    Allowed (T.graph H x) r ∧
      Allowed (T.graph H x) (F.prefix.append r) ∧
      T.count r=T.count F.tail ∧
      T.count (F.prefix.append r)=T.distance H x W ∧
      F.tau+1=T.count r ∧
      (Allowed (T.graph H root) (F.prefix.append r) ↔
        Allowed (T.graph H root) Q) := by
  have hxb : Reachable T.G x F.entry :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨F.prefix,allowed_mono (fun _ _ h => h.1) F.ownPrefix⟩
  have hrootb := reachable_trans (T.important_spec hx).1 hxb
  exact T.ownerLastRootTail_replace_fixed_root hH hx F hmin _
    (T.rootCanonicalSuffix_native_minimum hH hrootb ⟨F.tail,F.rootTail⟩)

end GreedyShortcuts.ChainDistance.Context
