import GreedyShortcuts.ChainProjectedConeOwners
import GreedyShortcuts.ChainPrefixSavings

/-! SOURCE ONLY, UNCOMPILED. First native maximum-core selector primitives
in the SAME root cone and fixed H. Relay/guard geometry is derived from
actual reachability; the full minimum-tail mode decision is not formalized. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Exactly the source selector's finite rank-maximizer relation. No owner,
band, stopping, filter-transfer or forcing conclusion is a field. -/
def RootConeMaximizer (H : Finset (V × V)) (root A U : V) : Prop :=
  U ∈ T.rootHeadCone root A ∧
    ∀ v ∈ T.rootHeadCone root A,T.distance H root v ≤ T.distance H root U

theorem rootCone_self_mem {root A : V} (hA : (root,A) ∈ T.important) :
    A ∈ T.rootHeadCone root A :=
  T.mem_rootHeadCone_iff.mpr ⟨hA,reachable_refl T.G A,T.important_covered hA⟩

/-- Construction uses the ACTUAL finite cone and actual fixed-root distance.
Every maximum tie remains permitted by the relation. -/
theorem exists_rootConeMaximizer (H : Finset (V × V)) {root A : V}
    (hA : (root,A) ∈ T.important) :
    ∃ U,T.RootConeMaximizer H root A U := by
  classical
  obtain ⟨U,hU,hmax⟩ := Finset.exists_max_image (T.rootHeadCone root A)
    (fun v => T.distance H root v) ⟨A,T.rootCone_self_mem hA⟩
  exact ⟨U,hU,hmax⟩

/-- ANY actual maximizer normalizes its OWN retained cone. Nesting and the
candidate-rank floor are consequences, not assumed selector fields. -/
theorem rootConeMaximizer_normalizes {H : Finset (V × V)} {root A U : V}
    (hA : (root,A) ∈ T.important) (hU : T.RootConeMaximizer H root A U) :
    (root,U) ∈ T.important ∧ Reachable T.G U A ∧
      T.rootHeadCone root U ⊆ T.rootHeadCone root A ∧
      T.RootConeMaximizer H root U U ∧
      T.distance H root A ≤ T.distance H root U := by
  obtain ⟨hUm,hmax⟩ := hU
  obtain ⟨hip,hUA,_hc⟩ := T.mem_rootHeadCone_iff.mp hUm
  have hsub := T.rootHeadCone_mono (root := root) hUA
  have hnorm : T.RootConeMaximizer H root U U :=
    ⟨T.rootCone_self_mem hip,fun v hv => hmax v (hsub hv)⟩
  exact ⟨hip,hUA,hsub,hnorm,hmax A (T.rootCone_self_mem hA)⟩

/-- A real original separator makes the maximum child PROPER. x's parent
membership and removal witness are derived from its actual head/reachability
certificates, not supplied as desired owner conclusions. Zero rank drop
is permitted despite strict cone/cardinality decrease. -/
theorem rootCone_child_of_separator {H : Finset (V × V)} {root W A U x : V}
    (hW : T.RootConeMaximizer H root W W)
    (hA : (root,A) ∈ T.important) (hAW : Reachable T.G A W)
    (hx : (root,x) ∈ T.important) (hxW : Reachable T.G x W)
    (hxA : ¬ Reachable T.G x A) (hU : T.RootConeMaximizer H root A U) :
    (root,U) ∈ T.important ∧ Reachable T.G U A ∧ Reachable T.G U W ∧
      T.RootConeMaximizer H root U U ∧
      T.rootHeadCone root U ⊆ T.rootHeadCone root W ∧
      x ∈ T.rootHeadCone root W \ T.rootHeadCone root U ∧
      (T.rootHeadCone root U).card < (T.rootHeadCone root W).card ∧
      T.distance H root A ≤ T.distance H root U ∧
      T.distance H root U ≤ T.distance H root W := by
  classical
  obtain ⟨hip,hUA,_hsubA,hnorm,hfloor⟩ := T.rootConeMaximizer_normalizes hA hU
  have hUW := reachable_trans hUA hAW
  have hsub := T.rootHeadCone_mono (root := root) hUW
  have hxparent : x ∈ T.rootHeadCone root W :=
    T.mem_rootHeadCone_iff.mpr ⟨hx,hxW,T.important_covered hx⟩
  have hxnot : x ∉ T.rootHeadCone root U := by
    intro hh
    exact hxA (reachable_trans (T.mem_rootHeadCone_iff.mp hh).2.1 hUA)
  have hcard : (T.rootHeadCone root U).card < (T.rootHeadCone root W).card := by
    apply Finset.card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun he => hxnot (he.symm ▸ hxparent)⟩
  have hUparent : U ∈ T.rootHeadCone root W :=
    (T.rootHeadCone_mono hAW) hU.1
  exact ⟨hip,hUA,hUW,hnorm,hsub,Finset.mem_sdiff.mpr ⟨hxparent,hxnot⟩,
    hcard,hfloor,hW.2 U hUparent⟩

/-- Guard-local construction from the SAME selected own-x minimum that is
actually ROOT-invalid. Native incompatible_guard constructs a real guard
from that path. This does NOT implement the minimum-tail relay/guard test.
The exported price uses the WHOLE own-x minimum, not an invented tail cost. -/
theorem exists_invalid_path_guard_maximum {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root x W : V}
    (hW : T.RootConeMaximizer H root W W) (hx : (root,x) ∈ T.important)
    (Q : DWalk x W) (hQ : Allowed (T.graph H x) Q)
    (hmin : T.count Q=T.distance H x W)
    (hbad : ¬ Allowed (T.graph H root) Q) :
    ∃ g U,(root,g) ∈ T.important ∧ Reachable T.G g W ∧
      ¬ Reachable T.G x g ∧
      T.distance H root W+1 ≤ T.distance H root g+T.distance H x W ∧
      T.RootConeMaximizer H root g U ∧ (root,U) ∈ T.important ∧
      Reachable T.G U g ∧ Reachable T.G U W ∧
      T.RootConeMaximizer H root U U ∧
      T.rootHeadCone root U ⊆ T.rootHeadCone root W ∧
      x ∈ T.rootHeadCone root W \ T.rootHeadCone root U ∧
      (T.rootHeadCone root U).card < (T.rootHeadCone root W).card ∧
      T.distance H root g ≤ T.distance H root U ∧
      T.distance H root U ≤ T.distance H root W := by
  have hxW : Reachable T.G x W :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨Q,allowed_mono (fun _ _ h => h.1) hQ⟩
  obtain ⟨g,hg,_hrootg,hgW,hxg,hgap⟩ :=
    T.incompatible_guard hH (T.important_spec hx).1 Q hQ hbad
  obtain ⟨U,hU⟩ := T.exists_rootConeMaximizer H hg
  obtain ⟨hip,hUg,hUW,hnorm,hsub,hremoved,hcard,hfloor,hupper⟩ :=
    T.rootCone_child_of_separator hW hg hgW hx hxW hxg hU
  have hprice : T.distance H root W+1 ≤
      T.distance H root g+T.distance H x W := by simpa only [hmin] using hgap
  exact ⟨g,U,hg,hgW,hxg,hprice,hU,hip,hUg,hUW,hnorm,hsub,hremoved,hcard,hfloor,hupper⟩

/-- Relay-local geometry for ANY actual maximum owner in the anchor cone.
The anchor is a genuine earlier global head, not a replacement cone chosen
to improve a bound. The mode's minimum-tail comparison remains external. -/
theorem relay_maximum_from_anchor {H : Finset (V × V)} {root W a U : V}
    (hW : T.RootConeMaximizer H root W W)
    (ha : (root,a) ∈ T.important) (haW : Reachable T.G a W) (hne : a≠W)
    (hU : T.RootConeMaximizer H root a U) :
    T.RootConeMaximizer H root U U ∧
      T.rootHeadCone root U ⊆ T.rootHeadCone root W ∧
      W ∈ T.rootHeadCone root W \ T.rootHeadCone root U ∧
      (T.rootHeadCone root U).card < (T.rootHeadCone root W).card ∧
      T.distance H root a ≤ T.distance H root U ∧
      T.distance H root U ≤ T.distance H root W := by
  have hWa : ¬ Reachable T.G W a := by
    intro hback
    exact hne ((CanonicalSegments.acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ haW hback)
  have hrootW := (T.mem_rootHeadCone_iff.mp hW.1).1
  obtain ⟨_hip,_hUa,_hUW,hnorm,hsub,hremoved,hcard,hfloor,hupper⟩ :=
    T.rootCone_child_of_separator hW ha haW hrootW (reachable_refl T.G W) hWa hU
  exact ⟨hnorm,hsub,hremoved,hcard,hfloor,hupper⟩

/-- The actual stopping comparison on the constructed endpoint. A terminal
child is accepted below q, not required to furnish another active band.
Only the REAL candidate's rank floor is asserted. -/
theorem rootConeMaximizer_stop_cases {H : Finset (V × V)} {root A U : V}
    (hA : (root,A) ∈ T.important) (hU : T.RootConeMaximizer H root A U) (q : ℕ) :
    q ≤ T.distance H root U ∨
      (T.distance H root A ≤ T.distance H root U ∧ T.distance H root U<q) := by
  have hfloor := (T.rootConeMaximizer_normalizes hA hU).2.2.2.2
  by_cases hactive : q ≤ T.distance H root U
  · exact Or.inl hactive
  · exact Or.inr ⟨hfloor,Nat.lt_of_not_ge hactive⟩

/-- Among original descendants of the relay anchor, the actual child can
retain only the anchor, and only when the selected maximum IS that anchor.
This preserves the true terminal-anchor exception without assuming a band. -/
theorem relay_descendant_retained_iff {H : Finset (V × V)} {root a U b : V}
    (ha : (root,a) ∈ T.important) (hU : T.RootConeMaximizer H root a U)
    (hab : Reachable T.G a b) :
    b ∈ T.rootHeadCone root U ↔ b=a ∧ U=a := by
  have hUa := (T.mem_rootHeadCone_iff.mp hU.1).2.1
  constructor
  · intro hb
    have hbU := (T.mem_rootHeadCone_iff.mp hb).2.1
    have hba := reachable_trans hbU hUa
    have hbeq : b=a :=
      (CanonicalSegments.acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hba hab
    have hUeq : U=a :=
      (CanonicalSegments.acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hUa (reachable_trans hab hbU)
    exact ⟨hbeq,hUeq⟩
  · rintro ⟨rfl,rfl⟩
    exact T.rootCone_self_mem ha

end GreedyShortcuts.ChainDistance.Context
