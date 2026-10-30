import GreedyShortcuts.ChainSharedPivotGuardV2
import GreedyShortcuts.ChainCertifiedRootProjection

/-! SOURCE ONLY, UNCOMPILED. The corrected V2 selected-pivot witness is
projected on the SAME repair/reference. Historical strict/shared modules
are not imports. No owner, rank, cross-row sum or new resource is claimed. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Genuine root-to-source reachability projects the existing delta+1
absent-chain bound from the actual corrected LAST witness. Source entries
and their potentially earlier root heads retain separate forward links. -/
theorem selected_shared_pivot_root_projection_v2 {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root s h w v t : V}
    (hroot : Reachable T.G root s)
    (p : DWalk s w) (reference : DWalk w v)
    (hpref : Allowed (T.graph H s) (p.append reference))
    (Q : DWalk h t) (hQ : Allowed (T.graph H h) Q)
    (hmin : T.count Q=T.distance H h t) (hw : w ∈ Q.support)
    (ht : (s,t) ∈ T.important) {delta : ℕ} (hdelta : 0<delta)
    (hresidual : T.count p+T.distance H h t+delta ≤
      T.distance H s t+T.distance H h w) :
    Reachable T.G h w ∧ Reachable T.G w t ∧
      T.count (Q.takeUntil w hw)=T.distance H h w ∧
      T.distance H h t+(label T.chains w).toFinset.card=
        T.distance H h w+T.count (Q.dropUntil w hw) ∧
      Allowed (T.graph H w) (Q.dropUntil w hw) ∧
      ∃ (a b : V) (edge : (⊤ : SimpleGraph V).Adj a b)
        (l : DWalk w a) (r : DWalk b t) (z : V) (repair : DWalk s z),
        Q.dropUntil w hw=l.append (.cons edge r) ∧
        Allowed (T.graph H w) l ∧ T.graph H w a b ∧ ¬ T.graph H s a b ∧
        Allowed (T.graph H s) r ∧ label T.chains b≠none ∧
        first T.chains w b=b ∧ first T.chains s b≠b ∧
        z=first T.chains s b ∧ (s,z) ∈ T.important ∧
        Reachable T.G z t ∧ ¬ Reachable T.G w z ∧
        Allowed (T.graph H s) repair ∧ T.count repair=T.distance H s z ∧
        T.count p+delta+1 ≤ T.distance H s z ∧
        delta+1 ≤ (T.chainSet repair \ T.chainSet (p.append reference)).card ∧
        (T.certifiedRootProjection root
          (T.chainSet repair \ T.chainSet (p.append reference))).card=
          (T.chainSet repair \ T.chainSet (p.append reference)).card ∧
        delta+1 ≤ (T.certifiedRootProjection root
          (T.chainSet repair \ T.chainSet (p.append reference))).card ∧
        Disjoint (T.certifiedRootProjection root
          (T.chainSet repair \ T.chainSet (p.append reference)))
          (T.certifiedRootProjection root (T.chainSet (p.append reference))) ∧
        ∀ head ∈ T.certifiedRootProjection root
            (T.chainSet repair \ T.chainSet (p.append reference)),
          ∃ c ∈ T.chainSet repair \ T.chainSet (p.append reference),
            head=entry T.chains root c ∧ label T.chains head=some c ∧
            Reachable T.G root head ∧ first T.chains root head=head ∧
            (root,head) ∈ T.important ∧ Reachable T.G head z ∧
            Reachable T.G head t ∧ head ∉ (p.append reference).support ∧
            ∃ e, e=entry T.chains s c ∧ e ∈ repair.support ∧
              e ∉ (p.append reference).support ∧ label T.chains e=some c ∧
              (s,e) ∈ T.important ∧ Reachable T.G head e ∧
              Reachable T.G e z ∧ Reachable T.G e t := by
  classical
  obtain ⟨hhw,hwt,hprefix,hjoin,hsufw,a,b,edge,l,r,z,repair,
      hform,hl,hab,hnb,hrs,hcovered,hfirst,hnfirst,hz,hpair,hzt,hnwz,
      hrepair,hrepairCount,_hsplit,_hprefixLower,_hprice,hguardPrice,
      hsupply,_hentryCount,_hentrySpec⟩ :=
    T.selected_shared_pivot_last_guard_offpath_v2 hH p reference hpref
      Q hQ hmin hw ht hdelta hresidual
  obtain ⟨hcard,hdisjoint,hprojectionSpec⟩ :=
    T.certifiedRootProjection_difference hH hroot repair hrepair
      (p.append reference) hpref
  have hrootCount : delta+1 ≤ (T.certifiedRootProjection root
      (T.chainSet repair \ T.chainSet (p.append reference))).card := by
    rw [hcard]
    exact hsupply
  have hspec : ∀ head ∈ T.certifiedRootProjection root
      (T.chainSet repair \ T.chainSet (p.append reference)),
      ∃ c ∈ T.chainSet repair \ T.chainSet (p.append reference),
        head=entry T.chains root c ∧ label T.chains head=some c ∧
        Reachable T.G root head ∧ first T.chains root head=head ∧
        (root,head) ∈ T.important ∧ Reachable T.G head z ∧
        Reachable T.G head t ∧ head ∉ (p.append reference).support ∧
        ∃ e, e=entry T.chains s c ∧ e ∈ repair.support ∧
          e ∉ (p.append reference).support ∧ label T.chains e=some c ∧
          (s,e) ∈ T.important ∧ Reachable T.G head e ∧
          Reachable T.G e z ∧ Reachable T.G e t := by
    intro head hh
    obtain ⟨c,hc,heq,hlabel,hrhead,hfirstRoot,hip,hheadz,hnref,
        e,heqEntry,heMem,heLabel,heImportant,hheadE,hez⟩ := hprojectionSpec head hh
    have hentryNotRef : e ∉ (p.append reference).support := by
      intro hm
      exact (Finset.mem_sdiff.mp hc).2
        ((T.mem_chainSet (p.append reference) c).mpr ⟨e,hm,heLabel⟩)
    exact ⟨c,hc,heq,hlabel,hrhead,hfirstRoot,hip,hheadz,
      reachable_trans hheadz hzt,hnref,e,heqEntry,heMem,hentryNotRef,
      heLabel,heImportant,hheadE,hez,reachable_trans hez hzt⟩
  exact ⟨hhw,hwt,hprefix,hjoin,hsufw,a,b,edge,l,r,z,repair,
    hform,hl,hab,hnb,hrs,hcovered,hfirst,hnfirst,hz,hpair,hzt,hnwz,
    hrepair,hrepairCount,hguardPrice,hsupply,hcard,hrootCount,hdisjoint,hspec⟩

end GreedyShortcuts.ChainDistance.Context
