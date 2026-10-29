import GreedyShortcuts.ChainStrictJoinGuardV2
import GreedyShortcuts.ChainEntries

/-! SOURCE ONLY, UNCOMPILED. Extract the competing tail from the unchanged
selected own-source minimum at an actual shared vertex. Only forward
validity, not source-rebased minimum optimality, is used. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- The literal take/drop split has its actual original-source prefix price
and exact covered/uncovered join marker. The rebased suffix is admitted,
and its own-start distance is only bounded ABOVE by its count. -/
theorem selected_pivot_suffix_prices_v2 {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {h w t : V}
    (Q : DWalk h t) (hQ : Allowed (T.graph H h) Q)
    (hmin : T.count Q=T.distance H h t) (hw : w ∈ Q.support) :
    Reachable T.G h w ∧ Reachable T.G w t ∧
      Allowed (T.graph H h) (Q.takeUntil w hw) ∧
      Allowed (T.graph H h) (Q.dropUntil w hw) ∧
      Allowed (T.graph H w) (Q.dropUntil w hw) ∧
      T.count (Q.takeUntil w hw)=T.distance H h w ∧
      T.distance H h t+(label T.chains w).toFinset.card=
        T.distance H h w+T.count (Q.dropUntil w hw) ∧
      T.distance H w t ≤ T.count (Q.dropUntil w hw) := by
  have hsplit : Allowed (T.graph H h)
      ((Q.takeUntil w hw).append (Q.dropUntil w hw)) := by
    simpa only [Q.take_spec hw] using hQ
  obtain ⟨hpre,hsuf⟩ := (allowed_append _ _ _).mp hsplit
  have hhw : Reachable T.G h w :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨Q.takeUntil w hw,allowed_mono (fun _ _ h => h.1) hpre⟩
  have hwt : Reachable T.G w t :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨Q.dropUntil w hw,allowed_mono (fun _ _ h => h.1) hsuf⟩
  have hsufw := T.allowed_rebase hH hhw (Q.dropUntil w hw) hsuf
  have hprefix := T.minimum_takeUntil hH Q hQ hmin hw
  have hj := T.count_append_exact hH (Q.takeUntil w hw) (Q.dropUntil w hw) hsplit
  have hjoin : T.distance H h t+(label T.chains w).toFinset.card=
      T.distance H h w+T.count (Q.dropUntil w hw) := by
    simpa only [Q.take_spec hw,hmin,hprefix] using hj
  exact ⟨hhw,hwt,hpre,hsuf,hsufw,hprefix,hjoin,
    T.distance_le_walk H hwt (Q.dropUntil w hw) hsufw⟩

/-- A genuine S-reference and the unchanged selected h-minimum share w.
The residual price premise uses sums, so it preserves the exact positive
threshold without truncated subtraction. It does not assume S reaches h.
The SAME guard/repair witnesses give off-reference important entries. -/
theorem selected_shared_pivot_last_guard_offpath_v2 {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {s h w v t : V}
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
        T.count (Q.dropUntil w hw)+1=
          T.count (l.append (.cons edge .nil))+T.count r ∧
        (label T.chains w).toFinset.card+1 ≤ T.count (l.append (.cons edge .nil)) ∧
        T.distance H s t+1 ≤ T.distance H s z+T.count r ∧
        T.count p+delta+1 ≤ T.distance H s z ∧
        delta+1 ≤ (T.chainSet repair \ T.chainSet (p.append reference)).card ∧
        delta+1 ≤ (T.offPathEntries repair (p.append reference)).card ∧
        ∀ e ∈ T.offPathEntries repair (p.append reference),
          e ∈ repair.support ∧ e ∉ (p.append reference).support ∧
          (s,e) ∈ T.important := by
  classical
  obtain ⟨hhw,hwt,_hpre,_hsuf,hsufw,hprefix,hjoin,_hownprice⟩ :=
    T.selected_pivot_suffix_prices_v2 hH Q hQ hmin hw
  have hcheap : T.count p+T.count (Q.dropUntil w hw)+delta ≤
      T.distance H s t+(label T.chains w).toFinset.card := by omega
  obtain ⟨a,b,edge,l,r,z,repair,hform,hl,hab,hnb,hrs,hcovered,hfirst,hnfirst,
      hz,hpair,hzt,hnwz,hrepair,hrepairCount,hsplit,hprefixLower,hprice,
      hguardPrice,hsupply⟩ :=
    T.strict_join_last_guard_offpath_v2 hH p reference hpref
      (Q.dropUntil w hw) hsufw ht hdelta hcheap
  have hentries : delta+1 ≤ (T.offPathEntries repair (p.append reference)).card :=
    hsupply.trans (T.offPathEntries_card hH repair (p.append reference) hrepair)
  have hspec : ∀ e ∈ T.offPathEntries repair (p.append reference),
      e ∈ repair.support ∧ e ∉ (p.append reference).support ∧
      (s,e) ∈ T.important := by
    intro e he
    exact T.offPathEntries_spec hH repair (p.append reference) hrepair he
  exact ⟨hhw,hwt,hprefix,hjoin,hsufw,a,b,edge,l,r,z,repair,
    hform,hl,hab,hnb,hrs,hcovered,hfirst,hnfirst,hz,hpair,hzt,hnwz,
    hrepair,hrepairCount,hsplit,hprefixLower,hprice,hguardPrice,hsupply,hentries,hspec⟩

end GreedyShortcuts.ChainDistance.Context
