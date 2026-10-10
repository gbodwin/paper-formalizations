import GreedyShortcuts.ChainHopCompression

/-! Actual chain-set accounting for spliced native walks. These finite-set
identities require no hereditary optimality of normalized distances. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ChainCover ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem mem_chainSet {s t : V} (p : DWalk s t) (c : I) :
    c ∈ T.chainSet p ↔ ∃ v ∈ p.support,label T.chains v = some c := by
  classical
  simp [chainSet]

theorem chainSet_append {s u t : V} (p : DWalk s u) (q : DWalk u t) :
    T.chainSet (p.append q) = T.chainSet p ∪ T.chainSet q := by
  classical
  ext c
  simp only [T.mem_chainSet,Walk.mem_support_append_iff,Finset.mem_union]
  aesop

theorem count_append_le {s u t : V} (p : DWalk s u) (q : DWalk u t) :
    T.count (p.append q) ≤ T.count p+T.count q := by
  unfold count
  rw [T.chainSet_append]
  exact Finset.card_union_le _ _

theorem chainSet_subwalk {s t u v : V} {p : DWalk s t} {q : DWalk u v}
    (hqp : q.IsSubwalk p) : T.chainSet q ⊆ T.chainSet p := by
  intro c hc
  obtain ⟨x,hx,hxc⟩ := (T.mem_chainSet q c).mp hc
  exact (T.mem_chainSet p c).mpr ⟨x,(Walk.isSubwalk_iff_support_isInfix.mp hqp).subset hx,hxc⟩

theorem count_subwalk {s t u v : V} {p : DWalk s t} {q : DWalk u v}
    (hqp : q.IsSubwalk p) : T.count q ≤ T.count p := Finset.card_le_card (T.chainSet_subwalk hqp)

theorem count_append_covered {s u t : V} (p : DWalk s u) (q : DWalk u t)
    {c : I} (hc : label T.chains u = some c) :
    T.count (p.append q)+1 ≤ T.count p+T.count q := by
  classical
  have hp : c ∈ T.chainSet p := (T.mem_chainSet p c).mpr ⟨u,p.end_mem_support,hc⟩
  have hq : c ∈ T.chainSet q := (T.mem_chainSet q c).mpr ⟨u,q.start_mem_support,hc⟩
  have hcard : 1 ≤ (T.chainSet p ∩ T.chainSet q).card :=
    Finset.one_le_card.mpr ⟨c,Finset.mem_inter.mpr ⟨hp,hq⟩⟩
  have he := Finset.card_union_add_card_inter (T.chainSet p) (T.chainSet q)
  unfold count
  rw [T.chainSet_append]
  omega

theorem chainSet_single_color {s t : V} (p : DWalk s t) {c : I}
    (hp : ∀ v ∈ p.support,label T.chains v = some c) : T.chainSet p = {c} := by
  classical
  ext d
  rw [T.mem_chainSet]
  constructor
  · rintro ⟨v,hv,hd⟩
    have he : c = d := Option.some.inj ((hp v hv).symm.trans hd)
    simpa [he]
  · intro hd
    have he : d = c := Finset.mem_singleton.mp hd
    subst d
    exact ⟨s,p.start_mem_support,hp s p.start_mem_support⟩

theorem count_append_internal {s u v : V} (p : DWalk s u) (q : DWalk u v)
    {c : I} (hq : ∀ x ∈ q.support,label T.chains x = some c) :
    T.count (p.append q) = T.count p := by
  classical
  have hu : c ∈ T.chainSet p := (T.mem_chainSet p c).mpr
    ⟨u,p.end_mem_support,hq u q.start_mem_support⟩
  unfold count
  rw [T.chainSet_append,T.chainSet_single_color q hq,Finset.union_eq_left.mpr (by simpa using hu)]

theorem allowed_internal {H : Finset (V × V)} {s u v : V} (q : DWalk u v)
    (hq : Allowed (augment T.G (T.base ∪ H)) q) {c : I}
    (hc : ∀ x ∈ q.support,label T.chains x = some c) : Allowed (T.graph H s) q := by
  intro d hd
  exact ⟨hq d hd,Or.inl ((hc d.fst (q.dart_fst_mem_support_of_mem_darts hd)).trans
    (hc d.snd (q.dart_snd_mem_support_of_mem_darts hd)).symm)⟩

end GreedyShortcuts.ChainDistance.Context
