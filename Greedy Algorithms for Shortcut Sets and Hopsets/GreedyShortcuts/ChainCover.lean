import GreedyShortcuts.ChainSubwalk
import GreedyShortcuts.DirectedLift

/-! Chain-cover guarantees survive legal shortcut insertion: expand every
shortcut into an original walk, retaining all of the shortcut walk's vertices.
Acyclicity makes the expansion an original simple path. -/
namespace GreedyShortcuts.ChainCover

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainUnion ChainFirst
open ChainNormalization ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Expansion retains the vertices of the supplied walk, rather than merely
proving its endpoints reachable. -/
theorem expand_support {G J : V → V → Prop}
    (hJ : ∀ u v,J u v → Reachable G u v) {s t : V}
    (p : DWalk s t) (hp : Allowed J p) :
    ∃ q : DWalk s t,Allowed G q ∧ p.support.toFinset ⊆ q.support.toFinset := by
  induction p with
  | nil => exact ⟨.nil,allowed_nil G _,Finset.Subset.refl _⟩
  | @cons s u t ha p ih =>
    have hh := (allowed_cons J ha p).mp hp
    obtain ⟨a,ha⟩ := hJ s u hh.1
    obtain ⟨b,hb,hsub⟩ := ih hh.2
    refine ⟨a.append b,(allowed_append G a b).mpr ⟨ha,hb⟩,?_⟩
    intro v hv
    simp only [Walk.support_cons,List.toFinset_cons,Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact List.mem_toFinset.mpr (Walk.start_mem_support _)
    · have hm := List.mem_toFinset.mp (hsub hv)
      exact List.mem_toFinset.mpr ((Walk.mem_support_append_iff a b).mpr (Or.inr hm))

/-- A walk either contains no covered vertex, or has a covered vertex after
which every remaining vertex is uncovered. The selected suffix is genuine. -/
theorem last_covered (color : V → Option I) {s t : V} (p : DWalk s t) :
    (∀ v ∈ p.support,color v = none) ∨
      ∃ u c,∃ q : DWalk u t,color u = some c ∧ q.IsSubwalk p ∧
        ∀ v ∈ q.support.tail,color v = none := by
  induction p with
  | @nil u =>
    cases hc : color u with
    | none => exact Or.inl (by simpa using hc)
    | some c => exact Or.inr ⟨u,c,.nil,hc,Walk.isSubwalk_rfl _,by simp⟩
  | @cons s u t ha p ih =>
    rcases ih with hnone | ⟨v,c,q,hvc,hqp,hq⟩
    · cases hc : color s with
      | none => exact Or.inl (by simpa [hc] using hnone)
      | some c => exact Or.inr ⟨s,c,.cons ha p,hc,Walk.isSubwalk_rfl _,by simpa using hnone⟩
    · exact Or.inr ⟨v,c,q,hvc,hqp.cons ha,hq⟩

noncomputable def uncovered (T : ChainDistance.Context V I) {s t : V} (p : DWalk s t) :
    Finset V := p.support.toFinset.filter (fun v => label T.chains v = none)

/-- The source's chain-cover condition, with an explicit finite uncovered
vertex budget. Improved cover construction is a separate cited input. -/
def IsCover (T : ChainDistance.Context V I) (U : ℕ) : Prop :=
  ∀ s t (p : DWalk s t),Allowed T.G p → p.IsPath → (uncovered T p).card ≤ U

variable (T : ChainDistance.Context V I)

theorem uncovered_le_of_legal {U : ℕ} (hcover : IsCover T U)
    {H : Finset (V × V)} (hH : H ⊆ candidates T.G) {s t : V}
    (p : DWalk s t) (hp : Allowed (augment T.G (T.base ∪ H)) p) :
    (uncovered T p).card ≤ U := by
  classical
  obtain ⟨q,hq,hsub⟩ := expand_support (G:=T.G)
    (fun u v h => (reachable_augment_iff T.G _ (T.augmentation_legal hH) u v).mp
      (reachable_edge h)) p hp
  apply (Finset.card_le_card ?_).trans (hcover s t q hq
    (ChainDistance.Context.allowed_isPath T.acyclic q hq))
  intro v hv
  have hh := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hsub hh.1,hh.2⟩

/-- Extract an ordinary original-graph suffix of at most the cover budget
from some reachable covered vertex, unless the whole demand is already short. -/
theorem covered_tail {U : ℕ} (hcover : IsCover T U) {s t : V}
    (hr : Reachable T.G s t) :
    (∃ p : DWalk s t,Allowed T.G p ∧ p.length ≤ U) ∨
      ∃ v c,Reachable T.G s v ∧ label T.chains v = some c ∧
        ∃ q : DWalk v t,Allowed T.G q ∧ q.length ≤ U := by
  classical
  let p := canonical T.G s t hr
  have hp := canonical_optimal T.G s t hr
  have hU := hcover s t p hp.1 hp.2.1
  rcases last_covered (label T.chains) p with hn | ⟨v,c,q,hvc,hqp,hq⟩
  · left
    have he : uncovered T p = p.support.toFinset := by
      apply Finset.filter_true_of_mem
      intro v hv
      exact hn v (List.mem_toFinset.mp hv)
    have hlen : p.support.toFinset.card = p.length+1 := by
      rw [List.toFinset_card_of_nodup hp.2.1.support_nodup,Walk.length_support]
    exact ⟨p,hp.1,by rw [he,hlen] at hU;omega⟩
  · right
    have hqG := allowed_subwalk hp.1 hqp
    have hqpath := ChainDistance.Context.allowed_isPath T.acyclic q hqG
    have hqsub := (Walk.isSubwalk_iff_support_isInfix.mp hqp).subset
    have hvp := hqsub q.start_mem_support
    have hreach : Reachable T.G s v :=
      ⟨p.takeUntil v hvp,allowed_subwalk hp.1 (p.isSubwalk_takeUntil hvp)⟩
    refine ⟨v,c,hreach,hvc,q,hqG,?_⟩
    have hsub : q.support.tail.toFinset ⊆ uncovered T p := by
      intro x hx
      have hx' := List.mem_toFinset.mp hx
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hqsub (List.mem_of_mem_tail hx')),hq x hx'⟩
    have hcard : q.support.tail.toFinset.card = q.length := by
      rw [List.toFinset_card_of_nodup hqpath.support_nodup.tail,List.length_tail,Walk.length_support]
      omega
    rw [← hcard]
    exact (Finset.card_le_card hsub).trans hU

/-- Every forward same-chain pair admits an actual at-most-four-hop walk,
all of whose vertices stay on that chain. -/
theorem internal_short {H : Finset (V × V)} (_hH : H ⊆ candidates T.G)
    {u v : V} (hr : Reachable T.G u v) {c : I}
    (hu : label T.chains u = some c) (hv : label T.chains v = some c) :
    ∃ p : DWalk u v,Allowed (augment T.G (T.base ∪ H)) p ∧ p.length ≤ 4 ∧
      ∀ x ∈ p.support,label T.chains x = some c := by
  classical
  obtain ⟨i,hi,hiu⟩ := Finset.mem_image.mp (mem_of_label T.chains hu)
  obtain ⟨j,hj,hjv⟩ := Finset.mem_image.mp (mem_of_label T.chains hv)
  have hij := index_le_of_reachable T.acyclic (T.chains c) i j
    (by simpa only [hiu,hjv] using hr)
  subst u
  subst v
  obtain ⟨p,hp,hp4⟩ := (T.witnesses c).short i j hij
  let q := p.map (DirectedMap.hom (T.chains c).node (T.chains c).injective)
  refine ⟨q,?_,?_,?_⟩
  · exact DirectedMap.allowed_map (T.chains c).node (T.chains c).injective
      (fun a b hab => Or.inr (Finset.mem_union_left H
        (local_subset T.chains T.witnesses c (DirectedMap.mem_edges _ _ hab)))) p hp
  · simpa [q,DirectedMap.hom] using hp4
  · intro x hx
    change x ∈ (p.map (DirectedMap.hom (T.chains c).node (T.chains c).injective)).support at hx
    rw [Walk.support_map] at hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact label_node T.chains T.disjoint c a

end GreedyShortcuts.ChainCover
