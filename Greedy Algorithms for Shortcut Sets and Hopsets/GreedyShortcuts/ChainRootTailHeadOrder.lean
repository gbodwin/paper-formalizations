import GreedyShortcuts.ChainCoalescingRootSuffix
import GreedyShortcuts.ChainProjectedConeOwners

/-! SOURCE ONLY, UNCOMPILED. Actual covered labels of a ROOT-admitted
tail, their ROOT-first projections and their ordered physical occurrence
witnesses. No minimum is inherited after changing the source. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def rootTailHeads (root : V) {b W : V} (q : DWalk b W) : Finset V :=
  T.certifiedRootProjection root (T.chainSet q)

/-- A physical chain occurrence and its projection are deliberately
different vertices. The predicate asserts only actual literal data. -/
def RootTailHeadAt (root : V) {b W : V} (q : DWalk b W) (v : V) (i : ℕ) : Prop :=
  i≤q.length ∧ label T.chains (q.getVert i)≠none ∧ first T.chains root (q.getVert i)=v

theorem rootTailHeadAt_exists {root b W v : V} (q : DWalk b W)
    (hv : v ∈ T.rootTailHeads root q) : ∃ i,T.RootTailHeadAt root q v i := by
  classical
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨y,hy,hyc⟩ := (T.mem_chainSet q c).mp hc
  obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp hy
  refine ⟨i,hil,?_,?_⟩
  · rw [hi,hyc]
    simp
  · simp only [hi,first,hyc]

/-- The FIRST actual physical occurrence of this projected chain. This
does not replace the walk or choose a favorable minimum. -/
noncomputable def rootTailHeadPosition (root : V) {b W : V} (q : DWalk b W) (v : V) : ℕ := by
  classical
  exact if h : ∃ i,T.RootTailHeadAt root q v i then Nat.find h else 0

theorem rootTailHeadPosition_spec {root b W v : V} (q : DWalk b W)
    (hv : v ∈ T.rootTailHeads root q) :
    T.RootTailHeadAt root q v (T.rootTailHeadPosition root q v) := by
  classical
  have h := T.rootTailHeadAt_exists q hv
  simpa only [rootTailHeadPosition,dif_pos h] using Nat.find_spec h

theorem rootTailHeadPosition_le {root b W v : V} (q : DWalk b W) {i : ℕ}
    (hi : T.RootTailHeadAt root q v i) : T.rootTailHeadPosition root q v ≤ i := by
  classical
  have h : ∃ i,T.RootTailHeadAt root q v i := ⟨i,hi⟩
  simpa only [rootTailHeadPosition,dif_pos h] using Nat.find_min' h hi

theorem rootTailHeads_spec {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {root b W v : V} (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (hv : v ∈ T.rootTailHeads root q) :
    ∃ c ∈ T.chainSet q,v=entry T.chains root c ∧ label T.chains v=some c ∧
      Reachable T.G root v ∧ first T.chains root v=v ∧ (root,v) ∈ T.important ∧
      Reachable T.G v W ∧
      ∃ e,e=entry T.chains b c ∧ e ∈ q.support ∧ label T.chains e=some c ∧
        (b,e) ∈ T.important ∧ Reachable T.G v e ∧ Reachable T.G e W := by
  classical
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hl,hr,hf,hip,hW,he⟩ := T.root_projection_entry_on_walk hH hrootb q
    (T.allowed_rebase hH hrootb q hq) hc
  exact ⟨c,hc,rfl,hl,hr,hf,hip,hW,he⟩

theorem rootTailHeads_card {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {root b W : V} (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) : (T.rootTailHeads root q).card=T.count q := by
  exact T.certifiedRootProjection_card hH hrootb q (T.allowed_rebase hH hrootb q hq)
    (T.chainSet q) (Finset.Subset.refl _)

theorem rootTailHeadPosition_injective {root b W v w : V} (q : DWalk b W)
    (hv : v ∈ T.rootTailHeads root q) (hw : w ∈ T.rootTailHeads root q)
    (he : T.rootTailHeadPosition root q v=T.rootTailHeadPosition root q w) : v=w := by
  have hfv := (T.rootTailHeadPosition_spec q hv).2.2
  have hfw := (T.rootTailHeadPosition_spec q hw).2.2
  rw [he] at hfv
  exact hfv.symm.trans hfw

theorem rootTailHeadPosition_label {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {root b W v : V} (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (hv : v ∈ T.rootTailHeads root q) :
    label T.chains (q.getVert (T.rootTailHeadPosition root q v))=label T.chains v := by
  have hi := T.rootTailHeadPosition_spec q hv
  have hbi : Reachable T.G b (q.getVert (T.rootTailHeadPosition root q v)) :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨q.take _,allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk hq (q.isSubwalk_take _))⟩
  have hf := (first_spec T.chains T.disjoint root _ (reachable_trans hrootb hbi) hi.2.1).2.2
  rw [hi.2.2] at hf
  exact hf.symm

theorem rootTailHeads_label_injective {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {root b W v w : V} (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q)
    (hv : v ∈ T.rootTailHeads root q) (hw : w ∈ T.rootTailHeads root q)
    (he : label T.chains v=label T.chains w) : v=w := by
  obtain ⟨_c,_hc,_hv,_hl,_hr,hfv,_hip,_hW,_he⟩ := T.rootTailHeads_spec hH hrootb q hq hv
  obtain ⟨_d,_hd,_hw,_hm,_hs,hfw,_hjp,_hZ,_hf⟩ := T.rootTailHeads_spec hH hrootb q hq hw
  exact hfv.symm.trans ((first_constant T.chains root v w he).trans hfw)

/-- On a genuine ROOT-started reference, earliest ROOT projections are
ordered by actual covered positions. Convexity handles an entry already
seen before the earlier physical position; no backwards filter inference. -/
private theorem fullRootFirst_order {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {root W : V} (P : DWalk root W) (hP : Allowed (T.graph H root) P)
    {i j : ℕ} (hij : i≤j) (hj : j≤P.length)
    (hiCov : label T.chains (P.getVert i)≠none)
    (hjCov : label T.chains (P.getVert j)≠none) :
    Reachable T.G (first T.chains root (P.getVert i))
      (first T.chains root (P.getVert j)) := by
  classical
  obtain ⟨c,hjc⟩ := Option.ne_none_iff_exists'.mp hjCov
  have hprefix := allowed_subwalk hP (P.isSubwalk_take j)
  have hm := T.first_mem_support hH (P.take j) hprefix (P.take j).end_mem_support hjc
  obtain ⟨l,hl,hll⟩ := Walk.mem_support_iff_exists_getVert.mp hm
  have hlj : l≤j := by
    have hlen : (P.take j).length=min j P.length := by simp only [Walk.take_length]
    omega
  have hlg : P.getVert l=first T.chains root (P.getVert j) := by
    simpa only [Walk.take_getVert,Nat.min_eq_right hlj] using hl
  have hrootj : Reachable T.G root (P.getVert j) :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨P.take j,allowed_mono (fun _ _ h => h.1) hprefix⟩
  have hlabel : label T.chains (P.getVert l)=some c := by
    rw [hlg]
    exact (first_spec T.chains T.disjoint root _ hrootj hjCov).2.2.trans hjc
  by_cases hli : l ≤ i
  · have hic := T.graph_convex hH hP hli hij hj c hlabel hjc
    have he := first_constant T.chains root (P.getVert i) (P.getVert j) (hic.trans hjc.symm)
    rw [he]
    exact reachable_refl T.G _
  · have hrooti : Reachable T.G root (P.getVert i) :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨P.take i,allowed_mono (fun _ _ h => h.1)
          (allowed_subwalk hP (P.isSubwalk_take i))⟩
    have hgi := (first_spec T.chains T.disjoint root _ hrooti hiCov).2.1
    have hil : i≤l := by omega
    have hseg := reachable_segment (allowed_mono (fun _ _ h => h.1) hP) hil
    have hsegG := (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp hseg
    rw [hlg] at hsegG
    exact reachable_trans hgi hsegG

theorem rootTailProjection_order {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {root b W : V} (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) {i j : ℕ} (hij : i≤j) (hj : j≤q.length)
    (hiCov : label T.chains (q.getVert i)≠none)
    (hjCov : label T.chains (q.getVert j)≠none) :
    Reachable T.G (first T.chains root (q.getVert i))
      (first T.chains root (q.getVert j)) := by
  obtain ⟨p,hp,_hpc⟩ := T.distance_spec H hrootb
  let P := p.append q
  have hP : Allowed (T.graph H root) P := (allowed_append _ _ _).mpr ⟨hp,hq⟩
  have hiP : P.getVert (p.length+i)=q.getVert i := by
    change (p.append q).getVert (p.length+i)=q.getVert i
    rw [Walk.getVert_append,if_neg (by omega : ¬ p.length+i<p.length),Nat.add_sub_cancel_left]
  have hjP : P.getVert (p.length+j)=q.getVert j := by
    change (p.append q).getVert (p.length+j)=q.getVert j
    rw [Walk.getVert_append,if_neg (by omega : ¬ p.length+j<p.length),Nat.add_sub_cancel_left]
  have hlen : p.length+j≤P.length := by
    change p.length+j≤(p.append q).length
    rw [Walk.length_append]
    omega
  have ho := fullRootFirst_order T hH P hP (by omega : p.length+i≤p.length+j) hlen
    (by simpa only [hiP] using hiCov) (by simpa only [hjP] using hjCov)
  simpa only [hiP,hjP] using ho

theorem rootTailHeads_order {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {root b W v w : V} (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q)
    (hv : v ∈ T.rootTailHeads root q) (hw : w ∈ T.rootTailHeads root q)
    (horder : T.rootTailHeadPosition root q v≤T.rootTailHeadPosition root q w) :
    Reachable T.G v w := by
  have hi := T.rootTailHeadPosition_spec q hv
  have hj := T.rootTailHeadPosition_spec q hw
  have hr := T.rootTailProjection_order hH hrootb q hq horder hj.1 hi.2.1 hj.2.1
  simpa only [hi.2.2,hj.2.2] using hr

/-- The actual child-cone pattern is an INSIDE prefix and EXTERIOR suffix
in this injective physical order. Neither length nor ownership is assumed. -/
theorem rootTailHeads_child_pattern {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {root b W U v w : V} (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q)
    (hv : v ∈ T.rootTailHeads root q) (hw : w ∈ T.rootTailHeads root q)
    (horder : T.rootTailHeadPosition root q v≤T.rootTailHeadPosition root q w) :
    (w ∈ T.rootHeadCone root U → v ∈ T.rootHeadCone root U) ∧
      (v ∉ T.rootHeadCone root U → w ∉ T.rootHeadCone root U) := by
  have hr := T.rootTailHeads_order hH hrootb q hq hv hw horder
  obtain ⟨c,_hc,_hv,hl,_hroot,_hf,hip,_hW,_he⟩ := T.rootTailHeads_spec hH hrootb q hq hv
  have hback : w ∈ T.rootHeadCone root U → v ∈ T.rootHeadCone root U := by
    intro hwU
    exact T.mem_rootHeadCone_iff.mpr
      ⟨hip,reachable_trans hr (T.mem_rootHeadCone_iff.mp hwU).2.1,c,hl⟩
  exact ⟨hback,fun hvU hwU => hvU (hback hwU)⟩

theorem rootTailHeads_marker {root b W : V} (q : DWalk b W)
    (hb : label T.chains b≠none) :
    first T.chains root b ∈ T.rootTailHeads root q ∧
      T.rootTailHeadPosition root q (first T.chains root b)=0 := by
  classical
  obtain ⟨c,hbc⟩ := Option.ne_none_iff_exists'.mp hb
  have hm : first T.chains root b ∈ T.rootTailHeads root q := by
    refine Finset.mem_image.mpr ⟨c,(T.mem_chainSet q c).mpr ⟨b,q.start_mem_support,hbc⟩,?_⟩
    simp only [first,hbc]
  have hz : T.RootTailHeadAt root q (first T.chains root b) 0 := by
    exact ⟨Nat.zero_le _,by simpa only [Walk.getVert_zero] using hb,by simp⟩
  exact ⟨hm,Nat.eq_zero_of_le_zero (T.rootTailHeadPosition_le q hz)⟩

theorem rootTailHeads_endpoint {root b W : V} (q : DWalk b W)
    (hW : (root,W) ∈ T.important) : W ∈ T.rootTailHeads root q := by
  classical
  obtain ⟨c,hc⟩ := T.important_covered hW
  refine Finset.mem_image.mpr ⟨c,(T.mem_chainSet q c).mpr ⟨W,q.end_mem_support,hc⟩,?_⟩
  simpa only [first,hc] using (T.important_spec hW).2

end GreedyShortcuts.ChainDistance.Context
