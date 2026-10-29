import GreedyShortcuts.ChainGuardSeparation
import GreedyShortcuts.ChainSubwalk

/-! SOURCE ONLY, UNCOMPILED. A strict, exactly joined price defect yields
the actual last rejected entry and a same-source off-reference chain bound.
This is local native codification, not a global progress or ownership bound. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

private theorem strictJoinV2_last_rejected_split {A B : V → V → Prop} {u t : V}
    (q : DWalk u t) (hq : Allowed A q) (hbad : ¬ Allowed B q) :
    ∃ (a b : V) (h : (⊤ : SimpleGraph V).Adj a b)
      (l : DWalk u a) (r : DWalk b t),
      q=l.append (.cons h r) ∧ Allowed A l ∧ A a b ∧ ¬ B a b ∧
      Allowed A r ∧ Allowed B r := by
  classical
  induction q with
  | nil => exact (hbad (allowed_nil _ _)).elim
  | @cons u v t h q ih =>
    obtain ⟨huv,hqA⟩ := (allowed_cons _ h q).mp hq
    by_cases hqB : Allowed B q
    · have hn : ¬ B u v := by
        intro hb
        exact hbad ((allowed_cons _ h q).mpr ⟨hb,hqB⟩)
      exact ⟨u,v,h,.nil,q,rfl,allowed_nil _ _,huv,hn,hqA,hqB⟩
    · obtain ⟨a,b,h',l,r,he,hl,hab,hnb,hrA,hrB⟩ := ih hqA hqB
      refine ⟨a,b,h',.cons h l,r,?_,
        (allowed_cons _ h l).mpr ⟨huv,hl⟩,hab,hnb,hrA,hrB⟩
      simp only [he,Walk.cons_append]

variable (T : ChainDistance.Context V I)

/-- Exact covered/uncovered strict join defect. The reference is genuinely
S-admitted through w; the competing tail is only w-admitted. The exported
dart is literally the last S-rejection on that tail, since its entire
following suffix is S-admitted. No reference or competing tail is assumed
minimum. Delta is a positive integer LOWER bound on the exact defect. -/
theorem strict_join_last_guard_offpath_v2 {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {s w v t : V}
    (p : DWalk s w) (reference : DWalk w v)
    (hpref : Allowed (T.graph H s) (p.append reference))
    (tail : DWalk w t) (htail : Allowed (T.graph H w) tail)
    (ht : (s,t) ∈ T.important) {delta : ℕ} (hdelta : 0<delta)
    (hcheap : T.count p+T.count tail+delta ≤
      T.distance H s t+(label T.chains w).toFinset.card) :
    ∃ (a b : V) (h : (⊤ : SimpleGraph V).Adj a b)
      (l : DWalk w a) (r : DWalk b t) (z : V) (repair : DWalk s z),
      tail=l.append (.cons h r) ∧ Allowed (T.graph H w) l ∧
      T.graph H w a b ∧ ¬ T.graph H s a b ∧
      Allowed (T.graph H s) r ∧ label T.chains b≠none ∧
      first T.chains w b=b ∧ first T.chains s b≠b ∧
      z=first T.chains s b ∧ (s,z) ∈ T.important ∧
      Reachable T.G z t ∧ ¬ Reachable T.G w z ∧
      Allowed (T.graph H s) repair ∧ T.count repair=T.distance H s z ∧
      T.count tail+1=T.count (l.append (.cons h .nil))+T.count r ∧
      (label T.chains w).toFinset.card+1 ≤ T.count (l.append (.cons h .nil)) ∧
      T.distance H s t+1 ≤ T.distance H s z+T.count r ∧
      T.count p+delta+1 ≤ T.distance H s z ∧
      delta+1 ≤ (T.chainSet repair \ T.chainSet (p.append reference)).card := by
  classical
  have hp := (allowed_append _ p reference).mp hpref |>.1
  have hsw : Reachable T.G s w :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p,allowed_mono (fun _ _ h => h.1) hp⟩
  have hbad : ¬ Allowed (T.graph H s) tail := by
    intro hs
    have hall := (allowed_append _ p tail).mpr ⟨hp,hs⟩
    have hc := T.count_append_exact hH p tail hall
    have hd := T.distance_le_walk H (T.important_spec ht).1 (p.append tail) hall
    omega
  obtain ⟨a,b,h,l,r,hform,hl,hab,hnb,hrw,hrs⟩ :=
    strictJoinV2_last_rejected_split tail htail hbad
  have hdiff : label T.chains a ≠ label T.chains b := by
    intro he
    exact hnb ⟨hab.1,Or.inl he⟩
  have hcovered : label T.chains b ≠ none := by
    intro he
    exact hnb ⟨hab.1,Or.inr (Or.inl he)⟩
  obtain ⟨c,hbc⟩ := Option.ne_none_iff_exists'.mp hcovered
  have hfirst : first T.chains w b=b :=
    hab.2.resolve_left hdiff |>.resolve_left hcovered
  have hnfirst : first T.chains s b ≠ b := by
    intro he
    exact hnb ⟨hab.1,Or.inr (Or.inr he)⟩
  let prefixB : DWalk w b := l.append (.cons h .nil)
  have hprefixB : Allowed (T.graph H w) prefixB :=
    (allowed_append _ _ _).mpr
      ⟨hl,(allowed_cons _ h .nil).mpr ⟨hab,allowed_nil _ _⟩⟩
  have hform' : tail=prefixB.append r := by
    simpa only [prefixB,← Walk.append_assoc,Walk.cons_append,Walk.nil_append] using hform
  have hsplit : T.count tail+1=T.count prefixB+T.count r := by
    have hc := T.count_append_exact hH prefixB r
      ((allowed_append _ _ _).mpr ⟨hprefixB,hrw⟩)
    simpa [← hform',hbc] using hc
  have hwb : Reachable T.G w b :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨prefixB,allowed_mono (fun _ _ h => h.1) hprefixB⟩
  have hsb := reachable_trans hsw hwb
  have hf := first_spec T.chains T.disjoint s b hsb hcovered
  let z := first T.chains s b
  have hzc : label T.chains z=some c := hf.2.2.trans hbc
  have hzt : Reachable T.G z t := reachable_trans hf.2.1
    ((reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨r,allowed_mono (fun _ _ h => h.1) hrs⟩)
  have hnwz : ¬ Reachable T.G w z := by
    intro hwz
    have hwf := first_spec T.chains T.disjoint w z hwz (by simp [hzc])
    have he : first T.chains w z=b :=
      (first_constant T.chains w z b hf.2.2).trans hfirst
    rw [he] at hwf
    have heb : z=b :=
      (acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hf.2.1 hwf.2.1
    exact hnfirst heb
  have hbne : b≠w := by
    intro he
    have hwa : Reachable T.G w a :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨l,allowed_mono (fun _ _ h => h.1) hl⟩
    have habG : Reachable T.G a b :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨.cons h .nil,(allowed_cons _ h .nil).mpr ⟨hab.1,allowed_nil _ _⟩⟩
    have hba : Reachable T.G b a := by simpa only [he] using hwa
    exact h.ne ((acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ habG hba)
  have hlabel : label T.chains w≠label T.chains b := by
    intro he
    have hfwb : first T.chains w b=w :=
      (first_constant T.chains w b w he.symm).trans (T.first_self w)
    exact hbne (hfirst.symm.trans hfwb)
  have hbmem : c ∈ T.chainSet prefixB :=
    (T.mem_chainSet prefixB c).mpr ⟨b,prefixB.end_mem_support,hbc⟩
  have hprefixLower : (label T.chains w).toFinset.card+1 ≤ T.count prefixB := by
    cases hw : label T.chains w with
    | none =>
      have hc : 1 ≤ (T.chainSet prefixB).card := Finset.one_le_card.mpr ⟨c,hbmem⟩
      simpa [hw,count] using hc
    | some cw =>
      have hcw : cw ∈ T.chainSet prefixB :=
        (T.mem_chainSet prefixB cw).mpr ⟨w,prefixB.start_mem_support,hw⟩
      have hne : cw≠c := by
        intro he
        exact hlabel (by simpa only [hw,hbc,he])
      have hs : ({cw,c} : Finset I) ⊆ T.chainSet prefixB := by
        intro j hj
        simp only [Finset.mem_insert,Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact hcw
        · exact hbmem
      have hc := Finset.card_le_card hs
      have hc' : 2 ≤ T.count prefixB := by simpa [hne,count] using hc
      simpa [hw] using hc'
  obtain ⟨repair,hrepair,hrepairCount⟩ := T.distance_spec H hf.1
  obtain ⟨internal,hi,_hilength,hicolor⟩ := GreedyShortcuts.ChainCover.internal_short T hH hf.2.1 hzc hbc
  have his : Allowed (T.graph H s) internal := T.allowed_internal internal hi hicolor
  have hrepairTail := (allowed_append _ _ _).mpr
    ⟨(allowed_append _ _ _).mpr ⟨hrepair,his⟩,hrs⟩
  have hd := T.distance_le_walk H (T.important_spec ht).1
    ((repair.append internal).append r) hrepairTail
  have hc := T.count_append_covered (repair.append internal) r hbc
  rw [T.count_append_internal repair internal hicolor,hrepairCount] at hc
  have hprice : T.distance H s t+1 ≤ T.distance H s z+T.count r := by
    dsimp only [z]
    omega
  have hguardPrice : T.count p+delta+1 ≤ T.distance H s z := by omega
  have hoff := T.guard_offpath_count hH p reference repair hpref hrepair hnwz
  have hsupply : delta+1 ≤ (T.chainSet repair \ T.chainSet (p.append reference)).card := by omega
  exact ⟨a,b,h,l,r,z,repair,hform,hl,hab,hnb,hrs,hcovered,hfirst,hnfirst,rfl,
    T.first_important hsb hbc,hzt,hnwz,hrepair,hrepairCount,
    hsplit,hprefixLower,hprice,hguardPrice,hsupply⟩

end GreedyShortcuts.ChainDistance.Context
