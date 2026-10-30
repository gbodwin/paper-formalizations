import GreedyShortcuts.ChainRootMinimumCorridor

/-! SOURCE ONLY, UNCOMPILED. Original one-step minimum-tail relay/guard
selector, using actual corridor/owner/minimum/LAST-tail constructions.
Choice contains only the numerical rule and actual maxima; geometry/ranks/
proper decrease are separately PROVED outputs, never selector fields. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- The ORIGINAL choice rule only. delta is the actual attaining old-owner
tail; sigma is the actual maximum old-owner rank. The guard target is the
ROOT projection of THAT row's literal LAST entry. No output facts appear. -/
def OriginalMinimumTailChoice {H : Finset (V × V)} {root a W : V}
    (Q : T.OwnerMinimumFamily H root a W)
    (F : ∀ x : T.RootOwner root a,T.OwnerLastRootTail H root x.val W (Q x).val)
    (x : T.RootOwner root a) (Vmax U : V) : Prop :=
  (T.distance H root W-T.distance H root Vmax≤(F x).tau ∧ U=Vmax) ∨
  ((F x).tau<T.distance H root W-T.distance H root Vmax ∧
    T.RootConeMaximizer H root (first T.chains root (F x).entry) U)

/-- Output conjunction, NOT input data or desired transition fields. -/
def OriginalMinimumTailStepFacts {H : Finset (V × V)} {root a W : V}
    (c q : ℕ) (Q : T.OwnerMinimumFamily H root a W)
    (F : ∀ x : T.RootOwner root a,T.OwnerLastRootTail H root x.val W (Q x).val)
    (x : T.RootOwner root a) (Vmax U : V) : Prop :=
  (root,U) ∈ T.important ∧ Reachable T.G U W ∧
    T.RootConeMaximizer H root U U ∧
    T.rootHeadCone root U ⊆ T.rootHeadCone root W ∧
    T.rootHeadCone root U ⊂ T.rootHeadCone root W ∧
    (T.rootHeadCone root U).card<(T.rootHeadCone root W).card ∧
    c≤T.distance H root U ∧ T.distance H root U≤T.distance H root W ∧
    T.distance H root W-T.distance H root U≤
      T.distance H root W-T.distance H root Vmax ∧
    T.distance H root W-T.distance H root U≤(F x).tau ∧
    (∀ y : T.RootOwner root a,T.distance H root W-T.distance H root U≤(F y).tau) ∧
    (q≤T.distance H root U ∨ (c≤T.distance H root U ∧ T.distance H root U<q))

/-- Branch witnesses are derived outputs. Relay retains the real anchor
exception; guard retains the actual selected row, LAST entry, tail price
and genuine removed source. No B/H/E or forcing conclusions are assumed. -/
def OriginalMinimumTailBranchFacts {H : Finset (V × V)} {root a W : V}
    (c q : ℕ) (Q : T.OwnerMinimumFamily H root a W)
    (F : ∀ x : T.RootOwner root a,T.OwnerLastRootTail H root x.val W (Q x).val)
    (x : T.RootOwner root a) (Vmax U : V) : Prop :=
  (U=Vmax ∧ T.distance H root W-T.distance H root Vmax≤(F x).tau ∧
    Reachable T.G U a ∧
    W ∈ T.rootHeadCone root W \ T.rootHeadCone root U ∧
    (∀ b,Reachable T.G a b →
      (b ∈ T.rootHeadCone root U ↔ b=a ∧ U=a)) ∧
    (U=a → T.distance H root U=c ∧ T.distance H root U<q)) ∨
  ∃ g,(F x).tau<T.distance H root W-T.distance H root Vmax ∧
    g=first T.chains root (F x).entry ∧
    ¬ Allowed (T.graph H root) (Q x).val ∧
    (root,g) ∈ T.important ∧ Reachable T.G g W ∧
    ¬ Reachable T.G x.val g ∧ Reachable T.G U g ∧
    T.RootConeMaximizer H root g U ∧
    T.distance H root Vmax<T.distance H root g ∧
    T.distance H root W≤T.distance H root g+(F x).tau ∧
    T.distance H root g≤T.distance H root U ∧
    x.val ∈ T.rootHeadCone root W \ T.rootHeadCone root U ∧
    (∀ b,Reachable T.G a b → b ∉ T.rootHeadCone root U)

/-- ALL permitted min/max ties obey the derived one-step facts. The
attaining row and its fixed original walk are not replaced in either mode. -/
theorem originalMinimumTailChoice_facts {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root a W : V} {c q : ℕ}
    (hW : T.RootConeMaximizer H root W W)
    (ha : (root,a) ∈ T.important) (haW : Reachable T.G a W)
    (hne : a≠W) (harank : T.distance H root a=c) (hcq : c<q)
    (Q : T.OwnerMinimumFamily H root a W)
    (F : ∀ x : T.RootOwner root a,T.OwnerLastRootTail H root x.val W (Q x).val)
    (x : T.RootOwner root a) (Vmax U : V)
    (hmin : ∀ y : T.RootOwner root a,(F x).tau≤(F y).tau)
    (hmax : T.RootConeMaximizer H root a Vmax)
    (hchoice : T.OriginalMinimumTailChoice Q F x Vmax U) :
    T.OriginalMinimumTailStepFacts c q Q F x Vmax U ∧
      T.OriginalMinimumTailBranchFacts c q Q F x Vmax U := by
  classical
  have hSigmaParent : T.distance H root Vmax≤T.distance H root W :=
    hW.2 Vmax ((T.rootHeadCone_mono haW) hmax.1)
  rcases hchoice with ⟨hrelay,hUV⟩ | ⟨hguard,hmaxG⟩
  · subst U
    obtain ⟨hip,hVa,_hsubA,_hnormA,_hfloorA⟩ :=
      T.rootConeMaximizer_normalizes ha hmax
    obtain ⟨hnorm,hsub,hremoved,hcard,hfloor,hupper⟩ :=
      T.relay_maximum_from_anchor hW ha haW hne hmax
    have hproper : T.rootHeadCone root Vmax ⊂ T.rootHeadCone root W := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub,?_⟩
      intro he
      rw [he] at hcard
      omega
    have hfloorc : c≤T.distance H root Vmax := by omega
    have hrows : ∀ y : T.RootOwner root a,
        T.distance H root W-T.distance H root Vmax≤(F y).tau :=
      fun y => hrelay.trans (hmin y)
    have hstop : q≤T.distance H root Vmax ∨
        (c≤T.distance H root Vmax ∧ T.distance H root Vmax<q) := by
      by_cases hs : q≤T.distance H root Vmax
      · exact Or.inl hs
      · exact Or.inr ⟨hfloorc,by omega⟩
    have hterminal : Vmax=a → T.distance H root Vmax=c ∧
        T.distance H root Vmax<q := by
      intro he
      constructor
      · simpa only [he] using harank
      · simpa only [he,harank] using hcq
    exact ⟨⟨hip,reachable_trans hVa haW,hnorm,hsub,hproper,hcard,hfloorc,
      hupper,le_rfl,hrelay,hrows,hstop⟩,
      Or.inl ⟨rfl,hrelay,hVa,hremoved,
        fun b hb => T.relay_descendant_retained_iff ha hmax hb,hterminal⟩⟩
  · have hstrict : T.distance H root Vmax+(F x).tau<T.distance H root W := by omega
    obtain ⟨_hmin',hbad,g,hg,he,hgW,hxg,hprice,hsigG⟩ :=
      T.minimum_owner_tail_strict_guard hH Q F x hmin hmax hstrict
    have hmaxg : T.RootConeMaximizer H root g U := by simpa only [he] using hmaxG
    obtain ⟨hx,hxa,_hxc⟩ := T.mem_rootHeadCone_iff.mp x.property
    obtain ⟨hip,hUg,hUW,hnorm,hsub,hremoved,hcard,hfloorG,hupper⟩ :=
      T.rootCone_child_of_separator hW hg hgW hx (reachable_trans hxa haW) hxg hmaxg
    have hfloorV := (T.rootConeMaximizer_normalizes ha hmax).2.2.2.2
    have hfloorc : c≤T.distance H root U := by omega
    have hdropD : T.distance H root W-T.distance H root U≤
        T.distance H root W-T.distance H root Vmax := by omega
    have hdropTail : T.distance H root W-T.distance H root U≤(F x).tau := by omega
    have hrows : ∀ y : T.RootOwner root a,
        T.distance H root W-T.distance H root U≤(F y).tau :=
      fun y => hdropTail.trans (hmin y)
    have hproper : T.rootHeadCone root U ⊂ T.rootHeadCone root W := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub,?_⟩
      intro heq
      rw [heq] at hcard
      omega
    have hstop : q≤T.distance H root U ∨
        (c≤T.distance H root U ∧ T.distance H root U<q) := by
      by_cases hs : q≤T.distance H root U
      · exact Or.inl hs
      · exact Or.inr ⟨hfloorc,by omega⟩
    have hdesc : ∀ b,Reachable T.G a b → b ∉ T.rootHeadCone root U := by
      intro b hab hb
      have hbU := (T.mem_rootHeadCone_iff.mp hb).2.1
      exact hxg (reachable_trans hxa (reachable_trans hab (reachable_trans hbU hUg)))
    exact ⟨⟨hip,hUW,hnorm,hsub,hproper,hcard,hfloorc,hupper,hdropD,hdropTail,hrows,hstop⟩,
      Or.inr ⟨g,hguard,he,hbad,hg,hgW,hxg,hUg,hmaxg,hsigG,hprice,hfloorG,hremoved,hdesc⟩⟩

/-- Construct an actual attaining minimum owner and actual maximum owner,
then the original numerical choice and selected child. No desired output
facts are hypotheses. The fixed family Q/F is arbitrary, not favorably retied. -/
theorem exists_original_minimum_tail_step {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root a W : V} {c q : ℕ}
    (hW : T.RootConeMaximizer H root W W)
    (ha : (root,a) ∈ T.important) (haW : Reachable T.G a W)
    (hne : a≠W) (harank : T.distance H root a=c) (hcq : c<q)
    (Q : T.OwnerMinimumFamily H root a W)
    (F : ∀ x : T.RootOwner root a,T.OwnerLastRootTail H root x.val W (Q x).val) :
    ∃ (x : T.RootOwner root a) (Vmax U : V),
      (∀ y : T.RootOwner root a,(F x).tau≤(F y).tau) ∧
      T.RootConeMaximizer H root a Vmax ∧
      T.OriginalMinimumTailChoice Q F x Vmax U ∧
      T.OriginalMinimumTailStepFacts c q Q F x Vmax U ∧
      T.OriginalMinimumTailBranchFacts c q Q F x Vmax U := by
  classical
  obtain ⟨x,hmin⟩ := T.exists_minimum_owner_tail ha Q F
  obtain ⟨Vmax,hmax⟩ := T.exists_rootConeMaximizer H ha
  have hSigmaParent : T.distance H root Vmax≤T.distance H root W :=
    hW.2 Vmax ((T.rootHeadCone_mono haW) hmax.1)
  have hex : ∃ U,T.OriginalMinimumTailChoice Q F x Vmax U := by
    by_cases hrelay : T.distance H root W-T.distance H root Vmax≤(F x).tau
    · exact ⟨Vmax,Or.inl ⟨hrelay,rfl⟩⟩
    · have hguard : (F x).tau<T.distance H root W-T.distance H root Vmax := by omega
      have hstrict : T.distance H root Vmax+(F x).tau<T.distance H root W := by omega
      obtain ⟨_hm,_hbad,g,hg,he,_hgW,_hxg,_hprice,_hsigG⟩ :=
        T.minimum_owner_tail_strict_guard hH Q F x hmin hmax hstrict
      obtain ⟨U,hU⟩ := T.exists_rootConeMaximizer H hg
      refine ⟨U,Or.inr ⟨hguard,?_⟩⟩
      simpa only [he] using hU
  obtain ⟨U,hchoice⟩ := hex
  obtain ⟨hfacts,hbranch⟩ :=
    T.originalMinimumTailChoice_facts hH hW ha haW hne harank hcq Q F x Vmax U hmin hmax hchoice
  exact ⟨x,Vmax,U,hmin,hmax,hchoice,hfacts,hbranch⟩

/-- Actual corridor-to-mode construction. First derive the strict-range
anchor from the SAME fixed P. Real owner/last-tail families exist, and EVERY
already fixed such family gets the original one-step construction above. -/
theorem actual_root_corridor_minimum_tail_step {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root W : V}
    (hW : T.RootConeMaximizer H root W W) (P : DWalk root W)
    (hP : Allowed (T.graph H root) P)
    (hPmin : T.count P=T.distance H root W) {c q : ℕ}
    (hc : 1≤c) (hcq : c<q) (hactive : q≤T.distance H root W) :
    ∃ i,i<P.length ∧ T.count (P.take i)=c ∧
      (root,P.getVert i) ∈ T.important ∧ T.distance H root (P.getVert i)=c ∧
      Reachable T.G (P.getVert i) W ∧ P.getVert i≠W ∧
      Nonempty (Σ Q : T.OwnerMinimumFamily H root (P.getVert i) W,
        ∀ y : T.RootOwner root (P.getVert i),
          T.OwnerLastRootTail H root y.val W (Q y).val) ∧
      ∀ (Q : T.OwnerMinimumFamily H root (P.getVert i) W)
        (F : ∀ y : T.RootOwner root (P.getVert i),
          T.OwnerLastRootTail H root y.val W (Q y).val),
        ∃ (x : T.RootOwner root (P.getVert i)) (Vmax U : V),
          (∀ y : T.RootOwner root (P.getVert i),(F x).tau≤(F y).tau) ∧
          T.RootConeMaximizer H root (P.getVert i) Vmax ∧
          T.OriginalMinimumTailChoice Q F x Vmax U ∧
          T.OriginalMinimumTailStepFacts c q Q F x Vmax U ∧
          T.OriginalMinimumTailBranchFacts c q Q F x Vmax U := by
  classical
  have hcR : c<T.distance H root W := by omega
  obtain ⟨i,_hil,hcount,ha,harank,haW,_hend,hstrict,_hinit,_hpos⟩ :=
    T.normalized_root_corridor_anchor hH hW P hP hPmin c hc (by omega)
  obtain ⟨hilt,hne⟩ := hstrict hcR
  have hfamilies : Nonempty (Σ Q : T.OwnerMinimumFamily H root (P.getVert i) W,
      ∀ y : T.RootOwner root (P.getVert i),
        T.OwnerLastRootTail H root y.val W (Q y).val) := by
    obtain ⟨Q⟩ := T.exists_ownerMinimumFamily H (root := root) haW
    obtain ⟨F⟩ := T.exists_ownerLastRootTailFamily Q
    exact ⟨⟨Q,F⟩⟩
  exact ⟨i,hilt,hcount,ha,harank,haW,hne,hfamilies,
    fun Q F => T.exists_original_minimum_tail_step hH hW ha haW hne harank hcq Q F⟩

/-- The actual preserved selector constants are c=k and q=16*k. Positive k
and an ACTUAL active parent imply the needed strict anchor range; below-q
children are terminal, not a premise that another band exists. -/
theorem original_selector_active_parameters {k R : ℕ}
    (hk : 1≤k) (hactive : 16*k≤R) :
    1≤k ∧ k<16*k ∧ 16*k≤R ∧ k<R := by omega

end GreedyShortcuts.ChainDistance.Context
