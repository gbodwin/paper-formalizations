import LightEFTSpanners.NativeSplitReachability
import LightEFTSpanners.NativeCenterElimination

namespace LightEFTSpanners.EvenSplitting
universe u v w
variable {V : Type u} {E F : Type v} {I : Type w}

/-- Pull an entire edge-disjoint family through a finite literal split trace.
The family uses original identities and retains every actual output connection.
No acyclicity of the raw expansions is claimed or needed. -/
theorem CenterSplitTrace.pullback_family {G : Graph (Option V) E}
    {H : Graph (Option V) F} (htrace : CenterSplitTrace G H)
    (A : I → Set F) (hA : ∀ c,A c⊆H.edgeSet)
    (hdis : Pairwise (fun c d => Disjoint (A c) (A d))) :
    ∃ B : I → Set E,(∀ c,B c⊆G.edgeSet) ∧
      Pairwise (fun c d => Disjoint (B c) (B d)) ∧
      ∀ c x y,EdgeSetJoins H (A c) x y → EdgeSetJoins G (B c) x y := by
  induction htrace with
  | refl G => exact ⟨A,hA,hdis,fun _ _ _ h => h⟩
  | step G i j hij tail ih =>
    obtain ⟨B,hB,hd,hj⟩ := ih A hA hdis
    refine ⟨fun c => splitPullback G i j (B c),?_,?_,?_⟩
    · exact fun c => splitPullback_subset G i j (hB c)
    · exact fun c d hcd => splitPullback_disjoint G i j (hB c) (hB d) (hd hcd)
    · exact fun c x y h => splitPullback_joins G i j (B c) (hj c x y h)

/-- The center-free graph is the actual induced terminal domain. Its walks
are genuine walks in the unreduced graph with the same selected edge IDs. -/
theorem centerCore_joins (G : Graph (Option V) E) (A : Set E) {x y : V}
    (h : EdgeSetJoins (centerCore G) A x y) :
    EdgeSetJoins G A (some x) (some y) := by
  obtain ⟨hx,hy,hr⟩ := h
  let f : ((centerCore G).restrict A).toSimpleGraph →g (G.restrict A).toSimpleGraph :=
    { toFun := fun a => ⟨some a.val,a.property⟩
      map_rel' := by
        rintro a b ⟨hne,e,he,hlink⟩
        refine ⟨?_,e,he,hlink⟩
        intro hab
        exact hne (Subtype.ext (Option.some.inj (congrArg Subtype.val hab))) }
  exact ⟨hx,hy,hr.map f⟩

/-- A family selected on the reduced terminal graph expands through the exact
split trace. Disjointness is on original edge identities, including parallels. -/
theorem CenterSplitTrace.pullback_core_family {G : Graph (Option V) E}
    {H : Graph (Option V) F} (htrace : CenterSplitTrace G H)
    (A : I → Set F) (hA : ∀ c,A c⊆(centerCore H).edgeSet)
    (hdis : Pairwise (fun c d => Disjoint (A c) (A d))) :
    ∃ B : I → Set E,(∀ c,B c⊆G.edgeSet) ∧
      Pairwise (fun c d => Disjoint (B c) (B d)) ∧
      ∀ c x y,EdgeSetJoins (centerCore H) (A c) x y →
        EdgeSetJoins G (B c) (some x) (some y) := by
  have hAH (c : I) : A c⊆H.edgeSet := by
    intro e he
    obtain ⟨x,y,hxy⟩ := Graph.exists_isLink_of_mem_edgeSet (hA c he)
    exact (show H.IsLink e (some x) (some y) from hxy).edge_mem
  obtain ⟨B,hB,hd,hj⟩ := htrace.pullback_family A hAH hdis
  exact ⟨B,hB,hd,fun c x y h => hj c (some x) (some y) (centerCore_joins H (A c) h)⟩
end LightEFTSpanners.EvenSplitting
