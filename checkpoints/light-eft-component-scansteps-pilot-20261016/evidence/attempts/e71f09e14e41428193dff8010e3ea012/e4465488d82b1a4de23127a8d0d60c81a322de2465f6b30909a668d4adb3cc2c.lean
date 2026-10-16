import LightEFTSpanners.NativeSplitTracePullback
import LightEFTSpanners.NativeForestSelection
import LightEFTSpanners.NativeSteinerReduction

namespace LightEFTSpanners.EvenSplitting
open MultigraphCuts
universe u v w
variable {V : Type u} {E F : Type v} {I : Type w}

/-- Prune every member of an actual original-edge family to a native forest.
Membership only decreases, so disjointness is retained, and all member-wise
connections are preserved. Loops and parallel cycles are removed by the native
forest construction rather than being silently identified. -/
theorem prune_disjoint_native_family (G : Graph V E) (B : I → Set E)
    (hB : ∀ c,B c⊆G.edgeSet) (hdis : Pairwise (fun c d => Disjoint (B c) (B d))) :
    ∃ A : I → Set E,(∀ c,A c⊆B c ∧ A c⊆G.edgeSet ∧
      ∀ e∈(G.restrict (A c)).edgeSet,(G.restrict (A c)).IsBridge e) ∧
      Pairwise (fun c d => Disjoint (A c) (A d)) ∧
      ∀ c x y,EdgeSetJoins G (B c) x y → EdgeSetJoins G (A c) x y := by
  classical
  choose A hA hb hr using fun c => exists_native_spanning_forest (G.restrict (B c))
  have hsub (c : I) : A c⊆B c := fun _ h => (hA c h).2
  have heq (c : I) : (G.restrict (B c)).restrict (A c)=G.restrict (A c) := by
    rw [Graph.restrict_restrict,Set.inter_eq_right.mpr (hsub c)]
  refine ⟨A,?_,?_,?_⟩
  · intro c
    refine ⟨hsub c,(hsub c).trans (hB c),?_⟩
    simpa only [heq c] using hb c
  · exact fun c d hcd => (hdis hcd).mono (hsub c) (hsub d)
  · intro c x y ⟨hx,hy,hxy⟩
    have hreach := hr c
    have hs : ((G.restrict (B c)).restrict (A c)).toSimpleGraph=
        (G.restrict (A c)).toSimpleGraph := by
      ext a b
      constructor
      · rintro ⟨hne,e,ha,_,hlink⟩; exact ⟨hne,e,ha,hlink⟩
      · rintro ⟨hne,e,ha,hlink⟩; exact ⟨hne,e,ha,hsub c ha,hlink⟩
    rw [hs] at hreach
    exact ⟨hx,hy,(congrArg (fun R => R ⟨x,hx⟩ ⟨y,hy⟩) hreach).mpr hxy⟩

/-- End-to-end split-trace forest lifting: any disjoint family on the reduced
terminal graph gives disjoint native original-edge forests preserving each
member's terminal connections. No forest-family existence premise is hidden. -/
theorem CenterSplitTrace.lift_core_forests {G : Graph (Option V) E}
    {H : Graph (Option V) F} (htrace : CenterSplitTrace G H)
    (A : I → Set F) (hA : ∀ c,A c⊆(centerCore H).edgeSet)
    (hdis : Pairwise (fun c d => Disjoint (A c) (A d))) :
    ∃ B : I → Set E,(∀ c,B c⊆G.edgeSet ∧
      ∀ e∈(G.restrict (B c)).edgeSet,(G.restrict (B c)).IsBridge e) ∧
      Pairwise (fun c d => Disjoint (B c) (B d)) ∧
      ∀ c x y,EdgeSetJoins (centerCore H) (A c) x y →
        EdgeSetJoins G (B c) (some x) (some y) := by
  obtain ⟨B,hB,hd,hj⟩ := htrace.pullback_core_family A hA hdis
  obtain ⟨C,hC,hcd,hcj⟩ := prune_disjoint_native_family G B hB hd
  exact ⟨C,fun c => (hC c).2,hcd,
    fun c x y h => hcj c (some x) (some y) (hj c x y h)⟩

/-- The actual single-center Eulerian reduction now carries an original-edge
forest-lifting certificate for arbitrary disjoint output families. Constructing
the required output family is still a separate packing-induction obligation. -/
theorem exists_native_steiner_reduction_with_lifting [Fintype V] [DecidableEq V]
    [Fintype E] (G : Graph (Option V) E) (P : V → V → Prop) (k : ℕ)
    (hdeg : ∀ x,Even (nativeDegree G x)) (hconn : RequiredConnectivity G P k) :
    ∃ (F : Type v) (hF : Fintype F) (H : Graph (Option V) F),
      CenterEliminationResult G P k hF H ∧
      (centerCore H).vertexSet={x | some x∈G.vertexSet} ∧
      (letI := hF; ∀ x,Even (nativeDegree (centerCore H) x)) ∧
      (letI := hF; ∀ a b,P a b →
        ∃ (ha : a∈(centerCore H).vertexSet) (hb : b∈(centerCore H).vertexSet),
          FaultConnected (centerCore H) (2*k) ⟨a,ha⟩ ⟨b,hb⟩) ∧
      ∀ (A : I → Set F),(∀ c,A c⊆(centerCore H).edgeSet) →
        Pairwise (fun c d => Disjoint (A c) (A d)) →
        ∃ B : I → Set E,(∀ c,B c⊆G.edgeSet ∧
          ∀ e∈(G.restrict (B c)).edgeSet,(G.restrict (B c)).IsBridge e) ∧
          Pairwise (fun c d => Disjoint (B c) (B d)) ∧
          ∀ c x y,EdgeSetJoins (centerCore H) (A c) x y →
            EdgeSetJoins G (B c) (some x) (some y) := by
  obtain ⟨F,hF,H,hH,hv,hd,hc⟩ := exists_native_steiner_reduction G P k hdeg hconn
  refine ⟨F,hF,H,hH,hv,hd,hc,?_⟩
  let := hF
  exact fun A hA hdis => hH.1.lift_core_forests A hA hdis
end LightEFTSpanners.EvenSplitting
