import LightEFTSpanners.NativeEulerianForestPacking
import LightEFTSpanners.ContractedCoreConnectivity

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
/-- Simple-graph incidence retains the exact unordered original edge ID. -/
theorem ofSimpleGraph_inc_iff (G : SimpleGraph V) (e : Sym2 V) (v : V) :
    (Graph.ofSimpleGraph G).Inc e v ↔ e∈G.incidenceSet v := by
  constructor
  · rintro ⟨w,he,hw⟩
    subst e
    exact ⟨hw,Sym2.mem_mk_left _ _⟩
  · intro he
    induction e using Sym2.inductionOn with
    | _ a b =>
      obtain ⟨hab,hva|hvb⟩ := G.mk'_mem_incidenceSet_iff.mp he
      · subst v; exact ⟨b,rfl,G.mem_edgeSet.mpr hab⟩
      · subst v; exact ⟨a,Sym2.eq_swap,G.mem_edgeSet.mpr hab⟩

/-- The actual native degree agrees with the usual simple-graph degree. -/
theorem ofSimpleGraph_nativeDegree (G : SimpleGraph V) (v : V) :
    nativeDegree (Graph.ofSimpleGraph G) v=(G.degree v:ℤ) := by
  classical
  have hn (e : Sym2 V) : ¬(Graph.ofSimpleGraph G).IsLink e v v := by
    rintro ⟨rfl,h⟩
    exact (G.mem_edgeSet.mp h).ne rfl
  simp only [nativeDegree,hn,ite_false,ofSimpleGraph_inc_iff]
  rw [←G.card_incidenceFinset_eq_degree v]
  simp only [←G.mem_incidenceFinset,Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter]

/-- Restricting native original IDs has a literal simple-graph interpretation
on the same full actual vertex domain. -/
def nativeSelectedIso (G : SimpleGraph V) (A : Set (Sym2 V)) :
    ((Graph.ofSimpleGraph G).restrict A).toSimpleGraph ≃g
      (G ⊓ fromEdgeSet A) := by
  refine ⟨Equiv.Set.univ V,?_⟩
  intro x y
  constructor
  · rintro ⟨hG,hA,hne⟩
    exact ⟨fun h => hne (congrArg Subtype.val h),s(x.val,y.val),hA,rfl,G.mem_edgeSet.mpr hG⟩
  · rintro ⟨hne,e,heA,he,heG⟩
    subst e
    exact ⟨G.mem_edgeSet.mp heG,heA,fun h => hne (Subtype.ext h)⟩

end LightEFTSpanners.MultigraphCuts
