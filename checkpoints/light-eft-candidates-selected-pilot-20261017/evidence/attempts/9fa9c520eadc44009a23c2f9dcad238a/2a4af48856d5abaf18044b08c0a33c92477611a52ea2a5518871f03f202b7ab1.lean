import LightEFTSpanners.NativeRefinementRigidity
import LightEFTSpanners.NativeColorExchange

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}

/-- A newly inserted actual edge joining distinct old within-block components
makes the selected component relation strictly coarser, provided all old
within-block routes survive. -/
theorem componentRefinement_lt_of_new_edge (G : Graph V E) {k : ℕ}
    (color other : E → Fin (k+1)) (R : Setoid G.vertexSet) (c : Fin (k+1))
    (hp : ∀ a b : G.vertexSet,
      (blockGraph (G.restrict {e | color e=c}).toSimpleGraph R).Reachable a b →
      (blockGraph (G.restrict {e | other e=c}).toSimpleGraph R).Reachable a b)
    {e : E} (he : other e=c) (hin : edgeInside G R e)
    (hout : ¬edgeInside G (componentRefinement (G.restrict {x | color x=c}).toSimpleGraph R) e) :
    componentRefinement (G.restrict {x | color x=c}).toSimpleGraph R <
      componentRefinement (G.restrict {x | other x=c}).toSimpleGraph R := by
  apply lt_of_le_of_ne (componentRefinement_le_of_routes _ _ _ hp)
  intro heq
  obtain ⟨a,b,hl,hR⟩ := hin
  have hnew : (blockGraph (G.restrict {x | other x=c}).toSimpleGraph R).Reachable a b := by
    by_cases hab : a=b
    · subst b; rfl
    · exact (show (blockGraph (G.restrict {x | other x=c}).toSimpleGraph R).Adj a b from
        ⟨⟨hab,e,he,hl⟩,hR⟩).reachable
  apply hout
  refine ⟨a,b,hl,?_⟩
  have hnew' : (componentRefinement (G.restrict {x | other x=c}).toSimpleGraph R).r a b := hnew
  exact (congrArg (fun S : Setoid G.vertexSet => S.r a b) heq).mpr hnew'

/-- The concrete two-identity swap improves the genuine recomputed signature
from its two real replacement routes and split boundaries. The selected-color
separation supplies strict progress; no unchanged-prefix premise is assumed. -/
theorem exchangedColor_strict_signature (G : Graph V E) [Fintype G.vertexSet]
    {k N : ℕ} (color : E → Fin (k+1)) {e d : E}
    (hdiff : color e≠color d) (m md : ℕ) (hm : m<N)
    (hext : ¬edgeInside G (nativePartitionAt G color (m+1)) e)
    (hdxt : ¬edgeInside G (nativePartitionAt G color (md+1)) d)
    (eroute : ∀ a b : G.vertexSet,G.IsLink e a.val b.val →
      (blockGraph (G.restrict {x | exchangedColor color e d x=color e}).toSimpleGraph
        (nativePartitionAt G color m)).Reachable a b)
    (droute : ∀ a b : G.vertexSet,G.IsLink d a.val b.val →
      (blockGraph (G.restrict {x | exchangedColor color e d x=color d}).toSimpleGraph
        (nativePartitionAt G color md)).Reachable a b)
    (hpriority : nativePriorityAt G color m=(color d).val)
    (hin : edgeInside G (nativePartitionAt G color m) e)
    (hout : ¬edgeInside G
      (componentRefinement (G.restrict {x | color x=color d}).toSimpleGraph
        (nativePartitionAt G color m)) e) :
    nativeRefinementSignature G N color < nativeRefinementSignature G N (exchangedColor color e d) := by
  have hanti : Antitone (nativePartitionAt G color) :=
    color_refinement_iterates_antitone _ ⊤
  have hp (i : ℕ) (c : Fin (k+1)) (a b : G.vertexSet) :=
    exchangedColor_preserves_stages G color hdiff (nativePartitionAt G color) hanti m md
      hext hdxt eroute droute c i (a:=a) (b:=b)
  apply native_signature_improves_of_selected_coarsening G color (exchangedColor color e d)
    (fun i _ c a b => hp i c a b) m hm (color d) hpriority
  apply componentRefinement_lt_of_new_edge G color (exchangedColor color e d)
    (nativePartitionAt G color m) (color d) (hp m (color d)) (e:=e) ?_ hin hout
  simp only [exchangedColor,ite_true]
end LightEFTSpanners.MultigraphCuts
