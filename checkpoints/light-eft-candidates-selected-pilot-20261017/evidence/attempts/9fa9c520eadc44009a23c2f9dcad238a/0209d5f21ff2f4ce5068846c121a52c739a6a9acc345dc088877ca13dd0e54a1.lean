import LightEFTSpanners.NativeColorExchange
import LightEFTSpanners.NativePartitionLabels
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- The actual least splitting color, with the finite color count as the
terminal sentinel when every block is already connected in every color. -/
noncomputable def refinementPriority {X : Type*} {k : ℕ}
    (H : Fin k → SimpleGraph X) (R : Setoid X) : ℕ :=
  if h : (splitColors H R).Nonempty then ((splitColors H R).min' h).val else k

/-- Genuine earlier-color native spanning trees in a full edge coloring. -/
def earlierColorTrees (G : Graph V E) {k : ℕ} (color : E → Fin (k+1)) : Prop :=
  ∀ c : Fin k,(∀ q∈(G.restrict {x | color x=c.castSucc}).edgeSet,
    (G.restrict {x | color x=c.castSucc}).IsBridge q) ∧
    (G.restrict {x | color x=c.castSucc}).toSimpleGraph.Connected

/-- The source's finite refinement signature: actual ordered-pair partition
size first, then actual least-color priority, compared from the earliest stage.
It is computed from the real graph and coloring, not supplied as an oracle. -/
noncomputable def nativeRefinementSignature (G : Graph V E) [Fintype G.vertexSet]
    {k : ℕ} (N : ℕ) (color : E → Fin (k+1)) :
    Lex (Fin (N+1) → Lex (ℕ×ℕ)) :=
  toLex (fun i =>
    let H : Fin (k+1) → SimpleGraph G.vertexSet :=
      fun c => (G.restrict {e | color e=c}).toSimpleGraph
    let R := (refinementStep H)^[i.val] ⊤
    toLex ((relatedPairs R).card,refinementPriority H R))

/-- The finite set of genuine colored decompositions has an actual maximal
refinement signature. The supplied initial decomposition is only the explicit
inductive seed; the optimizer is constructed over all finite colorings. -/
theorem exists_maximal_native_decomposition (G : Graph V E) [Fintype G.vertexSet]
    [Fintype E] {k : ℕ} (N : ℕ) (seed : E → Fin (k+1))
    (hseed : earlierColorTrees G seed) :
    ∃ color : E → Fin (k+1),earlierColorTrees G color ∧
      ∀ other : E → Fin (k+1),earlierColorTrees G other →
        nativeRefinementSignature G N other≤nativeRefinementSignature G N color := by
  classical
  let S : Finset (E → Fin (k+1)) := univ.filter (earlierColorTrees G)
  have hmem : seed∈S := mem_filter.mpr ⟨mem_univ _,hseed⟩
  obtain ⟨color,hcolor,hmax⟩ := S.exists_max_image (nativeRefinementSignature G N) ⟨seed,hmem⟩
  refine ⟨color,(mem_filter.mp hcolor).2,?_⟩
  intro other hother
  exact hmax other (mem_filter.mpr ⟨mem_univ _,hother⟩)

/-- A strict increase at the first changed actual refinement stage gives the
strict lexicographic improvement used to contradict maximality. -/
theorem native_signature_lt_of_stage (G : Graph V E) [Fintype G.vertexSet]
    {k N : ℕ} (color other : E → Fin (k+1)) (i : Fin (N+1))
    (hprefix : ∀ j : Fin (N+1),j < i →
      ofLex (nativeRefinementSignature G N color) j=
        ofLex (nativeRefinementSignature G N other) j)
    (hstage : ofLex (nativeRefinementSignature G N color) i<
      ofLex (nativeRefinementSignature G N other) i) :
    nativeRefinementSignature G N color<nativeRefinementSignature G N other := by
  exact ⟨i,hprefix,hstage⟩
end LightEFTSpanners.MultigraphCuts
