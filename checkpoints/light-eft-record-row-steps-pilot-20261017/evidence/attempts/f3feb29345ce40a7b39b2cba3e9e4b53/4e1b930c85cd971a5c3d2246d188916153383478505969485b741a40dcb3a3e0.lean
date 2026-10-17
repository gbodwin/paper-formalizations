import LightEFTSpanners.NativePriorityComparison

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}

noncomputable def nativePartitionAt (G : Graph V E) {k : ℕ}
    (color : E → Fin (k+1)) (i : ℕ) : Setoid G.vertexSet :=
  (refinementStep (fun c => (G.restrict {e | color e=c}).toSimpleGraph))^[i] ⊤

noncomputable def nativePriorityAt (G : Graph V E) {k : ℕ}
    (color : E → Fin (k+1)) (i : ℕ) : ℕ :=
  refinementPriority (fun c => (G.restrict {e | color e=c}).toSimpleGraph)
    (nativePartitionAt G color i)

theorem nativePartitionAt_zero (G : Graph V E) {k : ℕ} (color : E → Fin (k+1)) :
    nativePartitionAt G color 0=⊤ := rfl

theorem nativePartitionAt_succ (G : Graph V E) {k : ℕ} (color : E → Fin (k+1)) (i : ℕ) :
    nativePartitionAt G color (i+1)=
      refinementStep (fun c => (G.restrict {e | color e=c}).toSimpleGraph)
        (nativePartitionAt G color i) := by
  exact Function.iterate_succ_apply' _ _ _

theorem native_signature_eval (G : Graph V E) [Fintype G.vertexSet]
    {k N : ℕ} (color : E → Fin (k+1)) (i : Fin (N+1)) :
    ofLex (nativeRefinementSignature G N color) i=
      toLex ((relatedPairs (nativePartitionAt G color i.val)).card,nativePriorityAt G color i.val) := rfl

/-- A strict actual partition coarsening at the first changed stage improves
its true signature, independently of that stage's priority. -/
theorem native_signature_lt_of_partition (G : Graph V E) [Fintype G.vertexSet]
    {k N : ℕ} (color other : E → Fin (k+1)) (i : Fin (N+1))
    (hpref : ∀ j : Fin (N+1),j < i →
      ofLex (nativeRefinementSignature G N color) j=
        ofLex (nativeRefinementSignature G N other) j)
    (hpart : nativePartitionAt G color i.val<nativePartitionAt G other i.val) :
    nativeRefinementSignature G N color<nativeRefinementSignature G N other := by
  apply native_signature_lt_of_stage G color other i hpref
  rw [native_signature_eval,native_signature_eval]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (relatedPairs_card_lt hpart))

/-- With the actual partition unchanged, a strict increase in its real
least-color priority improves the same lexicographic signature. -/
theorem native_signature_lt_of_priority (G : Graph V E) [Fintype G.vertexSet]
    {k N : ℕ} (color other : E → Fin (k+1)) (i : Fin (N+1))
    (hpref : ∀ j : Fin (N+1),j < i →
      ofLex (nativeRefinementSignature G N color) j=
        ofLex (nativeRefinementSignature G N other) j)
    (hpart : nativePartitionAt G color i.val=nativePartitionAt G other i.val)
    (hpri : nativePriorityAt G color i.val<nativePriorityAt G other i.val) :
    nativeRefinementSignature G N color<nativeRefinementSignature G N other := by
  apply native_signature_lt_of_stage G color other i hpref
  rw [native_signature_eval,native_signature_eval]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨congrArg (fun R => (relatedPairs R).card) hpart,hpri⟩)
end LightEFTSpanners.MultigraphCuts
