import LightEFTSpanners.NativeSignatureStages

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}

/-- If a competing coloring preserves every old within-stage colored
connection but cannot improve the actual finite signature, both genuine
refinement sequences and their least-color priorities coincide through the
entire chosen horizon. This proves prefix rigidity from maximality rather
than assuming equality of the new refinement process. -/
theorem native_refinement_rigidity (G : Graph V E) [Fintype G.vertexSet]
    {k N : ℕ} (color other : E → Fin (k+1))
    (hmax : nativeRefinementSignature G N other≤nativeRefinementSignature G N color)
    (hpres : ∀ i≤N,∀ c : Fin (k+1),∀ a b : G.vertexSet,
      (blockGraph (G.restrict {e | color e=c}).toSimpleGraph (nativePartitionAt G color i)).Reachable a b →
      (blockGraph (G.restrict {e | other e=c}).toSimpleGraph (nativePartitionAt G color i)).Reachable a b) :
    ∀ i≤N,nativePartitionAt G color i=nativePartitionAt G other i ∧
      nativePriorityAt G color i=nativePriorityAt G other i := by
  classical
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hiN
    let idx : Fin (N+1) := ⟨i,by omega⟩
    have hpref : ∀ j : Fin (N+1),j < idx →
        ofLex (nativeRefinementSignature G N color) j=
          ofLex (nativeRefinementSignature G N other) j := by
      intro j hj
      have hjlt : j.val < i := hj
      obtain ⟨hpart,hpri⟩ := ih j.val hjlt (by omega)
      simp only [native_signature_eval,hpart,hpri]
    have hcomp (j : ℕ) (hj : j≤N) (c : Fin (k+1)) :
        componentRefinement (G.restrict {e | color e=c}).toSimpleGraph (nativePartitionAt G color j)≤
          componentRefinement (G.restrict {e | other e=c}).toSimpleGraph (nativePartitionAt G color j) :=
      componentRefinement_le_of_routes _ _ _ (hpres j hj c)
    have hpartle : nativePartitionAt G color i≤nativePartitionAt G other i := by
      cases i with
      | zero => exact le_rfl
      | succ j =>
        obtain ⟨hpart,hpri⟩ := ih j (by omega) (by omega)
        rw [nativePartitionAt_succ,nativePartitionAt_succ,←hpart]
        apply refinementStep_le_of_priority_eq _ _ _ (hcomp j (by omega))
        have hpri' := hpri
        unfold nativePriorityAt at hpri'
        simpa only [←hpart] using hpri'
    have hpart : nativePartitionAt G color i=nativePartitionAt G other i := by
      by_contra hne
      have hlt := lt_of_le_of_ne hpartle hne
      exact (not_lt_of_ge hmax) (native_signature_lt_of_partition G color other idx hpref hlt)
    have hprile : nativePriorityAt G color i≤nativePriorityAt G other i := by
      unfold nativePriorityAt
      rw [←hpart]
      exact refinementPriority_le_of_components_le _ _ _ (hcomp i hiN)
    have hpri : nativePriorityAt G color i=nativePriorityAt G other i := by
      by_contra hne
      have hlt := lt_of_le_of_ne hprile hne
      exact (not_lt_of_ge hmax) (native_signature_lt_of_priority G color other idx hpref hpart hlt)
    exact ⟨hpart,hpri⟩
/-- A concrete strict coarsening of the actual selected-color components,
combined with preservation of all old within-stage colored routes, forces a
strict improvement of the real finite signature. No progress estimate or
unchanged-new-prefix premise is assumed. -/
theorem native_signature_improves_of_selected_coarsening (G : Graph V E)
    [Fintype G.vertexSet] {k N : ℕ} (color other : E → Fin (k+1))
    (hpres : ∀ i≤N,∀ c : Fin (k+1),∀ a b : G.vertexSet,
      (blockGraph (G.restrict {e | color e=c}).toSimpleGraph (nativePartitionAt G color i)).Reachable a b →
      (blockGraph (G.restrict {e | other e=c}).toSimpleGraph (nativePartitionAt G color i)).Reachable a b)
    (m : ℕ) (hm : m<N) (c : Fin (k+1))
    (hc : nativePriorityAt G color m=c.val)
    (hstrict : componentRefinement (G.restrict {e | color e=c}).toSimpleGraph (nativePartitionAt G color m)<
      componentRefinement (G.restrict {e | other e=c}).toSimpleGraph (nativePartitionAt G color m)) :
    nativeRefinementSignature G N color<nativeRefinementSignature G N other := by
  apply lt_of_not_ge
  intro hmax
  have hr := native_refinement_rigidity G color other hmax hpres
  obtain ⟨hpart,hpri⟩ := hr m (by omega)
  have hnext := (hr (m+1) (by omega)).1
  have hold := refinementStep_eq_of_priority
    (fun c : Fin (k+1) => (G.restrict {e | color e=c}).toSimpleGraph) (nativePartitionAt G color m) c (by exact hc)
  have hother : refinementPriority (fun c => (G.restrict {e | other e=c}).toSimpleGraph)
      (nativePartitionAt G color m)=c.val := by
    have hh : nativePriorityAt G other m=c.val := hpri.symm.trans hc
    unfold nativePriorityAt at hh
    simpa only [←hpart] using hh
  have hnew := refinementStep_eq_of_priority
    (fun c : Fin (k+1) => (G.restrict {e | other e=c}).toSimpleGraph) (nativePartitionAt G color m) c hother
  rw [nativePartitionAt_succ,nativePartitionAt_succ,←hpart,hold,hnew] at hnext
  exact hstrict.ne hnext
end LightEFTSpanners.MultigraphCuts
