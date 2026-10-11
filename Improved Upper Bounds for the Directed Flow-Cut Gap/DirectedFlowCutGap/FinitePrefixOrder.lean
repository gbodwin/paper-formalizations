import DirectedFlowCutGap.FiniteBinaryPrefix

/-! The fixed materialization program stores the requested prefix in reverse
order. Independent identical fair bits have that same reversed-list law.
This states distributional equality explicitly; no individual stream is
silently reordered in a same-stream execution theorem. -/
namespace DirectedFlowCutGap.FinitePrefixOrder
noncomputable section
open FiniteBinaryPrefix

private theorem snoc_law (q : ℕ) :
    (PMF.uniformOfFintype (Fin 2)).bind (fun b =>
      (prefixLaw q).map (fun xs => xs++[b])) = prefixLaw (q+1) := by
  induction q with
  | zero => simp only [prefixLaw,PMF.pure_map,List.nil_append]
  | succ q ih =>
      simp only [prefixLaw,PMF.map_bind,PMF.map_comp,Function.comp_def,List.cons_append]
      rw [PMF.bind_comm]
      congr 1
      funext c
      have h := congrArg (fun p : PMF (List (Fin 2)) => p.map (List.cons c)) ih
      simpa only [PMF.map_bind,PMF.map_comp,Function.comp_def,prefixLaw] using h

theorem reversal_law (q : ℕ) : (prefixLaw q).map List.reverse=prefixLaw q := by
  induction q with
  | zero => simp only [prefixLaw,PMF.pure_map,List.reverse_nil]
  | succ q ih =>
      rw [prefixLaw,PMF.map_bind]
      have he : ∀ b : Fin 2,
          ((prefixLaw q).map (List.cons b)).map List.reverse=
            ((prefixLaw q).map List.reverse).map (fun xs => xs++[b]) := by
        intro b
        simp only [PMF.map_comp,Function.comp_def,List.reverse_cons]
      simp_rw [he,ih]
      exact snoc_law q

/-- Any complete result/ledger observation may use the reversed materialized
prefix with the identical marginal. No independence of record fields is used. -/
theorem observe_reversed {A : Type} (q : ℕ) (observe : List (Fin 2) → A) :
    (prefixLaw q).map (fun xs => observe xs.reverse)=(prefixLaw q).map observe := by
  have h := congrArg (fun p : PMF (List (Fin 2)) => p.map observe) (reversal_law q)
  simpa only [PMF.map_comp,Function.comp_def] using h

end
end DirectedFlowCutGap.FinitePrefixOrder
