import LightEFTSpanners.SampledHostExtremal

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners
variable {V W J : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

/-- The actual accepted-host history has a bounded assigned weight. Its
probability lower bound and an extremal retained sample are both constructed. -/
theorem assigned_host_extremal_bound (j : V ↪ W) (T : SimpleGraph V) (hT : T.IsTree)
    (Q : Finset (Sym2 W)) (w : Sym2 W → ℝ) (eps : ℝ) (k f h : ℕ)
    (hk : 0<k) (heps : 0<eps) (hf : 0<f)
    (eligible : Sym2 W → Finset J) (host : J → Finset (Sym2 W))
    (a : J) (hhost : host a=(T.map j).edgeFinset) (hTQ : host a⊆Q)
    (rs : List (Sym2 W × Finset J))
    (hs : (rs.map Prod.fst).Pairwise (fun e d => w d≤w e))
    (hn : (rs.map Prod.fst).Nodup) (hdis : ∀ e∈rs.map Prod.fst,e∉Q)
    (hdiag : ∀ e∈rs.map Prod.fst,¬e.IsDiag)
    (himage : ∀ e A,(e,A)∈rs → a∈A → ∃ d,j.sym2Map d=e)
    (hw : ∀ e∈Q∪(rs.map Prod.fst).toFinset,0<w e)
    (hgood : ApprovedHistory Q w ((1+eps)*(2*k-1)) f h eligible host rs) :
    assignedWeight w a rs≤32*(f:ℝ)*
      extremalLightness (Fintype.card W) ((1+eps)*(2*k-1)+1)*totalWeight (T.map j) w := by
  obtain ⟨S,_,hS⟩ := exists_heavy_retained_host_sample Q w ((1+eps)*(2*k-1)) f h
    eligible host rs a hf hTQ hn hdis
    (fun e he => (hw e (mem_union_right _ (List.mem_toFinset.mpr he))).le) hgood
  rw [hhost] at hS
  have hp := retained_host_extremal_bound j T hT w eps k hk heps a S rs hs hn
    (fun e he hmem => hdis e he (hTQ (hhost.symm ▸ hmem))) hdiag himage
    (fun e he => hw e (mem_union.mp he |>.elim
      (fun he => mem_union_left _ (hTQ (hhost.symm ▸ he))) (mem_union_right _)))
  have hh := (div_le_iff₀ (show (0:ℝ)<8*(f:ℝ) by positivity)).mp (hS.trans hp)
  nlinarith
end LightEFTSpanners.SampledGreedy
