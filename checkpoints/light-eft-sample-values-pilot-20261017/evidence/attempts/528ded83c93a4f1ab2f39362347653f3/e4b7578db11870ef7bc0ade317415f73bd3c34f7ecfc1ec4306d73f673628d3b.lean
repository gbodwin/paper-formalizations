import LightEFTSpanners.HostFamilyBound

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
attribute [local instance] Classical.propDecidable

/-- Assign every non-seed edge to every supplied tree avoiding its blockers.
This is an actual finite assignment; no desired charging inequality is encoded. -/
noncomputable def unblockedAssignments (G Q : SimpleGraph V)
    (B : Sym2 V → Finset (Sym2 V)) (T : I → SimpleGraph V) (i : I) : Finset (Sym2 V) :=
  (G.edgeFinset \ Q.edgeFinset).filter (fun e => Disjoint (B e) (T i).edgeFinset)

/-- A concrete supplied spanning-tree packing suffices for the global coarse
bound. Coverage and blocker avoidance are constructed, not assumed. Existence
of this packing, and general subtree vertex-set transport, remain separate. -/
theorem spanning_packing_lightness {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hQG : Q ≤ G) (hQpos : 0 < totalWeight Q w)
    (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (indices : Finset I) (T : I → SimpleGraph V)
    (htrees : ∀ i∈indices, (T i).IsTree) (htreeQ : ∀ i∈indices, T i ≤ Q)
    (hcount : 2*f+h ≤ indices.card)
    (hcong : ∀ e∈Q.edgeFinset, (hosts indices (fun i => (T i).edgeFinset) e).card ≤ 2)
    (hw : ∀ e∈G.edgeSet, 0 < w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps)
    (hn : 2 ≤ Fintype.card V) (hh : 0<h) :
    totalWeight G w / totalWeight Q w ≤
      1+8*(f:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/h := by
  classical
  have hcongAll (e : Sym2 V) : (hosts indices (fun i => (T i).edgeFinset) e).card ≤ 2 := by
    by_cases he : e∈Q.edgeFinset
    · exact hcong e he
    · have heq : hosts indices (fun i => (T i).edgeFinset) e = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hi,heT⟩ := mem_filter.mp hi
        exact he (edgeFinset_mono (htreeQ i hi) heT)
      simp [heq]
  apply spanning_host_family_bound hQG hQpos hB indices T (unblockedAssignments G Q B T)
    htrees htreeQ
  · intro i _ e he
    exact mem_edgeFinset.mp (mem_sdiff.mp (mem_filter.mp he).1).1
  · intro i _ e he
    exact (mem_sdiff.mp (mem_filter.mp he).1).2
  · intro i _ e he
    exact (mem_filter.mp he).2
  · intro e he
    have hb := two_congestion_hosts indices (fun i => (T i).edgeFinset) (B e) f h
      hcount (hB.capped e) (fun d _ => hcongAll d)
    have heq : hosts indices (unblockedAssignments G Q B T) e =
        indices.filter (fun i => Disjoint (T i).edgeFinset (B e)) := by
      ext i
      simp only [hosts,mem_filter,unblockedAssignments,he,true_and]
      exact and_congr_right (fun _ => disjoint_comm)
    rwa [heq]
  · exact hcong
  · exact hw
  · exact hf
  · exact hk
  · exact heps
  · exact hn
  · exact hh
end LightEFTSpanners
