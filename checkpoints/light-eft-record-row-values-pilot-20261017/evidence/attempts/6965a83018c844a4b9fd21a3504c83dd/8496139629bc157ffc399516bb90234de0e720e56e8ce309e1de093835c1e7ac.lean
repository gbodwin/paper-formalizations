import LightEFTSpanners.HostGraphSampling

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Restrict blocking pairs to actual candidates in a blocker-disjoint host.
The new cap measures only candidate blockers, not all original faults. -/
theorem BlockingData.local_host {G T : SimpleGraph V} {seed U : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {t : ℝ} {f r : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w t f B) (hTG : T≤G)
    (hTseed : ∀ e∈T.edgeSet,e∈seed) (hUG : ∀ e∈U,e∈G.edgeSet)
    (hUseed : ∀ e∈U,e∉seed) (hhost : ∀ e∈U,Disjoint (B e) T.edgeFinset)
    (hcap : ∀ e∈U,(B e∩U).card≤r) :
    BlockingData (T⊔edgeGraph U) seed w t r (fun e => if e∈U then B e∩U else ∅) := by
  classical
  let X := T⊔edgeGraph U
  have hXG : X≤G := sup_le hTG (by
    intro a b hab
    exact G.mem_edgeSet.mp (hUG _ ((mem_edgeGraph U _).mp ((edgeGraph U).mem_edgeSet.mpr hab)).1))
  have heX (e : Sym2 V) (he : e∈U) : e∈X.edgeSet := by
    change e∈(T⊔edgeGraph U).edgeSet
    rw [edgeSet_sup]
    apply Set.mem_union_right
    exact (mem_edgeGraph U e).mpr ⟨he,G.not_isDiag_of_mem_edgeSet (hUG e he)⟩
  constructor
  · intro e; by_cases he : e∈U <;> simp only [he,ite_true,ite_false,card_empty]
    · exact hcap e he
    · exact Nat.zero_le _
  · intro e d hd
    by_cases he : e∈U
    · exact heX d (mem_inter.mp (by simpa [he] using hd)).2
    · simp [he] at hd
  · intro e d hd
    by_cases he : e∈U
    · exact ⟨heX e he,hUseed e he⟩
    · simp [he] at hd
  · intro e; by_cases he : e∈U <;> simp [he,hB.no_self e]
  · intro a p hp d hd hdn hw
    have old : ∀ e∈p.edges,e∈G.edgeSet := fun e he => edgeSet_mono hXG (p.edges_subset_edgeSet he)
    obtain ⟨e,hep,b,hbp,hbe⟩ := hB.blocks a (p.transfer G old) (hp.transfer old) d
      (by simpa only [Walk.edges_transfer] using hd) hdn (by simpa only [walkWeight_transfer] using hw)
    simp only [Walk.edges_transfer] at hep hbp
    have heU : e∈U := by
      have he := p.edges_subset_edgeSet hep
      rw [edgeSet_sup] at he
      rcases he with heT|heU
      · exact False.elim ((hB.first_edge e b hbe).2 (hTseed e heT))
      · exact ((mem_edgeGraph U e).mp heU).1
    have hbU : b∈U := by
      have hb := p.edges_subset_edgeSet hbp
      rw [edgeSet_sup] at hb
      rcases hb with hbT|hbU
      · exact False.elim (Finset.disjoint_left.mp (hhost e heU) hbe (mem_edgeFinset.mpr hbT))
      · exact ((mem_edgeGraph U b).mp hbU).1
    exact ⟨e,hep,b,hbp,by simp [heU,hbe,hbU]⟩

/-- Actual host candidate weight depends on the local blocker cap r, even
when the global seeded recursion tolerates the larger fault budget f. -/
theorem host_weight_local_cap {G T : SimpleGraph V} {seed U : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {eps : ℝ} {f k r : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w ((1+eps)*(2*k-1)) f B)
    (hT : T.IsTree) (hTG : T≤G) (hTseed : ∀ e∈T.edgeSet,e∈seed)
    (hUG : ∀ e∈U,e∈G.edgeSet) (hUseed : ∀ e∈U,e∉seed)
    (hhost : ∀ e∈U,Disjoint (B e) T.edgeFinset) (hcap : ∀ e∈U,(B e∩U).card≤r)
    (hw : ∀ e∈G.edgeSet,0<w e) (hr : 0<r) (hk : 0<k) (heps : 0<eps)
    (hn : 2≤Fintype.card V) :
    (∑ e∈U,w e) ≤ 4*(r:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))*totalWeight T w := by
  have hXG : T⊔edgeGraph U≤G := sup_le hTG (by
    intro a b hab
    exact G.mem_edgeSet.mp (hUG _ ((mem_edgeGraph U _).mp ((edgeGraph U).mem_edgeSet.mpr hab)).1))
  apply host_candidate_weight_bound (hB.local_host hTG hTseed hUG hUseed hhost hcap)
    hT le_sup_left hTseed
  · intro e he
    rw [edgeSet_sup]
    exact Set.mem_union_right _ ((mem_edgeGraph U e).mpr ⟨he,G.not_isDiag_of_mem_edgeSet (hUG e he)⟩)
  · exact hUseed
  · intro e he
    simp only [he,ite_true]
    exact (hhost e he).mono_left inter_subset_left
  · exact fun e he => hw e (edgeSet_mono hXG he)
  · exact hr
  · exact hk
  · exact heps
  · exact hn
end LightEFTSpanners
