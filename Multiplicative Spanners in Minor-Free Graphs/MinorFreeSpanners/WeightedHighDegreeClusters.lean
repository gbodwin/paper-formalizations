import MinorFreeSpanners.RadiusTwoClusterWalks
import MinorFreeSpanners.ClusterMergeWalk

/-! An actual high-degree level-clustering construction on the genuine cluster
quotient. Centers, index groups, host unions and connecting walks are selected
internally. This is one hierarchy phase; no credit or whole-lightness bound is
inferred from it. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

theorem exists_weighted_high_degree_clusters {I V : Type*} [Fintype I]
    {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D M : ℝ}
    (C : ClusterFamily (I := I) A w D) (hA : A ≤ G) (hB : B ≤ G)
    (hDM : 0 ≤ D+M) (hweight : ∀ e∈B.edgeSet, w e ≤ M) (q : ℕ) :
    ∃ centers : Finset I, ∃ groups : I → Finset I,
    ∃ F : ClusterFamily (I := {c // c∈centers}) G w (4*(D+M)+D),
      (∀ c∈centers, q ≤ (C.graph B).degree c) ∧
      (∀ c∈centers, closedNeighborhood (C.graph B) c ⊆ groups c) ∧
      (∀ c∈centers, q+1 ≤ (groups c).card) ∧
      (∀ c∈centers, ∀ d∈centers, c≠d → Disjoint (groups c) (groups d)) ∧
      (∀ c : {c // c∈centers},
        F.branch c = {x | ∃ i∈groups c.val, x∈C.branch i}) ∧
      (∀ i, i∉centers.biUnion groups → (C.graph B).degree i < q) := by
  classical
  obtain ⟨centers,groups,hhigh,hcore,hsize,hdis,hwalk,hlow⟩ :=
    exists_high_degree_clustering (C.graph B) q
  have hbridge : ∀ i j, (C.graph B).Adj i j →
      ∃ x∈C.branch i, ∃ y∈C.branch j, ∃ _hxy : G.Adj x y, w s(x,y) ≤ M := by
    rintro i j ⟨_,x,hx,y,hy,hxy⟩
    exact ⟨x,hx,y,hy,hB hxy,hweight _ hxy⟩
  let T (c : {c // c∈centers}) : Set I := groups c.val
  have hne (c : {c // c∈centers}) : (T c).Nonempty := by
    exact ⟨c.val,hcore c.val c.property (by simp)⟩
  have hd (c d : {c // c∈centers}) (hcd : c≠d) : Disjoint (T c) (T d) := by
    exact Finset.disjoint_coe.mpr (hdis c.val c.property d.val d.property
      (fun he => hcd (Subtype.ext he)))
  have hw (c : {c // c∈centers}) (i : I) (hi : i∈T c)
      (j : I) (hj : j∈T c) :
      ∃ p : (C.graph B).Walk i j, (∀ l∈p.support, l∈T c) ∧ p.length ≤ 4 :=
    hwalk c.val c.property i hi j hj
  let F := C.merge hA (C.graph B) M 4 hDM hbridge T hne hd hw
  exact ⟨centers,groups,F,hhigh,hcore,hsize,hdis,fun _ => rfl,hlow⟩

end MinorFreeSpanners
