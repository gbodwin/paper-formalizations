import MinorFreeSpanners.WeightedPathSplit

/-! A real coarse path lifts inside the strictly lighter A sup T graph.
Weighted girth therefore lower-bounds its actual effective node mass against
the original heavy edge, without assuming any shortest-path certificate. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
namespace ClusterFamily
variable {I V : Type*} {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem coarse_path_detour_gap (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hT : T≤G) (H : SimpleGraph I) (hH : H≤C.graph T)
    (d : I → ℝ)
    (hdiam : ∀ i a,a∈C.branch i → ∀ b,b∈C.branch i →
      ∃ p : A.Walk a b,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (g ell : ℝ) (hG : WeightedGirthAbove G w g) (hw : ∀ e∈G.edgeSet,0≤w e)
    (hlight : ∀ e∈A.edgeSet,w e<ell) (hunit : ∀ e∈T.edgeSet,w e=1)
    (hell : 1<ell) {x y : I} (p : H.Walk x y) (hp : p.IsPath)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) (hab : G.Adj a b)
    (hheavy : ell≤w s(a,b)) :
    (g-1)*w s(a,b)+1<pathMass (fun i => d i+1) p := by
  classical
  let K := A⊔T
  have hK : K≤G := sup_le hA hT
  have hAK : A≤K := le_sup_left
  have hbridge : ∀ i j,H.Adj i j → ∃ u∈C.branch i,∃ v∈C.branch j,
      ∃ _huv : K.Adj u v,w s(u,v)≤1 := by
    intro i j hij
    obtain ⟨_,u,hu,v,hv,huv⟩ := hH hij
    exact ⟨u,hu,v,hv,Or.inr huv,(hunit _ huv).le⟩
  obtain ⟨q,_,hqw⟩ := C.lift_path_variable hAK H d hdiam hbridge p hp Set.univ
    (fun _ _ => Set.subset_univ _) ha hb
  have hlightK : ∀ e∈K.edgeSet,w e<ell := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      change A.Adj u v ∨ T.Adj u v at he
      rcases he with he|he
      · exact hlight _ he
      · rw [hunit _ he]
        exact hell
  have hnot : s(a,b)∉(q.mapLe hK).edges := by
    simpa using heavy_edge_not_mem hlightK hheavy q
  have hgap := replacement_walk_gap hG hw hab (q.mapLe hK) hnot
  simp only [walkWeight_mapLe] at hgap
  rw [pathMass_add_one d p hp]
  linarith

end ClusterFamily
end MinorFreeSpanners
