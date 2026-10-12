import MinorFreeSpanners.ForestPathMass
import MinorFreeSpanners.ClusterMergeWalk

/-! Effective path mass pays the actual internal cluster walks and original
unit connector edges. Each simple-path cluster is charged exactly once. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
namespace ClusterFamily
variable {I V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem lift_path_variable (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (H : SimpleGraph I) (d : I → ℝ)
    (hdiam : ∀ i x, x∈C.branch i → ∀ y, y∈C.branch i →
      ∃ q : A.Walk x y, (∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i)
    (hbridge : ∀ i j,H.Adj i j → ∃ x∈C.branch i,∃ y∈C.branch j,
      ∃ _hxy : G.Adj x y,w s(x,y)≤1)
    {i j : I} (p : H.Walk i j) (hp : p.IsPath) (S : Set V)
    (hS : ∀ k∈p.support,C.branch k⊆S) {a b : V}
    (ha : a∈C.branch i) (hb : b∈C.branch j) :
    ∃ q : G.Walk a b,(∀ z∈q.support,z∈S) ∧
      walkWeight w q≤pathMass d p+p.length := by
  classical
  induction p generalizing a with
  | nil =>
    obtain ⟨q,hq,hweight⟩ := hdiam _ a ha b hb
    refine ⟨q.mapLe hA,?_,?_⟩
    · intro z hz
      exact hS _ (by simp) (hq z (by simpa using hz))
    · simpa [pathMass] using hweight
  | @cons i j k hij p ih =>
    have hpp := Walk.cons_isPath_iff hij p |>.mp hp
    obtain ⟨x,hx,y,hy,hxy,hweight⟩ := hbridge i j hij
    obtain ⟨q1,hq1,hw1⟩ := hdiam i a ha x hx
    obtain ⟨q2,hq2,hw2⟩ := ih hpp.1 (fun l hl => hS l (by simp [hl])) hy hb
    refine ⟨(q1.mapLe hA).append (.cons hxy q2),?_,?_⟩
    · intro z hz
      rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
      · exact hS i (by simp) (hq1 z (by simpa using hz))
      · simp only [Walk.support_cons,List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hS i (by simp) hx
        · exact hq2 z hz
    · have heq : pathMass d (.cons hij p)=d i+pathMass d p := by
        simp [pathMass,Walk.support_cons,hpp.2]
      simp only [walkWeight_append,walkWeight_cons,walkWeight_mapLe,
        Walk.length_cons,Nat.cast_add,Nat.cast_one,heq]
      linarith

 theorem lift_path_twice_mass (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (H : SimpleGraph I) (d : I → ℝ)
    (hdiam : ∀ i x, x∈C.branch i → ∀ y, y∈C.branch i →
      ∃ q : A.Walk x y, (∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i)
    (hbridge : ∀ i j,H.Adj i j → ∃ x∈C.branch i,∃ y∈C.branch j,
      ∃ _hxy : G.Adj x y,w s(x,y)≤1)
    {i j : I} (p : H.Walk i j) (hp : p.IsPath)
    (hd : ∀ k∈p.support,1≤d k) (S : Set V)
    (hS : ∀ k∈p.support,C.branch k⊆S) {a b : V}
    (ha : a∈C.branch i) (hb : b∈C.branch j) :
    ∃ q : G.Walk a b,(∀ z∈q.support,z∈S) ∧ walkWeight w q≤2*pathMass d p := by
  classical
  obtain ⟨q,hq,hw⟩ := C.lift_path_variable hA H d hdiam hbridge p hp S hS ha hb
  have hmass : (p.length:ℝ)+1≤pathMass d p := by
    have hs : (∑ _k∈p.support.toFinset,(1:ℝ))≤pathMass d p :=
      Finset.sum_le_sum (fun k hk => hd k (List.mem_toFinset.mp hk))
    simpa [pathMass,List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support] using hs
  exact ⟨q,hq,by linarith⟩

end ClusterFamily
end MinorFreeSpanners
