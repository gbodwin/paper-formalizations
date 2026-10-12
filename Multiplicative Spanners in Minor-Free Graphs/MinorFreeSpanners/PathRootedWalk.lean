import MinorFreeSpanners.WeightedPathSplit
import MinorFreeSpanners.RootedBridgeWalk

/-! Actual original-host radial walks for every old branch lying on a
specified coarse simple path. The node-mass certificate pays the connectors. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
namespace ClusterFamily
variable {I V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem path_to_start (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (H : SimpleGraph I) (d : I → ℝ) {x y : I}
    (p : H.Walk x y) (hp : p.IsPath) (hd : ∀ i∈p.support,0≤d i+1)
    (hdiam : ∀ i a,a∈C.branch i → ∀ b,b∈C.branch i →
      ∃ q : A.Walk a b,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i)
    (hbridge : ∀ i j,H.Adj i j → ∃ a∈C.branch i,∃ b∈C.branch j,
      ∃ _hab : G.Adj a b,w s(a,b)≤1)
    {i : I} (hi : i∈p.support) {a z : V} (ha : a∈C.branch i) (hz : z∈C.branch x) :
    ∃ q : G.Walk a z,(∀ v∈q.support,∃ j∈p.support,v∈C.branch j) ∧
      walkWeight w q≤pathMass (fun j => d j+1) p-1 := by
  classical
  let q := p.takeUntil i hi
  have hq := hp.takeUntil hi
  have hqs : ∀ j∈q.reverse.support,j∈p.support := by
    intro j hj
    exact p.support_takeUntil_subset_support hi (by simpa [q] using hj)
  obtain ⟨r,hrs,hrw⟩ := C.lift_path_variable hA H d hdiam hbridge q.reverse hq.reverse
    {v | ∃ j∈p.support,v∈C.branch j} (fun j hj v hv => ⟨j,hqs j hj,hv⟩) ha hz
  have hm := pathMass_takeUntil_le (fun j => d j+1) p hi hd
  change pathMass (fun j => d j+1) q≤_ at hm
  rw [pathMass_add_one d q hq] at hm
  simp only [pathMass_reverse,Walk.length_reverse] at hrw
  exact ⟨r,hrs,by linarith⟩

end ClusterFamily
end MinorFreeSpanners
