import MinorFreeSpanners.RootedBridgeWalk
import MinorFreeSpanners.FourArmCredit

/-! Lift the four selected coarse paths and their one actual heavy connector
to supported walks in the original graph, with a common intrinsic bound. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem arm_to_center (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) {x : I}
    (P : WeightedPathArms H (fun i => d i+1) L (D+1) x)
    (hd : ∀ i∈P.carrier,0≤d i+1)
    (hdiam : ∀ i a,a∈C.branch i → ∀ b,b∈C.branch i →
      ∃ p : A.Walk a b,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (hbridge : ∀ i j,H.Adj i j → ∃ a∈C.branch i,∃ b∈C.branch j,
      ∃ _hab : G.Adj a b,w s(a,b)≤1)
    {i : I} (hi : i∈P.carrier) {a z : V} (ha : a∈C.branch i) (hz : z∈C.branch x) :
    ∃ p : G.Walk a z,(∀ v∈p.support,∃ j∈P.carrier,v∈C.branch j) ∧
      walkWeight w p≤L+D := by
  classical
  obtain ⟨q,hq,hqs,hqm⟩ := P.radial_path hd hi
  have hrev : ∀ j∈q.reverse.support,j∈P.carrier := fun j hj => hqs j (by simpa using hj)
  obtain ⟨p,hps,hpw⟩ := C.lift_path_variable hA H d hdiam hbridge q.reverse hq.reverse
    {v | ∃ j∈P.carrier,v∈C.branch j} (fun j hj v hv => ⟨j,hrev j hj,hv⟩) ha hz
  rw [pathMass_add_one d q hq] at hqm
  simp only [pathMass_reverse,Walk.length_reverse] at hpw
  exact ⟨p,hps,by linarith⟩

 theorem four_arm_walks (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (H : SimpleGraph I) (d : I → ℝ) (L M : ℝ) {x y : I}
    (P : WeightedPathArms H (fun i => d i+1) L (D+1) x)
    (Q : WeightedPathArms H (fun i => d i+1) L (D+1) y)
    (hd : ∀ i∈P.carrier∪Q.carrier,0≤d i+1)
    (hdiam : ∀ i a,a∈C.branch i → ∀ b,b∈C.branch i →
      ∃ p : A.Walk a b,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (hbridge : ∀ i j,H.Adj i j → ∃ a∈C.branch i,∃ b∈C.branch j,
      ∃ _hab : G.Adj a b,w s(a,b)≤1)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) (hab : G.Adj a b)
    (hM : 0≤M) (hweight : w s(a,b)≤M) :
    ∀ u,(∃ i∈P.carrier∪Q.carrier,u∈C.branch i) →
      ∀ v,(∃ i∈P.carrier∪Q.carrier,v∈C.branch i) →
      ∃ p : G.Walk u v,(∀ z∈p.support,∃ i∈P.carrier∪Q.carrier,z∈C.branch i) ∧
        walkWeight w p≤2*(L+D)+M := by
  classical
  let S : Set V := {v | ∃ i∈P.carrier,v∈C.branch i}
  let T : Set V := {v | ∃ i∈Q.carrier,v∈C.branch i}
  have hs : ∀ u∈S,∃ p : G.Walk u a,(∀ z∈p.support,z∈S) ∧ walkWeight w p≤L+D := by
    rintro u ⟨i,hi,hui⟩
    exact C.arm_to_center hA H d L P (fun j hj => hd j (Finset.mem_union_left _ hj))
      hdiam hbridge hi hui ha
  have ht : ∀ u∈T,∃ p : G.Walk u b,(∀ z∈p.support,z∈T) ∧ walkWeight w p≤L+D := by
    rintro u ⟨i,hi,hui⟩
    exact C.arm_to_center hA H d L Q (fun j hj => hd j (Finset.mem_union_right _ hj))
      hdiam hbridge hi hui hb
  have he : S∪T={v | ∃ i∈P.carrier∪Q.carrier,v∈C.branch i} := by
    ext v
    simp only [Set.mem_union,Set.mem_ofPred_eq,S,T,Finset.mem_union]
    aesop
  have h := rooted_sets_bridge w S T hab ⟨x,P.center_mem,ha⟩
    (L+D) M hM hweight hs ht
  simpa only [he,Set.mem_ofPred_eq] using h

end ClusterFamily
end MinorFreeSpanners
