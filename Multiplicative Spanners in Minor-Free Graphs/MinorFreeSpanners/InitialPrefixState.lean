import MinorFreeSpanners.InitialUnitTreePhase
import MinorFreeSpanners.RetainedScaleState
import MinorFreeSpanners.WeightPrefixHost

/-! Construct a finite starting prefix state at every positive integer scale,
paid from disjoint actual initial tree edges. The small-tree case is excluded
only by the explicit scale-versus-tree-size inequality. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem exists_initial_prefix_state {V : Type*} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (hT : T≤G) (hTree : T.IsTree) (hunit : ∀ e∈T.edgeSet,w e=1)
    (b : ℕ) (hb : 0<b) (hsize : b≤T.edgeFinset.card) (c : ℝ) (hc : 0≤c) :
    ∃ S : FiniteScaleState (weightPrefix G w (2*(b:ℝ))) w (200*(b:ℝ)) c (b:ℝ),
      (∑ i,S.credit i)≤c*(T.edgeFinset.card:ℝ) := by
  classical
  have hb1 : (1:ℝ)≤b := by exact_mod_cast hb
  have hprefix : T≤weightPrefix G w (2*(b:ℝ)) := le_weightPrefix hT
    (fun e he => by rw [hunit e he];linarith only [hb1])
  rcases initial_unit_tree_phase T hTree w hunit b hb c hc with hsmall|hlarge
  · omega
  obtain ⟨P,B,C,hbranch,hcover,hcard,hshort,hcredit,htotal⟩ := hlarge
  let J := {S // S∈P}
  let e := Fintype.equivFin J
  let radius : J → ℝ := fun S => ((min ((B S).card-1) (4*(b+1)):ℕ):ℝ)
  let keep : J → ℝ := fun S => c*(internalEdges T (B S)).card
  have hrad1 (S : J) : 1≤radius S := by
    have hs := hcard S
    change (1:ℝ)≤((min ((B S).card-1) (4*(b+1)):ℕ):ℝ)
    exact_mod_cast (show 1≤min ((B S).card-1) (4*(b+1)) by omega)
  have hradcap (S : J) : radius S≤200*(b:ℝ) := by
    have hn := min_le_right ((B S).card-1) (4*(b+1))
    have hr : radius S≤(4*(b+1):ℕ) := by dsimp [radius];exact_mod_cast hn
    push_cast at hr
    linarith only [hr,hb1]
  let F : ClusterFamily (I:=J) (weightPrefix G w (2*(b:ℝ))) w (200*(b:ℝ)) := {
    branch := C.branch
    nonempty := C.nonempty
    disjoint := C.disjoint
    connected := by
      intro S x hx y hy
      obtain ⟨p,hp,hl⟩ := C.connected S x hx y hy
      refine ⟨p.mapLe hprefix,?_,?_⟩
      · simpa using hp
      · rw [walkWeight_mapLe]
        exact hl.trans (by linarith only [hb1]) }
  have hwalk (S : J) (x : V) (hx : x∈F.branch S) (y : V) (hy : y∈F.branch S) :
      ∃ p : (weightPrefix G w (2*(b:ℝ))).Walk x y,
        (∀ z∈p.support,z∈F.branch S) ∧ walkWeight w p≤radius S := by
    have hx' : x∈B S := by change x∈C.branch S at hx;simpa only [hbranch S,Finset.mem_coe] using hx
    have hy' : y∈B S := by change y∈C.branch S at hy;simpa only [hbranch S,Finset.mem_coe] using hy
    obtain ⟨p,hp,hl⟩ := hshort S x hx' y hy'
    refine ⟨p.mapLe hprefix,?_,?_⟩
    · intro z hz
      change z∈C.branch S
      rw [hbranch S]
      exact hp z (by simpa using hz)
    · simpa only [walkWeight_mapLe] using hl
  let result : FiniteScaleState (weightPrefix G w (2*(b:ℝ))) w (200*(b:ℝ)) c (b:ℝ) := {
    count := Fintype.card J
    family := F.reindex e.symm
    cover := by
      intro x
      obtain ⟨S,hS⟩ := hcover x
      refine ⟨e S,?_⟩
      simpa [ClusterFamily.reindex,F,hbranch S] using hS
    radius := radius∘e.symm
    credit := keep∘e.symm
    radius_one := fun i => hrad1 (e.symm i)
    radius_cap := fun i => hradcap (e.symm i)
    intrinsic := fun i => hwalk (e.symm i)
    credit_radius := fun i => (mul_le_mul_of_nonneg_left (le_max_right (b:ℝ) (radius (e.symm i))) hc).trans (hcredit (e.symm i))
    credit_baseline := fun i => (mul_le_mul_of_nonneg_left (le_max_left (b:ℝ) (radius (e.symm i))) hc).trans (hcredit (e.symm i))
    credit_nonnegative := fun _ => mul_nonneg hc (Nat.cast_nonneg _) }
  refine ⟨result,?_⟩
  have hs : (∑ i : Fin (Fintype.card J),keep (e.symm i))=∑ i,keep i := e.symm.sum_comp keep
  change (∑ i : Fin (Fintype.card J),keep (e.symm i))≤_
  rw [hs]
  have he := hTree.card_edgeFinset
  simpa only [←he,Nat.add_sub_cancel,keep] using htotal

end MinorFreeSpanners
