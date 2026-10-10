import MinorFreeSpanners.RobustCoreDeletion
import MinorFreeSpanners.SmallConnectedCover

/-! An actual connected dominating branch avoiding each small deleted set. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
attribute [local instance] Classical.propDecidable

theorem exists_residual_connected_cover (G : SimpleGraph V) (D : ℕ) (hD : 0 < D)
    (hsize : Fintype.card V ≤ 12*D) (hdeg : ∀ x, 4*D ≤ G.degree x)
    (hrob : DeletionConnected G (2*D)) (S : Finset V) (hS : S.card ≤ D) :
    ∃ C : Finset V, C.Nonempty ∧ Disjoint C S ∧
      C.card ≤ 48*(Nat.log 2 (Fintype.card V)+1) ∧
      (∀ x, x ∉ S → ∃ v ∈ C, G.Adj v x) ∧
      ∀ x ∈ C, ∀ y ∈ C, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ C := by
  classical
  let A : Finset V := Finset.univ \ S
  let H := G.induce (A:Set V)
  obtain ⟨hconn,hAsize,hAdeg⟩ := robust_core_survives G D hD hsize hdeg hrob S hS
  obtain ⟨B,hB,hcard,hdom,hpaths⟩ := exists_small_connected_dominating_set
    H (3*D) (by omega) hconn hAsize hAdeg
  let C : Finset V := B.image Subtype.val
  have hmap (x : A) (hx : x ∈ B) : x.val ∈ C := Finset.mem_image.mpr ⟨x,hx,rfl⟩
  refine ⟨C,hB.image _,?_,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hxS
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_sdiff.mp v.property).2 hxS
  · have hAcard : Fintype.card (A:Set V) ≤ Fintype.card V :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have hlog := Nat.log_mono_right (b := 2) hAcard
    exact (Finset.card_image_le.trans hcard).trans (by omega)
  · intro x hx
    let a : A := ⟨x,by simp [A,hx]⟩
    obtain ⟨v,hv,hvx⟩ := hdom a
    exact ⟨v.val,hmap v hv,hvx⟩
  · intro x hx y hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨p,hp⟩ := hpaths u hu v hv
    let f : H →g G := ⟨Subtype.val,fun h => h⟩
    refine ⟨p.map f,?_⟩
    intro z hz
    have hz' : z ∈ p.support.map f := by
      simpa only [Walk.support_map] using hz
    obtain ⟨w,hw,he⟩ := List.mem_map.mp hz'
    have he' : w.val = z := (show f w = w.val from rfl).symm.trans he
    rw [← he']
    exact hmap w (hp w hw)

end MinorFreeSpanners
