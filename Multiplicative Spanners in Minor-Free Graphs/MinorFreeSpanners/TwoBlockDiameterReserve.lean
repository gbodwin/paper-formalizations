import MinorFreeSpanners.RootedBridgeWalk
import Mathlib.Data.Finset.Powerset

/-! At most two actual block radii suffice for every cross-block route.
The maximizing reserve is selected from the finite original block family,
including its empty and singleton cases; no reserve oracle is assumed. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable

 theorem exists_two_block_radius_reserve {J : Type*} (F : Finset J) (radius : J → ℝ)
    (K : ℝ) (hK : 0≤K) (hr : ∀ j∈F,radius j≤K) :
    ∃ Q : Finset J,Q⊆F ∧ Q.card≤2 ∧ 0≤∑ j∈Q,radius j ∧
      (∑ j∈Q,radius j)≤2*K ∧
      (∀ j∈F,radius j≤∑ k∈Q,radius k) ∧
      (∀ i∈F,∀ j∈F,i≠j → radius i+radius j≤∑ k∈Q,radius k) := by
  classical
  let candidates := F.powerset.filter fun S => S.card≤2
  have h0 : ∅∈candidates := by simp [candidates]
  obtain ⟨Q,hQ,hmax⟩ := Finset.exists_max_image candidates (fun S => ∑ j∈S,radius j) ⟨∅,h0⟩
  obtain ⟨hQF,hcard⟩ := Finset.mem_filter.mp hQ
  have hsub : Q⊆F := Finset.mem_powerset.mp hQF
  refine ⟨Q,hsub,hcard,?_,?_,?_,?_⟩
  · simpa using hmax ∅ h0
  · have hsum : (∑ j∈Q,radius j)≤Q.card*K := by
      calc
        _ ≤ ∑ _j∈Q,K := Finset.sum_le_sum fun j hj => hr j (hsub hj)
        _ = _ := by simp
    have hcardR : (Q.card:ℝ)≤2 := by exact_mod_cast hcard
    exact hsum.trans (by nlinarith [mul_le_mul_of_nonneg_right hcardR hK])
  · intro j hj
    have hs : {j}∈candidates := by simp [candidates,hj]
    simpa using hmax {j} hs
  · intro i hi j hj hij
    have hs : {i,j}∈candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_,by simp [hij]⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hi
      · have he : k=j := Finset.mem_singleton.mp hk
        exact he.symm ▸ hj
    simpa [hij] using hmax {i,j} hs

 theorem two_block_absorption_credit {J : Type*} (F Q : Finset J)
    (radius credit : J → ℝ) (size : J → ℕ) (N : ℕ)
    (R M c a spare future : ℝ) (ha : 0≤a)
    (hQF : Q⊆F) (hQ : Q.card≤2) (hsize : ∀ j∈F,size j≤N)
    (hintrinsic : ∀ j∈F,c*radius j≤credit j)
    (hrelease : ∀ j∈F,a*size j≤credit j)
    (hbudget : 2*c*M+2*(N:ℝ)*a+future≤spare) :
    c*(R+2*M+∑ j∈Q,radius j)+a*(∑ j∈F,(size j:ℝ))+future≤
      c*R+spare+∑ j∈F,credit j := by
  classical
  have hreserve : c*(∑ j∈Q,radius j)≤∑ j∈Q,credit j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => hintrinsic j (hQF hj)
  have hrel : a*(∑ j∈F\Q,(size j:ℝ))≤∑ j∈F\Q,credit j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => hrelease j (Finset.mem_sdiff.mp hj).1
  have hsz : (∑ j∈Q,(size j:ℝ))≤2*N := by
    have hh : (∑ j∈Q,(size j:ℝ))≤Q.card*N := by
      calc
        _ ≤ ∑ _j∈Q,(N:ℝ) := Finset.sum_le_sum fun j hj => by exact_mod_cast hsize j (hQF hj)
        _ = _ := by simp
    have hcQ : (Q.card:ℝ)≤2 := by exact_mod_cast hQ
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hcQ (Nat.cast_nonneg N)])
  have hsplit := Finset.sum_sdiff (f:=credit) hQF
  have hsplitSize := Finset.sum_sdiff (f:=fun j => (size j:ℝ)) hQF
  nlinarith [mul_le_mul_of_nonneg_left hsz ha]

end MinorFreeSpanners
