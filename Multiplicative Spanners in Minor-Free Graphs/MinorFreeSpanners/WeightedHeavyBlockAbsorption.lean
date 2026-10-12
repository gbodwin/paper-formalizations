import MinorFreeSpanners.RootedHeavyFamilyWalks

/-! A finite actual family of small blocks is absorbed through its selected
original heavy edges. Two internally chosen blocks reserve the new diameter;
released block credit and bounded old-root slack pay every old-label allocation.
No credit from the selected heavy edges is counted as new unit-tree credit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem weighted_heavy_block_absorption {V J : Type*} {G : SimpleGraph V}
    (w : Sym2 V → ℝ) (F : Finset J) (root : Set V) (block : J → Set V)
    (source target : J → V) (radius credit : J → ℝ) (size : J → ℕ)
    (R K M c a spare future : ℝ) (N : ℕ)
    (hR : 0≤R) (hK : 0≤K) (hM : 0≤M) (ha : 0≤a)
    (hs : ∀ j∈F,source j∈root) (ht : ∀ j∈F,target j∈block j)
    (hedge : ∀ j∈F,G.Adj (source j) (target j))
    (hweight : ∀ j∈F,w s(source j,target j)≤M)
    (hroot : ∀ x∈root,∀ y∈root,∃ p : G.Walk x y,
      (∀ z∈p.support,z∈root) ∧ walkWeight w p≤R)
    (hblock : ∀ j∈F,∀ x∈block j,∀ y∈block j,∃ p : G.Walk x y,
      (∀ z∈p.support,z∈block j) ∧ walkWeight w p≤radius j)
    (hradius : ∀ j∈F,radius j≤K) (hsize : ∀ j∈F,size j≤N)
    (hintrinsic : ∀ j∈F,c*radius j≤credit j)
    (hrelease : ∀ j∈F,a*size j≤credit j)
    (hbudget : 2*c*M+2*(N:ℝ)*a+future≤spare) :
    ∃ Q : Finset J,∃ newRadius : ℝ,Q⊆F ∧ Q.card≤2 ∧
      R≤newRadius ∧ newRadius≤R+2*M+2*K ∧
      (∀ x∈{x | x∈root ∨ ∃ j∈F,x∈block j},
        ∀ y∈{x | x∈root ∨ ∃ j∈F,x∈block j},∃ p : G.Walk x y,
          (∀ z∈p.support,z∈root ∨ ∃ j∈F,z∈block j) ∧ walkWeight w p≤newRadius) ∧
      c*newRadius+a*(∑ j∈F,(size j:ℝ))+future≤c*R+spare+∑ j∈F,credit j := by
  obtain ⟨Q,hQ,hcard,h0,hbound,hone,htwo⟩ := exists_two_block_radius_reserve F radius K hK hradius
  refine ⟨Q,R+2*M+∑ j∈Q,radius j,hQ,hcard,by linarith,by linarith,?_,?_⟩
  · exact rooted_heavy_family_walks w F root block source target radius R M _
      hR hM h0 hs ht hedge hweight hroot hblock hone htwo
  · exact two_block_absorption_credit F Q radius credit size N R M c a spare future
      ha hQ hcard hsize hintrinsic hrelease hbudget

end MinorFreeSpanners
