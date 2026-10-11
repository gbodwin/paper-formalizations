import MinorFreeSpanners.ConnectedSetUnitCredits

/-! Actual initial unit-edge clusters, paid once from their own original
internal edges. No initial partition or connected-core family is supplied. -/
namespace MinorFreeSpanners
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

 theorem exists_initial_unit_clusters {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ)
    (hw : ∀ e∈G.edgeSet, w e=1) (k : ℕ) (hk : 0<k)
    (hkN : k≤Fintype.card V) (c : ℝ) (hc : 0≤c) :
    ∃ P : Finset (Finset V), ∃ B : {S // S∈P} → Finset V,
    ∃ C : ClusterFamily (I := {S // S∈P}) G w (4*k),
      (∀ S, C.branch S=(B S:Set V)) ∧
      (∀ v : V, ∃ S, v∈B S) ∧
      (∀ S, k≤(B S).card) ∧
      (∀ S, ∀ x∈B S, ∀ y∈B S, ∃ p : G.Walk x y,
        (∀ z∈p.support, z∈B S) ∧
        walkWeight w p ≤ (min ((B S).card-1) (4*k) : ℕ)) ∧
      (∀ S, c*max ((k-1:ℕ):ℝ) ((min ((B S).card-1) (4*k):ℕ):ℝ) ≤
        c*(internalEdges G (B S)).card) ∧
      (∑ S, c*(internalEdges G (B S)).card) ≤ c*G.edgeFinset.card := by
  classical
  obtain ⟨P,B,hcore,hdis,hcover,hpaths⟩ := exists_initial_connected_partition G hG k hk hkN
  have hsize (S : {S // S∈P}) : k≤(B S).card := by
    rw [← (hcore S).1]
    exact Finset.card_le_card (hcore S).2
  have hne (S : {S // S∈P}) : (B S).Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hk (hsize S))
  have hconn (S : {S // S∈P}) : ConnectedWithin G (B S) := by
    intro x hx y hy
    obtain ⟨p,hp,_⟩ := hpaths S x hx y hy
    exact ⟨p,hp⟩
  have hshort (S : {S // S∈P}) (x : V) (hx : x∈B S) (y : V) (hy : y∈B S) :
      ∃ p : G.Walk x y, (∀ z∈p.support, z∈B S) ∧
        walkWeight w p ≤ (min ((B S).card-1) (4*k) : ℕ) := by
    obtain ⟨p,hp,hl⟩ := hpaths S x hx y hy
    exact unit_short_walk w hw (B S) (4*k) p hp hl
  let C : ClusterFamily (I := {S // S∈P}) G w (4*k) := {
    branch := fun S => (B S:Set V)
    nonempty := fun S => hne S
    disjoint := fun S T hne => Finset.disjoint_coe.mpr (hdis S T hne)
    connected := by
      intro S x hx y hy
      obtain ⟨p,hp,hl⟩ := hshort S x hx y hy
      refine ⟨p,hp,le_trans hl ?_⟩
      exact_mod_cast (min_le_right ((B S).card-1) (4*k)) }
  refine ⟨P,B,C,fun _ => rfl,hcover,hsize,hshort,?_,?_⟩
  · intro S
    have he := internalEdges_card_lower G (B S) (hconn S) (hne S)
    have hk' : k-1≤(internalEdges G (B S)).card := le_trans (Nat.sub_le_sub_right (hsize S) 1) he
    have hd : min ((B S).card-1) (4*k) ≤ (internalEdges G (B S)).card :=
      le_trans (min_le_left _ _) he
    exact mul_le_mul_of_nonneg_left (max_le (by exact_mod_cast hk') (by exact_mod_cast hd)) hc
  · rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hc
    exact_mod_cast internalEdges_total_le G B hdis

end MinorFreeSpanners
