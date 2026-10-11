import MinorFreeSpanners.ClusterWalkLift

/-! Weighted walk lifting with its actual branch-union support retained. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
namespace ClusterFamily
variable {I V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

theorem lift_walk_supported (C : ClusterFamily (I := I) A w D)
    (hA : A ≤ G) (H : SimpleGraph I) (M : ℝ)
    (hbridge : ∀ i j, H.Adj i j → ∃ x∈C.branch i, ∃ y∈C.branch j,
      ∃ _hxy : G.Adj x y, w s(x,y) ≤ M)
    {i j : I} (p : H.Walk i j) (S : Set V)
    (hS : ∀ k∈p.support, C.branch k ⊆ S) {a b : V}
    (ha : a∈C.branch i) (hb : b∈C.branch j) :
    ∃ q : G.Walk a b, (∀ z∈q.support, z∈S) ∧
      walkWeight w q ≤ (p.length : ℝ)*(D+M)+D := by
  induction p generalizing a with
  | nil =>
    obtain ⟨q,hq,hweight⟩ := C.connected _ a ha b hb
    refine ⟨q.mapLe hA,?_,by simpa using hweight⟩
    intro z hz
    exact hS _ (by simp) (hq z (by simpa using hz))
  | @cons i j k hij p ih =>
    obtain ⟨x,hx,y,hy,hxy,hweight⟩ := hbridge i j hij
    obtain ⟨q1,hq1,hw1⟩ := C.connected i a ha x hx
    obtain ⟨q2,hq2,hw2⟩ := ih (fun l hl => hS l (by simp [hl])) hy hb
    refine ⟨(q1.mapLe hA).append (.cons hxy q2),?_,?_⟩
    · intro z hz
      rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
      · exact hS i (by simp) (hq1 z (by simpa using hz))
      · simp only [Walk.support_cons,List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hS i (by simp) hx
        · exact hq2 z hz
    · simp only [walkWeight_append,walkWeight_cons,walkWeight_mapLe,
        Walk.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith

/-- Merge actual old clusters along disjoint index groups. All intrinsic
connecting walks remain inside the resulting union branch. -/
noncomputable def merge {J : Type*} (C : ClusterFamily (I := I) A w D)
    (hA : A ≤ G) (H : SimpleGraph I) (M : ℝ) (t : ℕ)
    (hDM : 0 ≤ D+M)
    (hbridge : ∀ i j, H.Adj i j → ∃ x∈C.branch i, ∃ y∈C.branch j,
      ∃ _hxy : G.Adj x y, w s(x,y) ≤ M)
    (T : J → Set I) (hne : ∀ j, (T j).Nonempty)
    (hdis : ∀ j k, j≠k → Disjoint (T j) (T k))
    (hwalk : ∀ j i, i∈T j → ∀ k, k∈T j →
      ∃ p : H.Walk i k, (∀ l∈p.support, l∈T j) ∧ p.length ≤ t) :
    ClusterFamily (I := J) G w ((t:ℝ)*(D+M)+D) where
  branch j := {x | ∃ i∈T j, x∈C.branch i}
  nonempty := by
    intro j
    obtain ⟨i,hi⟩ := hne j
    obtain ⟨x,hx⟩ := C.nonempty i
    exact ⟨x,i,hi,hx⟩
  disjoint := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    rintro x ⟨i,hi,hxi⟩ ⟨l,hl,hxl⟩
    have he : i=l := by
      by_contra hn
      exact Set.disjoint_left.mp (C.disjoint i l hn) hxi hxl
    subst l
    exact Set.disjoint_left.mp (hdis j k hjk) hi hl
  connected := by
    rintro j x ⟨i,hi,hxi⟩ y ⟨k,hk,hyk⟩
    obtain ⟨p,hp,hlen⟩ := hwalk j i hi k hk
    obtain ⟨r,hr,hw⟩ := C.lift_walk_supported hA H M hbridge p
      {x | ∃ l∈T j, x∈C.branch l} (fun l hl z hz => ⟨l,hp l hl,hz⟩) hxi hyk
    refine ⟨r,hr,hw.trans ?_⟩
    have hh : (p.length:ℝ) ≤ t := by exact_mod_cast hlen
    have hm := mul_le_mul_of_nonneg_right hh hDM
    linarith

end ClusterFamily
end MinorFreeSpanners
