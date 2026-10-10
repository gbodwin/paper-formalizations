import MinorFreeSpanners.ClusterGraph

namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {I V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

namespace ClusterFamily

/-- An actual walk lift with an explicit additive diameter cost per visited
cluster. A forbidden host edge is excluded from every part of the lift. -/
theorem lift_walk_bounded (C : ClusterFamily (I := I) A w D)
    (hA : A ≤ G) (H : SimpleGraph I) (M : ℝ) (e : Sym2 V)
    (havoid : ∀ {a b : V} (p : A.Walk a b), e ∉ p.edges)
    (hbridge : ∀ i j, H.Adj i j → ∃ x ∈ C.branch i, ∃ y ∈ C.branch j,
      ∃ _hxy : G.Adj x y, w s(x,y) ≤ M ∧ s(x,y) ≠ e)
    {i j : I} (p : H.Walk i j) {a b : V}
    (ha : a ∈ C.branch i) (hb : b ∈ C.branch j) :
    ∃ q : G.Walk a b, e ∉ q.edges ∧
      walkWeight w q ≤ (p.length : ℝ)*(D+M)+D := by
  induction p generalizing a with
  | nil =>
    obtain ⟨q,_,hq⟩ := C.connected _ a ha b hb
    refine ⟨q.mapLe hA,by simpa using havoid q,?_⟩
    simpa using hq
  | @cons i j k hij p ih =>
    obtain ⟨x,hx,y,hy,hxy,hweight,hne⟩ := hbridge i j hij
    obtain ⟨q1,_,hq1⟩ := C.connected i a ha x hx
    obtain ⟨q2,hnot2,hq2⟩ := ih hy hb
    refine ⟨(q1.mapLe hA).append (.cons hxy q2),?_,?_⟩
    · simp only [Walk.edges_append,Walk.edges_cons,Walk.edges_mapLe_eq_edges,
        List.mem_append,List.mem_cons]
      exact fun h => h.elim (havoid q1) (fun h => h.elim (fun he => hne he.symm) hnot2)
    · simp only [walkWeight_append,walkWeight_cons,walkWeight_mapLe,
        Walk.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith

/-- The same lift needs bridge bounds only for edges used by the given walk. -/
theorem lift_walk_bounded_on_edges (C : ClusterFamily (I := I) A w D)
    (hA : A ≤ G) (H : SimpleGraph I) (M : ℝ) (e : Sym2 V)
    (havoid : ∀ {a b : V} (p : A.Walk a b), e ∉ p.edges)
    {i j : I} (p : H.Walk i j)
    (hbridge : ∀ i j, H.Adj i j → s(i,j) ∈ p.edges →
      ∃ x ∈ C.branch i, ∃ y ∈ C.branch j,
        ∃ _hxy : G.Adj x y, w s(x,y) ≤ M ∧ s(x,y) ≠ e) {a b : V}
    (ha : a ∈ C.branch i) (hb : b ∈ C.branch j) :
    ∃ q : G.Walk a b, e ∉ q.edges ∧
      walkWeight w q ≤ (p.length : ℝ)*(D+M)+D := by
  induction p generalizing a with
  | nil =>
    obtain ⟨q,_,hq⟩ := C.connected _ a ha b hb
    refine ⟨q.mapLe hA,by simpa using havoid q,?_⟩
    simpa using hq
  | @cons i j k hij p ih =>
    obtain ⟨x,hx,y,hy,hxy,hweight,hne⟩ := hbridge i j hij (by simp)
    obtain ⟨q1,_,hq1⟩ := C.connected i a ha x hx
    obtain ⟨q2,hnot2,hq2⟩ := ih (fun u v huv he => hbridge u v huv (by simp [he])) hy hb
    refine ⟨(q1.mapLe hA).append (.cons hxy q2),?_,?_⟩
    · simp only [Walk.edges_append,Walk.edges_cons,Walk.edges_mapLe_eq_edges,
        List.mem_append,List.mem_cons]
      exact fun h => h.elim (havoid q1) (fun h => h.elim (fun he => hne he.symm) hnot2)
    · simp only [walkWeight_append,walkWeight_cons,walkWeight_mapLe,
        Walk.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith

end ClusterFamily
end MinorFreeSpanners
