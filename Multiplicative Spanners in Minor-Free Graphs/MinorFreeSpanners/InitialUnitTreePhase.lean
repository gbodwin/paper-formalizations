import MinorFreeSpanners.InitialUnitClusters

/-! Complete unit-tree initialization at an integer scale t. The small-tree
case is explicit; otherwise every actual branch keeps a t-unit reserve and
its intrinsic diameter reserve from disjoint original tree-edge credits. -/
namespace MinorFreeSpanners
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

 theorem initial_unit_tree_phase {V : Type*} [Fintype V]
    (T : SimpleGraph V) (hT : T.IsTree) (w : Sym2 V → ℝ)
    (hw : ∀ e∈T.edgeSet, w e=1) (t : ℕ) (ht : 0<t)
    (c : ℝ) (hc : 0≤c) :
    (T.edgeFinset.card < t ∧ ∀ x y : V, ∃ p : T.Walk x y, walkWeight w p < t) ∨
    (∃ P : Finset (Finset V), ∃ B : {S // S∈P} → Finset V,
    ∃ C : ClusterFamily (I := {S // S∈P}) T w (8*t),
      (∀ S, C.branch S=(B S:Set V)) ∧
      (∀ v : V, ∃ S, v∈B S) ∧
      (∀ S, t+1≤(B S).card) ∧
      (∀ S, ∀ x∈B S, ∀ y∈B S, ∃ p : T.Walk x y,
        (∀ z∈p.support, z∈B S) ∧
        walkWeight w p ≤ (min ((B S).card-1) (4*(t+1)) : ℕ)) ∧
      (∀ S, c*max (t:ℝ) ((min ((B S).card-1) (4*(t+1)):ℕ):ℝ) ≤
        c*(internalEdges T (B S)).card) ∧
      (∑ S, c*(internalEdges T (B S)).card) ≤ c*(Fintype.card V-1:ℕ)) := by
  classical
  have hcard := hT.card_edgeFinset
  by_cases hsmall : Fintype.card V≤t
  · left
    refine ⟨by omega,?_⟩
    intro x y
    obtain ⟨p,hp,hl⟩ := (show ConnectedWithin T Finset.univ from
      fun x _ y _ => by obtain ⟨p⟩ := hT.connected x y;exact ⟨p,by simp⟩).short_walk
        (Finset.mem_univ x) (Finset.mem_univ y)
    have heq := walkWeight_eq_length_mul p w 1 (fun e he => hw e (p.edges_subset_edgeSet he))
    refine ⟨p,?_⟩
    rw [heq,mul_one]
    have hn : p.length<t := by simpa only [Finset.card_univ] using lt_of_lt_of_le hl (by simpa using hsmall)
    exact_mod_cast hn
  · right
    obtain ⟨P,B,C,hbranch,hcover,hsize,hshort,hcredit,htotal⟩ :=
      exists_initial_unit_clusters T hT.connected w hw (t+1) (by omega) (by omega) c hc
    have hd : (4:ℝ)*(t+1:ℕ)≤8*t := by
      have ht' : (1:ℝ)≤t := by exact_mod_cast ht
      push_cast
      linarith
    let C' : ClusterFamily (I := {S // S∈P}) T w (8*t) := {
      branch := C.branch
      nonempty := C.nonempty
      disjoint := C.disjoint
      connected := by
        intro S x hx y hy
        obtain ⟨p,hp,hl⟩ := C.connected S x hx y hy
        exact ⟨p,hp,le_trans hl hd⟩ }
    refine ⟨P,B,C',hbranch,hcover,hsize,hshort,?_,?_⟩
    · simpa using hcredit
    · have he : T.edgeFinset.card=Fintype.card V-1 := by omega
      simpa only [he] using htotal

end MinorFreeSpanners
