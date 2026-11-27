import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import OnlineReachabilityPreservers.DagReduction

/-! The sharp arc bound for a directed graph whose arcs have no substitutes. -/

namespace OnlineReachabilityPreservers

open Finset Relation
variable {V : Type*} [LinearOrder V] [Fintype V]

/-- One canonical representative per strongly connected component. -/
def componentRoots (G : Arcs V) : Finset V := univ.image (componentLabel G)

private theorem mem_componentRoots {G : Arcs V} {v : V} :
    v ∈ componentRoots G ↔ componentLabel G v = v := by
  constructor
  · intro mem
    obtain ⟨u,_,rfl⟩ := mem_image.mp mem
    exact componentLabel_label G u
  · intro root
    exact mem_image.mpr ⟨v,mem_univ _,root⟩

private theorem inTrees_card_le_nonroots (G : Arcs V) :
    (inTrees G).card ≤ Fintype.card V-(componentRoots G).card := by
  have filtered : inTrees G = (componentRoots G)ᶜ.biUnion (towardRoot G) := by
    ext edge
    constructor
    · intro on
      obtain ⟨v,_,uses⟩ := mem_biUnion.mp on
      have nonroot : v ∉ componentRoots G := by
        intro root
        have equal := (mem_componentRoots.mp root).symm
        have empty : towardRoot G v = ∅ := ite_eq_left equal
        rw [empty] at uses
        exact notMem_empty _ uses
      exact mem_biUnion.mpr ⟨v,mem_compl.mpr nonroot,uses⟩
    · intro on
      obtain ⟨v,_,uses⟩ := mem_biUnion.mp on
      exact mem_biUnion.mpr ⟨v,mem_univ _,uses⟩
  rw [filtered]
  calc
    _ ≤ ∑ v ∈ (componentRoots G)ᶜ, (towardRoot G v).card := card_biUnion_le
    _ ≤ ∑ _ ∈ (componentRoots G)ᶜ, 1 := by
      apply sum_le_sum
      intro v _
      unfold towardRoot
      dsimp only
      split
      · simp
      · split <;> simp
    _ = _ := by rw [sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,card_compl]

/-- The two SCC connector forests use at most two edges per nonroot. -/
theorem connectors_card_le_twice_nonroots (G : Arcs V) :
    (connectors G).card ≤ 2*(Fintype.card V-(componentRoots G).card) := by
  have sameRoots : componentRoots (reverseArcs G) = componentRoots G := by
    ext v
    simp only [mem_componentRoots,componentLabel_reverse]
  calc
    _ ≤ (inTrees G).card + (reverseArcs (inTrees (reverseArcs G))).card := card_union_le _ _
    _ ≤ _ := by
      rw [reverseArcs_card,Nat.two_mul]
      exact Nat.add_le_add (inTrees_card_le_nonroots G) (sameRoots ▸ inTrees_card_le_nonroots (reverseArcs G))

private theorem within_component_reach_erase_crossing {G : Arcs V} (e : V × V)
    (crossing : componentLabel G e.1 ≠ componentLabel G e.2) {u v : V}
    (together : SameComponent G u v) : Reach (G.erase e) u v := by
  obtain ⟨forward,back⟩ := together
  induction forward with
  | refl => exact .refl
  | @tail y z initial step ih =>
    have same : SameComponent G y z := ⟨.single step,back.trans initial⟩
    have different : (y,z) ≠ e := by
      rintro rfl
      exact crossing (componentLabel_eq.mpr same)
    exact (ih (back.head step)).tail (mem_erase.mpr ⟨different,step⟩)

private theorem condensation_no_transitive_triangle (G : Arcs V)
    (essential : ∀ {u v}, Edge G u v → ¬ Reach (G.erase (u,v)) u v) {x y z : V}
    (xy : Edge (condensation G) x y) (yz : Edge (condensation G) y z) :
    ¬ Edge (condensation G) x z := by
  intro xz
  obtain ⟨xyApart,a,b,first,ax,byEq⟩ := edge_condensation.mp xy
  obtain ⟨yzApart,c,d,second,cy,dz⟩ := edge_condensation.mp yz
  obtain ⟨xzApart,u,v,direct,ux,vz⟩ := edge_condensation.mp xz
  have crossing : componentLabel G u ≠ componentLabel G v := by rw [ux,vz]; exact xzApart
  have firstApart : (a,b) ≠ (u,v) := by
    intro equal
    exact yzApart (by rw [← byEq, congrArg (fun e : V × V => componentLabel G e.2) equal, vz])
  have secondApart : (c,d) ≠ (u,v) := by
    intro equal
    exact xyApart (by rw [← ux,← cy,congrArg (fun e : V × V => componentLabel G e.1) equal])
  have start := within_component_reach_erase_crossing (u,v) crossing (componentLabel_eq.mp (ux.trans ax.symm))
  have middle := within_component_reach_erase_crossing (u,v) crossing (componentLabel_eq.mp (byEq.trans cy.symm))
  have finish := within_component_reach_erase_crossing (u,v) crossing (componentLabel_eq.mp (dz.trans vz.symm))
  have toMiddle := (start.tail (mem_erase.mpr ⟨firstApart,first⟩ : Edge (G.erase (u,v)) a b)).trans middle
  exact essential direct ((toMiddle.tail (mem_erase.mpr ⟨secondApart,second⟩ : Edge (G.erase (u,v)) c d)).trans finish)

omit [LinearOrder V] [Fintype V] in
private theorem no_triangle_of_dag (G : Arcs V) (dag : IsDAG G)
    (noTransitive : ∀ {x y z}, Edge G x y → Edge G y z → ¬ Edge G x z) {x y z : V}
    (xy : Edge G x y ∨ Edge G y x) (yz : Edge G y z ∨ Edge G z y)
    (xz : Edge G x z ∨ Edge G z x) : False := by
  rcases xy with xy | yx <;> rcases yz with yz | zy <;> rcases xz with xz | zx
  · exact noTransitive xy yz xz
  · exact dag zx ((ReflTransGen.single xy).tail yz)
  · exact noTransitive xz zy xy
  · exact noTransitive zx xy zy
  · exact noTransitive yx xz yz
  · exact noTransitive yz zx yx
  · exact dag xz ((ReflTransGen.single zy).tail yx)
  · exact noTransitive zy yx zx

private theorem condensation_card_of_essential (G : Arcs V)
    (essential : ∀ {u v}, Edge G u v → ¬ Reach (G.erase (u,v)) u v) :
    (condensation G).card ≤ (componentRoots G).card^2/4 := by
  classical
  let R := ↥(componentRoots G)
  let U : SimpleGraph R :=
    ⟨fun x y => Edge (condensation G) x.val y.val ∨ Edge (condensation G) y.val x.val,
      ⟨fun {_ _} adj => Or.symm adj⟩,⟨fun _ adj => (condensation_dag G (adj.elim id id)) (.refl)⟩⟩
  have free : U.CliqueFree 3 := by
    intro vertices triangle
    obtain ⟨x,y,z,xy,xz,yz,rfl⟩ := card_eq_three.mp triangle.card_eq
    have xOn : x ∈ ({x,y,z} : Finset R) := by simp
    have yOn : y ∈ ({x,y,z} : Finset R) := by simp
    have zOn : z ∈ ({x,y,z} : Finset R) := by simp
    have together := triangle.isClique
    exact no_triangle_of_dag (condensation G) (condensation_dag G)
      (fun {_ _ _} => condensation_no_transitive_triangle G essential)
      (together xOn yOn xy) (together yOn zOn yz) (together xOn zOn xz)
  have rootEndpoints (e : condensation G) : e.val.1 ∈ componentRoots G ∧ e.val.2 ∈ componentRoots G := by
    obtain ⟨_,u,v,_,left,right⟩ := edge_condensation.mp
      (show Edge (condensation G) e.val.1 e.val.2 from e.property)
    exact ⟨mem_image.mpr ⟨u,mem_univ _,left⟩,mem_image.mpr ⟨v,mem_univ _,right⟩⟩
  let ends (e : condensation G) : R × R :=
    (⟨e.val.1,(rootEndpoints e).1⟩,⟨e.val.2,(rootEndpoints e).2⟩)
  let f (e : condensation G) : U.edgeFinset :=
    ⟨s((ends e).1,(ends e).2),SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet (G := U)).mpr (Or.inl e.property))⟩
  have injective : Function.Injective f := by
    intro e d same
    have pair : s((ends e).1,(ends e).2) = s((ends d).1,(ends d).2) := congrArg Subtype.val same
    rcases Sym2.mk_eq_mk_iff.mp pair with normal | reverse
    · exact Subtype.ext (congrArg (fun e : R × R => (e.1.val,e.2.val)) normal)
    · have equal : e.val = d.val.swap := congrArg (fun e : R × R => (e.1.val,e.2.val)) reverse
      have back : Edge (condensation G) e.val.2 e.val.1 := by rw [equal]; exact d.property
      exact (condensation_dag G (show Edge (condensation G) e.val.1 e.val.2 from e.property) (.single back)).elim
  have size : (condensation G).card ≤ U.edgeFinset.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f injective
  have cardR : Fintype.card R = (componentRoots G).card := Fintype.card_coe _
  exact size.trans (by simpa only [SimpleGraph.turanNumber_two,cardR] using
    (free.card_edgeFinset_le (r := 2)))

/-- With no alternate reachability route for any arc, each component needs
only its two connector trees. Its condensation has at most the Mantel bound. -/
theorem essential_arcs_card_le_component_bound (G : Arcs V)
    (essential : ∀ {u v}, Edge G u v → ¬ Reach (G.erase (u,v)) u v) :
    G.card ≤ 2*(Fintype.card V-(componentRoots G).card)+(componentRoots G).card^2/4 := by
  let K := connectors G ∪ liftedArcs G (condensation G)
  have sub : K ⊆ G := union_subset (connectors_subset G) (liftedArcs_subset G _)
  have enough : G ⊆ K := by
    rintro ⟨u,v⟩ edge
    by_contra apart
    have without : K ⊆ G.erase (u,v) := fun e on => mem_erase.mpr ⟨fun eq => apart (eq ▸ on),sub on⟩
    have together : Reach K u v := lift_selected_reach (Subset.refl _) (project_reach (ReflTransGen.single edge)) u v rfl rfl
    exact essential edge (reach_mono without together)
  rw [show G.card = K.card from congrArg Finset.card (Subset.antisymm enough sub)]
  exact (card_union_le _ _).trans (Nat.add_le_add (connectors_card_le_twice_nonroots G)
    ((liftedArcs_card G _).trans (condensation_card_of_essential G essential)))

/-- A directed graph whose edges all matter for reachability has at
most the larger of twice a tree's edge count and the Mantel bound. -/
theorem essential_arcs_card_le_tree_or_bipartite (G : Arcs V)
    (essential : ∀ {u v}, Edge G u v → ¬ Reach (G.erase (u,v)) u v) :
    G.card ≤ max (2*(Fintype.card V-1)) ((Fintype.card V)^2/4) := by
  let n := Fintype.card V
  let c := (componentRoots G).card
  have cLe : c ≤ n := card_le_univ _
  have main : G.card ≤ 2*(n-c)+c^2/4 := essential_arcs_card_le_component_bound G essential
  by_cases nZero : n = 0
  · have cZero : c = 0 := by omega
    have zero : G.card ≤ 0 := by simpa [nZero,cZero] using main
    exact zero.trans (Nat.zero_le _)
  have positive : 0 < c := by
    have h : 0 < Fintype.card V := Nat.pos_of_ne_zero nZero
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp h
    exact card_pos.mpr ⟨componentLabel G v,mem_image.mpr ⟨v,mem_univ _,rfl⟩⟩
  by_cases small : c ≤ 3
  · have bound : c^2/4 ≤ 2*(c-1) := by interval_cases c <;> decide
    exact main.trans ((show 2*(n-c)+c^2/4 ≤ 2*(n-1) by omega).trans (le_max_left _ _))
  · have diff : c+(n-c) = n := Nat.add_sub_of_le cLe
    have comparison : 8*(n-c)+c^2 ≤ n^2 := by
      have sum : 8 ≤ n+c := by omega
      have mul := Nat.mul_le_mul_right (n-c) sum
      nlinarith only [mul,diff]
    exact main.trans ((show 2*(n-c)+c^2/4 ≤ n^2/4 by omega).trans (le_max_right _ _))

end OnlineReachabilityPreservers
