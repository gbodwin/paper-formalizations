import OnlineReachabilityPreservers.HalfFiveOppositeCycles
import OnlineReachabilityPreservers.FrozenMatchedPartners

/-! Count two-step walks on the two sides of an opposite link. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

variable {I V : Type*} [LinearOrder I] [DecidableEq V] [Fintype V]

private def edgeSideTwoSteps (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    Finset (Σ _ : V, V) :=
  ((G.neighborFinset u).erase v).sigma (fun x => (G.neighborFinset x).erase u)

private theorem mem_edgeSideTwoSteps {G : SimpleGraph V} [DecidableRel G.Adj] {u v x y : V} :
    (⟨x,y⟩ : Σ _ : V, V) ∈ edgeSideTwoSteps G u v ↔
      G.Adj u x ∧ x ≠ v ∧ G.Adj x y ∧ y ≠ u := by
  simp only [edgeSideTwoSteps,mem_sigma,mem_erase,SimpleGraph.mem_neighborFinset]
  tauto

private theorem edgeSideTwoSteps_card (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    (edgeSideTwoSteps G u v).card = ∑ x ∈ (G.neighborFinset u).erase v, (G.degree x-1) := by
  rw [edgeSideTwoSteps,card_sigma]
  apply sum_congr rfl
  intro x inside
  have adjacent := (SimpleGraph.mem_neighborFinset _ _ _).mp (mem_erase.mp inside).2
  rw [card_erase_of_mem (SimpleGraph.mem_neighborFinset _ _ _ |>.mpr adjacent.symm),
    SimpleGraph.card_neighborFinset_eq_degree]

/-- The two-step walks continuing away from an edge have distinct
endpoints, and every endpoint is outside both root neighborhoods. -/
theorem halfFive_oppositeLinkGraph_edge_two_step_bound {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) {u v : V}
    (edge : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj u v) :
    let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
    letI : DecidableRel G.Adj := Classical.decRel _
    (∑ x ∈ (G.neighborFinset u).erase v, (G.degree x-1)) +
      (∑ x ∈ (G.neighborFinset v).erase u, (G.degree x-1)) +
      (G.degree u + G.degree v) ≤ Fintype.card V := by
  classical
  let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
  have triangle {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False :=
    halfThree_oppositeLinkGraph_no_triangle (fun _ h => free (h.trans (by decide))) ab bc ca
  have oneSide {a b x y z : V} (first : (⟨x,z⟩ : Σ _ : V, V) ∈ edgeSideTwoSteps G a b)
      (second : (⟨y,z⟩ : Σ _ : V, V) ∈ edgeSideTwoSteps G a b) : x = y := by
    obtain ⟨ax,_,xz,za⟩ := mem_edgeSideTwoSteps.mp first
    obtain ⟨ay,_,yz,_⟩ := mem_edgeSideTwoSteps.mp second
    by_contra apart
    exact halfFour_oppositeLinkGraph_no_square (fun _ h => free (h.trans (by decide)))
      za.symm apart ax xz yz.symm ay.symm
  have across {x y z : V} (first : (⟨x,z⟩ : Σ _ : V, V) ∈ edgeSideTwoSteps G u v)
      (second : (⟨y,z⟩ : Σ _ : V, V) ∈ edgeSideTwoSteps G v u) : False := by
    obtain ⟨ux,xv,xz,zu⟩ := mem_edgeSideTwoSteps.mp first
    obtain ⟨vy,yu,yz,zv⟩ := mem_edgeSideTwoSteps.mp second
    have apartXY : x ≠ y := fun eq => triangle edge vy (eq ▸ ux.symm)
    have apartUV := edge.ne
    have apartUX := ux.ne
    have apartXZ := xz.ne
    have apartVY := vy.ne
    have apartYZ := yz.ne
    let corners : Fin 5 → V := ![u,x,z,y,v]
    have distinct : Function.Injective corners := by
      apply List.nodup_ofFn.mp
      change ([u,x,z,y,v] : List V).Nodup
      simp [apartUX,zu.symm,yu.symm,apartUV,apartXZ,apartXY,xv,apartYZ.symm,zv,apartVY.symm]
    apply halfFive_oppositeLinkGraph_no_pentagon free corners distinct
    intro i
    fin_cases i
    · exact ux
    · exact xz
    · exact yz.symm
    · exact vy.symm
    · exact edge.symm
  let pairs (side : Bool) := if side then edgeSideTwoSteps G u v else edgeSideTwoSteps G v u
  let both := (univ : Finset Bool).sigma pairs
  let endpoint (w : Σ _ : Bool, Σ _ : V, V) := w.2.2
  have distinctEnds : Set.InjOn endpoint both := by
    rintro ⟨a,x,z⟩ ax ⟨b,y,w⟩ byMem equal
    change z = w at equal
    subst w
    have left := (mem_sigma.mp ax).2
    have right := (mem_sigma.mp byMem).2
    cases a <;> cases b
    · have same := oneSide (show (⟨x,z⟩ : Σ _ : V, V) ∈ edgeSideTwoSteps G v u from left) right
      subst y
      rfl
    · exact (across right left).elim
    · exact (across left right).elim
    · have same := oneSide (show (⟨x,z⟩ : Σ _ : V, V) ∈ edgeSideTwoSteps G u v from left) right
      subst y
      rfl
  let roots := G.neighborFinset u ∪ G.neighborFinset v
  let target := (univ : Finset V) \ roots
  have outside {a b x z : V} (adjacent : G.Adj a b)
      (step : (⟨x,z⟩ : Σ _ : V, V) ∈ edgeSideTwoSteps G a b) :
      ¬ G.Adj a z ∧ ¬ G.Adj b z := by
    obtain ⟨ax,xb,xz,za⟩ := mem_edgeSideTwoSteps.mp step
    refine ⟨fun az => triangle ax xz az.symm,fun bz => ?_⟩
    exact halfFour_oppositeLinkGraph_no_square (fun _ h => free (h.trans (by decide)))
      za.symm xb ax xz bz.symm adjacent.symm
  have mapped : Set.MapsTo endpoint both target := by
    rintro ⟨flag,x,z⟩ inside
    have steps := (mem_sigma.mp inside).2
    have apart : ¬ G.Adj u z ∧ ¬ G.Adj v z := by
      cases flag
      · exact (outside edge.symm steps).symm
      · exact outside edge steps
    exact mem_sdiff.mpr ⟨mem_univ _,fun on => (mem_union.mp on).elim
      (fun left => apart.1 ((SimpleGraph.mem_neighborFinset _ _ _).mp left))
      (fun right => apart.2 ((SimpleGraph.mem_neighborFinset _ _ _).mp right))⟩
  have separated : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
    apply disjoint_left.mpr
    intro z uz vz
    exact triangle edge ((SimpleGraph.mem_neighborFinset _ _ _).mp vz)
      ((SimpleGraph.mem_neighborFinset _ _ _).mp uz).symm
  have rootCount : roots.card = G.degree u + G.degree v := by
    change (G.neighborFinset u ∪ G.neighborFinset v).card = _
    rw [card_union_of_disjoint separated,SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree]
  have fits : G.degree u + G.degree v ≤ Fintype.card V := by
    rw [← rootCount,← card_univ]
    exact card_le_card (subset_univ _)
  have targetCount : target.card = Fintype.card V-(G.degree u + G.degree v) := by
    change ((univ : Finset V) \ roots).card = _
    rw [card_sdiff_of_subset (subset_univ _),card_univ,rootCount]
  have total := card_le_card_of_injOn endpoint mapped distinctEnds
  have count : (∑ x ∈ (G.neighborFinset u).erase v, (G.degree x-1)) +
      (∑ x ∈ (G.neighborFinset v).erase u, (G.degree x-1)) ≤ Fintype.card V-(G.degree u + G.degree v) := by
    simpa [both,pairs,card_sigma,Fintype.sum_bool,edgeSideTwoSteps_card,targetCount,add_comm] using total
  change (∑ x ∈ (G.neighborFinset u).erase v, (G.degree x-1)) +
      (∑ x ∈ (G.neighborFinset v).erase u, (G.degree x-1)) +
      (G.degree u + G.degree v) ≤ Fintype.card V
  omega


/-- A lower degree bound on the opposite-link graph forces a vertex
budget covering both root neighborhoods and the distinct two-step endpoints. -/
theorem halfFive_oppositeLinkGraph_min_degree_bound {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) {u v : V}
    (edge : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj u v)
    (d : ℕ) (degreeLower : let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
      letI : DecidableRel G.Adj := Classical.decRel _
      ∀ x, d ≤ G.degree x) :
    2*d + 2*(d-1)^2 ≤ Fintype.card V := by
  classical
  let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
  have oneSide {a b : V} (adjacent : G.Adj a b) :
      (d-1)^2 ≤ ∑ x ∈ (G.neighborFinset a).erase b, (G.degree x-1) := by
    let neighbors := (G.neighborFinset a).erase b
    have count : d-1 ≤ neighbors.card := by
      change d-1 ≤ ((G.neighborFinset a).erase b).card
      rw [card_erase_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).mpr adjacent),
        SimpleGraph.card_neighborFinset_eq_degree]
      exact Nat.sub_le_sub_right (degreeLower a) 1
    calc
      (d-1)^2 = (d-1)*(d-1) := by ring
      _ ≤ neighbors.card*(d-1) := Nat.mul_le_mul_right _ count
      _ = ∑ x ∈ neighbors, (d-1) := by simp
      _ ≤ _ := sum_le_sum (fun x _ => Nat.sub_le_sub_right (degreeLower x) 1)
  calc
    2*d + 2*(d-1)^2 = (d-1)^2+(d-1)^2+(d+d) := by ring
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (oneSide edge) (oneSide edge.symm))
      (Nat.add_le_add (degreeLower u) (degreeLower v))
    _ ≤ _ := halfFive_oppositeLinkGraph_edge_two_step_bound free edge

/-- For a regular opposite-link graph, the degree bound gives a frozen
half-five witness from a sufficient inequality involving only mass and
vertex budget. -/
theorem regularization_list_frozen_half_five_of_regular_opposite_links {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (d : ℕ) (regular : let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
      letI : DecidableRel G.Adj := Classical.decRel _
      ∀ x, G.degree x = d)
    (massLinear : 12*n ≤ 11*(∑ i, (paths i).length))
    (massSquare : 144*n^3 ≤ 2*(11*(∑ i, (paths i).length)-12*n)^2) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
  let E := Nat.card G.edgeSet
  apply regularization_list_frozen_half_five_of_few_opposite_links paths simple free hn hp dense long
  change 24*E ≤ 11*M
  have degreeSum : 2*E = n*d := by
    change 2*Nat.card G.edgeSet = n*d
    rw [Nat.card_eq_fintype_card,G.card_edgeSet,← G.sum_degrees_eq_twice_card_edges]
    have uniform (x : Fin n) : G.degree x = d := regular x
    simp [uniform]
  by_cases isolated : d = 0
  · rw [isolated,Nat.mul_zero] at degreeSum
    omega
  let u : Fin n := ⟨0,hn⟩
  have positive : 0 < G.degree u := by rw [regular]; omega
  obtain ⟨v,adjacent⟩ := (SimpleGraph.degree_pos_iff_exists_adj G u).mp positive
  have capacity : 2*(d-1)^2 ≤ n := by
    have bound := halfFive_oppositeLinkGraph_min_degree_bound free adjacent d (fun x => (regular x).ge)
    simp only [Fintype.card_fin] at bound
    omega
  have scaled : 2*(12*n*(d-1))^2 ≤ 144*n^3 := calc
    _ = (144*n^2)*(2*(d-1)^2) := by ring
    _ ≤ (144*n^2)*n := Nat.mul_le_mul_left _ capacity
    _ = _ := by ring
  have compare : 12*n*(d-1) ≤ 11*M-12*n := by
    by_contra! strict
    have larger := Nat.pow_lt_pow_left strict (by decide : 2 ≠ 0)
    have enough : 2*(12*n*(d-1))^2 ≤ 2*(11*M-12*n)^2 := scaled.trans massSquare
    omega
  have one : d-1+1 = d := by omega
  have count : 24*E = 12*n*(d-1)+12*n := calc
    _ = 12*(2*E) := by ring
    _ = 12*(n*d) := by rw [degreeSum]
    _ = 12*n*d := by ring
    _ = 12*n*(d-1+1) := congrArg (fun x => 12*n*x) one.symm
    _ = _ := by ring
  omega

end OnlineReachabilityPreservers
