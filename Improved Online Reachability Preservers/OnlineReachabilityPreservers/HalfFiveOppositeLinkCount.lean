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


omit [DecidableEq V] in
private theorem sum_darts_as_neighbor_sums {R : Type*} [AddCommMonoid R]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → V → R) :
    (∑ e : G.Dart, f e.fst e.snd) = ∑ u, ∑ v ∈ G.neighborFinset u, f u v := by
  let unpack : G.Dart ≃ Σ u : V, G.neighborSet u := {
    toFun := fun e => ⟨e.fst,⟨e.snd,e.adj⟩⟩
    invFun := fun uv => ⟨(uv.fst,uv.snd.val),uv.snd.property⟩
    left_inv := by intro e; cases e; rfl
    right_inv := by intro p; cases p; rfl }
  calc
    _ = ∑ uv : Σ u : V, G.neighborSet u, f uv.fst uv.snd.val :=
      Fintype.sum_equiv unpack _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply sum_congr rfl
      intro x _
      exact (sum_subtype (G.neighborFinset x) (fun y => SimpleGraph.mem_neighborFinset G x y) (f x)).symm

omit [DecidableEq V] in
private theorem sum_across_symmetric_neighbors {R : Type*} [AddCommMonoid R]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → V → R) :
    (∑ u, ∑ v ∈ G.neighborFinset u, f u v) = ∑ v, ∑ u ∈ G.neighborFinset v, f u v := by
  have neighbors (u : V) : G.neighborFinset u = univ.filter (G.Adj u) := by ext v; simp
  simp_rw [neighbors,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro u _
  by_cases linked : G.Adj u v
  · simp [linked,linked.symm]
  · have reversed : ¬ G.Adj v u := fun back => linked back.symm
    simp [linked,reversed]

private theorem halfFive_oppositeLinkGraph_two_step_total {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) :
    let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
    letI : DecidableRel G.Adj := Classical.decRel _
    (∑ x, G.degree x*(G.degree x-1)) ≤ Fintype.card V*(Fintype.card V-1) := by
  classical
  let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
  let walks := (univ : Finset V).sigma fun u => edgeSideTwoSteps G u u
  let endpoint (w : Σ _ : V, Σ _ : V, V) : V × V := (w.1,w.2.2)
  let target := (univ : Finset V).offDiag
  have map : Set.MapsTo endpoint walks target := by
    rintro ⟨u,x,z⟩ included
    have step := mem_edgeSideTwoSteps.mp (mem_sigma.mp included).2
    exact mem_offDiag.mpr ⟨mem_univ _,mem_univ _,step.2.2.2.symm⟩
  have injective : Set.InjOn endpoint walks := by
    rintro ⟨u,x,z⟩ left ⟨v,y,w⟩ right equal
    have roots : u = v := congrArg Prod.fst equal
    have ends : z = w := congrArg Prod.snd equal
    subst v
    subst w
    obtain ⟨ux,_,xz,zu⟩ := mem_edgeSideTwoSteps.mp (mem_sigma.mp left).2
    obtain ⟨uy,_,yz,_⟩ := mem_edgeSideTwoSteps.mp (mem_sigma.mp right).2
    have middle : x = y := by
      by_contra apart
      exact halfFour_oppositeLinkGraph_no_square (fun _ h => free (h.trans (by decide)))
        zu.symm apart ux xz yz.symm uy.symm
    subst y
    rfl
  have size := card_le_card_of_injOn endpoint map injective
  have walkCount : walks.card = ∑ x, G.degree x*(G.degree x-1) := by
    calc
      _ = ∑ u, ∑ x ∈ G.neighborFinset u, (G.degree x-1) := by
        simp [walks,card_sigma,edgeSideTwoSteps_card,erase_eq_of_notMem]
      _ = ∑ x, ∑ _ ∈ G.neighborFinset x, (G.degree x-1) :=
        sum_across_symmetric_neighbors G (fun _ x => G.degree x-1)
      _ = _ := by simp
  have fullCount : target.card = Fintype.card V*(Fintype.card V-1) := by
    simp only [target,offDiag_card,card_univ,Nat.mul_sub_left_distrib,Nat.mul_one]
  rw [walkCount,fullCount] at size
  exact size

/-- Sum the edge-neighborhood bound over both orientations of all
opposite links. This controls degree products for nonregular graphs. -/
theorem halfFive_oppositeLinkGraph_degree_product_bound {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) :
    let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
    letI : DecidableRel G.Adj := Classical.decRel _
    let n := Fintype.card V
    let m := Fintype.card G.Dart
    2*(∑ e : G.Dart, G.degree e.fst * G.degree e.snd) ≤ n*m + 2*n*(n-1) := by
  classical
  let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
  let n := Fintype.card V
  let m := Fintype.card G.Dart
  let d (v : V) : ℕ := G.degree v
  let T (u : V) := ∑ v ∈ G.neighborFinset u, d v
  let B (u v : V) := ∑ x ∈ (G.neighborFinset u).erase v, (d x-1)
  have restore {u v : V} (edge : G.Adj u v) : B u v+(d u-1)+d v = T u := by
    let vertices := (G.neighborFinset u).erase v
    have on : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).mpr edge
    have room : vertices.card = d u-1 := card_erase_of_mem on
    have plus : B u v+vertices.card = ∑ x ∈ vertices, d x := by
      change (∑ x ∈ vertices, (d x-1))+vertices.card = _
      have ones : (∑ _ ∈ vertices, (1 : ℕ)) = vertices.card := by simp
      rw [← ones,← sum_add_distrib]
      apply sum_congr rfl
      intro x inside
      have adj : G.Adj u x := (SimpleGraph.mem_neighborFinset _ _ _).mp (mem_erase.mp inside).2
      have positive : 0 < d x := adj.degree_pos_right
      exact Nat.sub_add_cancel (by omega)
    rw [← room,plus]
    exact sum_erase_add (G.neighborFinset u) d on
  have localBound (e : G.Dart) : T e.fst+T e.snd+2 ≤ n+(d e.fst+d e.snd) := by
    have uv : B e.fst e.snd+B e.snd e.fst+(d e.fst+d e.snd) ≤ n :=
      halfFive_oppositeLinkGraph_edge_two_step_bound free e.adj
    have left := restore e.adj
    have right := restore e.adj.symm
    have dp : 0 < d e.fst := e.adj.degree_pos_left
    have dq : 0 < d e.snd := e.adj.degree_pos_right
    omega
  let reversal : G.Dart ≃ G.Dart :=
    ⟨SimpleGraph.Dart.symm,SimpleGraph.Dart.symm,SimpleGraph.Dart.symm_symm,SimpleGraph.Dart.symm_symm⟩
  have reverseSum (f : V → ℕ) : (∑ e : G.Dart, f e.snd) = ∑ e : G.Dart, f e.fst :=
    Equiv.sum_comp reversal (fun e => f e.fst)
  have rootSum (f : V → ℕ) : (∑ e : G.Dart, f e.fst) = ∑ v, d v*f v := by
    rw [sum_darts_as_neighbor_sums G (fun u _ => f u)]
    simp [d]
  let S := ∑ e : G.Dart, d e.fst*d e.snd
  let Q := ∑ v, (d v)^2
  have allT : (∑ e : G.Dart, T e.fst) = S := by
    rw [rootSum]
    change (∑ v, d v*T v) = ∑ e : G.Dart, d e.fst*d e.snd
    rw [sum_darts_as_neighbor_sums G (fun u v => d u*d v)]
    simp [T,mul_sum]
  have allD : (∑ e : G.Dart, d e.fst) = Q := by
    rw [rootSum d]
    simp [Q,pow_two]
  have combined : 2*S+2*m ≤ n*m+2*Q := by
    have total := sum_le_sum (s := (univ : Finset G.Dart)) (fun e _ => localBound e)
    simp only [sum_add_distrib,Finset.sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at total
    rw [reverseSum T,reverseSum d,allT,allD] at total
    change S+S+m*2 ≤ m*n+(Q+Q) at total
    rw [mul_comm m n] at total
    omega
  have squareSum : Q ≤ n*(n-1)+m := by
    have walks : (∑ v, d v*(d v-1)) ≤ n*(n-1) := halfFive_oppositeLinkGraph_two_step_total free
    have degrees : (∑ v, d v) = m := G.dart_card_eq_sum_degrees.symm
    have splitDegree (t : ℕ) : t^2 = t*(t-1)+t := by
      cases t with
      | zero => rfl
      | succ t =>
        simp only [Nat.succ_sub_one]
        ring
    have exactSquare : Q = (∑ v, d v*(d v-1))+m := by
      simp only [Q,splitDegree,sum_add_distrib,degrees]
    rw [exactSquare]
    exact Nat.add_le_add_right walks _
  have doubled := Nat.mul_le_mul_left 2 squareSum
  change 2*S ≤ n*m+2*n*(n-1)
  have expand : 2*(n*(n-1)+m) = 2*n*(n-1)+2*m := by ring
  rw [expand] at doubled
  omega


omit [DecidableEq V] in
private theorem dart_degree_product_lower (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Fintype.card G.Dart)^3 ≤ (Fintype.card V)^2 *
      ∑ e : G.Dart, G.degree e.fst * G.degree e.snd := by
  classical
  let n := Fintype.card V
  let m := Fintype.card G.Dart
  let d (v : V) : ℝ := G.degree v
  let h (e : G.Dart) := Real.sqrt (d e.fst*d e.snd)
  have positiveFirst (e : G.Dart) : 0 < d e.fst := by
    change 0 < (G.degree e.fst:ℝ)
    exact_mod_cast (e.adj.degree_pos_left : 0 < G.degree e.fst)
  have positiveSecond (e : G.Dart) : 0 < d e.snd := by
    change 0 < (G.degree e.snd:ℝ)
    exact_mod_cast (e.adj.degree_pos_right : 0 < G.degree e.snd)
  have positive (e : G.Dart) : 0 < h e :=
    Real.sqrt_pos.2 (mul_pos (positiveFirst e) (positiveSecond e))
  have hSquared (e : G.Dart) : (h e)^2 = d e.fst*d e.snd :=
    Real.sq_sqrt (mul_nonneg (positiveFirst e).le (positiveSecond e).le)
  have inversePair (e : G.Dart) : 2*(h e)⁻¹ ≤ (d e.fst)⁻¹+(d e.snd)⁻¹ := by
    have left := positiveFirst e
    have right := positiveSecond e
    have average : 2*h e ≤ d e.fst+d e.snd := by
      change 2*Real.sqrt (d e.fst*d e.snd) ≤ d e.fst+d e.snd
      rw [Real.sqrt_mul left.le]
      nlinarith only [sq_nonneg (Real.sqrt (d e.fst)-Real.sqrt (d e.snd)),
        Real.sq_sqrt left.le,Real.sq_sqrt right.le]
    apply le_of_mul_le_mul_right _ (mul_pos left right)
    have first : (2*(h e)⁻¹)*(d e.fst*d e.snd) = 2*h e := by
      rw [← hSquared e]
      field_simp [(positive e).ne']
    have last : ((d e.fst)⁻¹+(d e.snd)⁻¹)*(d e.fst*d e.snd) = d e.fst+d e.snd := by
      field_simp [left.ne',right.ne']; ring
    rwa [first,last]
  have inverseFirst : (∑ e : G.Dart, (d e.fst)⁻¹) ≤ (n:ℝ) := by
    rw [sum_darts_as_neighbor_sums G (fun u _ => (d u)⁻¹)]
    calc
      _ ≤ ∑ _ : V, (1:ℝ) := by
        apply sum_le_sum
        intro u _
        simp only [sum_const,SimpleGraph.card_neighborFinset_eq_degree,nsmul_eq_mul]
        change d u*(d u)⁻¹ ≤ 1
        by_cases zero : d u = 0 <;> simp [zero]
      _ = _ := by simp [n]
  let reversal : G.Dart ≃ G.Dart :=
    ⟨SimpleGraph.Dart.symm,SimpleGraph.Dart.symm,SimpleGraph.Dart.symm_symm,SimpleGraph.Dart.symm_symm⟩
  have inverseSecond : (∑ e : G.Dart, (d e.snd)⁻¹) = ∑ e : G.Dart, (d e.fst)⁻¹ :=
    Equiv.sum_comp reversal (fun e => (d e.fst)⁻¹)
  have inverseSum : (∑ e : G.Dart, (h e)⁻¹) ≤ (n:ℝ) := by
    have total : 2*(∑ e : G.Dart, (h e)⁻¹) ≤
        (∑ e : G.Dart, (d e.fst)⁻¹)+(∑ e : G.Dart, (d e.snd)⁻¹) := by
      rw [mul_sum,← sum_add_distrib]
      exact sum_le_sum (fun e _ => inversePair e)
    rw [inverseSecond] at total
    linarith only [inverseFirst,total]
  have canceled (e : G.Dart) : Real.sqrt (h e)*Real.sqrt ((h e)⁻¹) = 1 := by
    rw [← Real.sqrt_mul (positive e).le,mul_inv_cancel₀ (positive e).ne',Real.sqrt_one]
  have rootSquared (e : G.Dart) : (Real.sqrt (h e))^2 = h e := Real.sq_sqrt (positive e).le
  have inverseSquared (e : G.Dart) : (Real.sqrt ((h e)⁻¹))^2 = (h e)⁻¹ :=
    Real.sq_sqrt (inv_nonneg.mpr (positive e).le)
  let A := ∑ e : G.Dart, h e
  have nonnegative : 0 ≤ A := sum_nonneg (fun e _ => (positive e).le)
  have harmonic : (m:ℝ)^2 ≤ A*(n:ℝ) := by
    have cauchy : (m:ℝ)^2 ≤ A*(∑ e : G.Dart, (h e)⁻¹) := by
      simpa only [canceled,rootSquared,inverseSquared,Finset.sum_const,card_univ,nsmul_eq_mul,mul_one,A,m] using
        Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset G.Dart)
          (fun e => Real.sqrt (h e)) (fun e => Real.sqrt ((h e)⁻¹))
    exact cauchy.trans (mul_le_mul_of_nonneg_left inverseSum nonnegative)
  let S := ∑ e : G.Dart, G.degree e.fst*G.degree e.snd
  have squares : (∑ e : G.Dart, (h e)^2) = (S:ℝ) := by
    simp [S,hSquared,d]
  have arithmetic : A^2 ≤ (m:ℝ)*(S:ℝ) := by
    have cauchy : A^2 ≤ (m:ℝ)*(∑ e : G.Dart, (h e)^2) := by
      simpa only [one_mul,one_pow,Finset.sum_const,card_univ,nsmul_eq_mul,mul_one,A,m] using
        Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset G.Dart) (fun _ => (1:ℝ)) h
    rwa [squares] at cauchy
  by_cases empty : m = 0
  · change m^3 ≤ n^2*S
    simp [empty]
  have positiveCount : 0 < (m:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero empty
  have result : (m:ℝ)^3 ≤ (n:ℝ)^2*(S:ℝ) := by
    apply le_of_mul_le_mul_left _ positiveCount
    calc
      (m:ℝ)*(m:ℝ)^3 = ((m:ℝ)^2)^2 := by ring
      _ ≤ (A*(n:ℝ))^2 := pow_le_pow_left₀ (sq_nonneg _) harmonic 2
      _ = (n:ℝ)^2*A^2 := by ring
      _ ≤ (n:ℝ)^2*((m:ℝ)*(S:ℝ)) := mul_le_mul_of_nonneg_left arithmetic (sq_nonneg _)
      _ = _ := by ring
  exact_mod_cast result

/-- Count opposite links without a regularity assumption. The variable
`m` counts both orientations of each opposite link. -/
theorem halfFive_oppositeLinkGraph_card_cubic {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) :
    let n := Fintype.card V
    let m := 2*Nat.card (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).edgeSet
    2*m^3 ≤ n^3*m+2*n^3*(n-1) := by
  classical
  let G := oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))
  let n := Fintype.card V
  let m := Fintype.card G.Dart
  let S := ∑ e : G.Dart, G.degree e.fst*G.degree e.snd
  have lower : m^3 ≤ n^2*S := dart_degree_product_lower G
  have upper : 2*S ≤ n*m+2*n*(n-1) := halfFive_oppositeLinkGraph_degree_product_bound free
  have identify : m = 2*Nat.card G.edgeSet := by
    rw [Nat.card_eq_fintype_card,G.card_edgeSet]
    exact G.dart_card_eq_twice_card_edges
  change 2*(2*Nat.card G.edgeSet)^3 ≤ n^3*(2*Nat.card G.edgeSet)+2*n^3*(n-1)
  rw [← identify]
  calc
    2*m^3 ≤ 2*(n^2*S) := Nat.mul_le_mul_left _ lower
    _ = n^2*(2*S) := by ring
    _ ≤ n^2*(n*m+2*n*(n-1)) := Nat.mul_le_mul_left _ upper
    _ = _ := by ring

/-- A mass condition in the original counts suffices for the frozen
half-five witness, without a degree-regularity premise. -/
theorem regularization_list_frozen_half_five_of_large_mass {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (massLinear : 48*n ≤ 11*(∑ i, (paths i).length))
    (massSquare : 108*n^3 ≤ (11*(∑ i, (paths i).length))^2) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let E := Nat.card (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).edgeSet
  let m := 2*E
  apply regularization_list_frozen_half_five_of_few_opposite_links paths simple free hn hp dense long
  change 24*E ≤ 11*M
  suffices 12*m ≤ 11*M by dsimp only [m] at this; omega
  by_cases low : m ≤ 4*n
  · omega
  have cubic : 2*m^3 ≤ n^3*m+2*n^3*(n-1) := by
    simpa only [Fintype.card_fin] using halfFive_oppositeLinkGraph_card_cubic free
  have error : 4*n^3*(n-1) ≤ n^3*m := calc
    _ = n^3*(4*(n-1)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have four : 4*m^3 ≤ 3*n^3*m := calc
    _ = 2*(2*m^3) := by ring
    _ ≤ 2*(n^3*m+2*n^3*(n-1)) := Nat.mul_le_mul_left _ cubic
    _ = 2*(n^3*m)+4*n^3*(n-1) := by ring
    _ ≤ 2*(n^3*m)+n^3*m := Nat.add_le_add_left error _
    _ = _ := by ring
  have square : 4*m^2 ≤ 3*n^3 := (Nat.mul_le_mul_right_iff (show 0 < m by omega)).mp (by
    calc
      _ = 4*m^3 := by ring
      _ ≤ 3*n^3*m := four)
  have scaled : (12*m)^2 ≤ (11*M)^2 := calc
    _ = 36*(4*m^2) := by ring
    _ ≤ 36*(3*n^3) := Nat.mul_le_mul_left _ square
    _ = 108*n^3 := by ring
    _ ≤ _ := massSquare
  by_contra! violates
  exact (Nat.pow_lt_pow_left violates (by decide : 2 ≠ 0)).not_ge scaled

end OnlineReachabilityPreservers
