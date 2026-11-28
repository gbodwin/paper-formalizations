import OnlineReachabilityPreservers.FrozenSmallBudgets
import OnlineReachabilityPreservers.CyclicIntersections

/-! Literal row capacity through full cutoff three and short full-free witnesses. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- In a directed graph with no transitive triangle, an arc's endpoints
have disjoint out-neighborhoods and disjoint in-neighborhoods. -/
theorem directed_arcs_card_le_half_square_of_no_transitive_triangle {V : Type*} [Fintype V] [DecidableEq V]
    (arcs : Finset (V × V))
    (noTriangle : ∀ {x y z : V}, (x,y) ∈ arcs → (y,z) ∈ arcs → (x,z) ∉ arcs) :
    2*arcs.card ≤ (Fintype.card V)^2 := by
  let out (v : V) := (univ : Finset V).filter (fun w => (v,w) ∈ arcs)
  let incoming (v : V) := (univ : Finset V).filter (fun w => (w,v) ∈ arcs)
  let degree (v : V) := (out v).card+(incoming v).card
  let n := Fintype.card V
  let m := arcs.card
  have outCard (v : V) : (arcs.filter fun e => e.1 = v).card = (out v).card := by
    let embed : V ↪ V × V := ⟨fun w => (v,w),fun _ _ eq => congrArg Prod.snd eq⟩
    have equal : (out v).map embed = arcs.filter fun e => e.1 = v := by
      ext e
      rcases e with ⟨x,y⟩
      simp only [mem_map,mem_filter,mem_univ,true_and,out]
      constructor
      · rintro ⟨w,member,equal⟩
        change (v,w) = (x,y) at equal
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
        exact ⟨member,rfl⟩
      · rintro ⟨member,rfl⟩
        exact ⟨y,member,rfl⟩
    rw [← equal,card_map]
  have inCard (v : V) : (arcs.filter fun e => e.2 = v).card = (incoming v).card := by
    let embed : V ↪ V × V := ⟨fun w => (w,v),fun _ _ eq => congrArg Prod.fst eq⟩
    have equal : (incoming v).map embed = arcs.filter fun e => e.2 = v := by
      ext e
      rcases e with ⟨x,y⟩
      simp only [mem_map,mem_filter,mem_univ,true_and,incoming]
      constructor
      · rintro ⟨w,member,equal⟩
        change (w,v) = (x,y) at equal
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
        exact ⟨member,rfl⟩
      · rintro ⟨member,rfl⟩
        exact ⟨x,member,rfl⟩
    rw [← equal,card_map]
  have distribute (choose : V × V → V) (size : V → ℕ)
      (counts : ∀ v, (arcs.filter fun e => choose e = v).card = size v) (weight : V → ℕ) :
      (∑ e ∈ arcs, weight (choose e)) = ∑ v, size v*weight v := calc
    _ = ∑ v : V, ∑ e ∈ arcs.filter (fun e => choose e = v), weight (choose e) :=
      (sum_fiberwise_of_maps_to (fun e (_ : e ∈ arcs) => mem_univ (choose e)) (fun e => weight (choose e))).symm
    _ = _ := by
      apply sum_congr rfl
      intro v _
      calc
        _ = ∑ _ ∈ arcs.filter (fun e => choose e = v), weight v :=
          sum_congr rfl fun e member => congrArg weight (mem_filter.mp member).2
        _ = _ := by rw [sum_const,nsmul_eq_mul,counts,Nat.cast_id]
  have weighted (weight : V → ℕ) :
      (∑ e ∈ arcs, (weight e.1+weight e.2)) = ∑ v, degree v*weight v := by
    rw [sum_add_distrib,distribute Prod.fst _ outCard,distribute Prod.snd _ inCard,← sum_add_distrib]
    simp only [degree,Nat.add_mul]
  have total : ∑ v, degree v = 2*m := by
    simpa [m,Nat.mul_comm] using (weighted (fun _ => 1)).symm
  have sumLimit : (∑ v, (degree v)^2) ≤ (2*n)*m := by
    simp only [pow_two]
    rw [← weighted degree]
    calc
      _ ≤ ∑ _ ∈ arcs, 2*n := by
        apply sum_le_sum
        intro e on
        have outApart : Disjoint (out e.1) (out e.2) := disjoint_left.mpr fun w a b =>
          noTriangle on (mem_filter.mp b).2 (mem_filter.mp a).2
        have inApart : Disjoint (incoming e.1) (incoming e.2) := disjoint_left.mpr fun w a b =>
          noTriangle (mem_filter.mp a).2 on (mem_filter.mp b).2
        have outLimit : (out e.1).card+(out e.2).card ≤ n := by
          rw [← card_union_of_disjoint outApart]
          exact card_le_univ _
        have inLimit : (incoming e.1).card+(incoming e.2).card ≤ n := by
          rw [← card_union_of_disjoint inApart]
          exact card_le_univ _
        dsimp [degree]
        omega
      _ = _ := by simp [m,Nat.mul_comm]
  have squared : (2*m)^2 ≤ n*(∑ v, (degree v)^2) := by
    have cauchy := sum_mul_sq_le_sq_mul_sq (R := ℕ) (univ : Finset V) (fun _ => 1) degree
    simpa only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,total,n] using cauchy
  by_cases empty : m = 0
  · change 2*m ≤ n^2
    omega
  have compare : (2*m)*(2*m) ≤ (2*m)*n^2 := calc
    _ = (2*m)^2 := (pow_two _).symm
    _ ≤ n*((2*n)*m) := squared.trans (Nat.mul_le_mul_left _ sumLimit)
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left compare (by omega)

theorem balancedLayer_product {n m : ℕ} (bound : 2*m ≤ n^2) :
    m ≤ 2*((n/2)*(n-n/2)) := by
  let a := n/2
  let b := n-a
  have nEq : n = a+b := by dsimp [a,b]; omega
  have side : b = a ∨ b = a+1 := by dsimp [a,b]; omega
  have square : n^2 ≤ 4*(a*b)+1 := by
    rcases side with same | next
    · have expanded : (a+b)^2 = 4*(a*b) := by rw [same]; ring
      rw [← expanded,← nEq]
      omega
    · have expanded : (a+b)^2 = 4*(a*b)+1 := by rw [next]; ring
      rw [← expanded,← nEq]
  change m ≤ 2*(a*b)
  omega

/-- First comparisons of the longer rows of a literal family can be
assigned to distinct arcs, leaving at most one singleton per vertex. -/
theorem literal_first_darts {n p cutoff : ℕ} (paths : Fin p → List (Fin n))
    (unique : Function.Injective paths) (well : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff) :
    ∃ arcs : Arcs (Fin n), p ≤ n+arcs.card ∧ ∃ owner : arcs → Fin p,
      Function.Injective owner ∧ ∀ edge : arcs, Before paths (owner edge) edge.val.1 edge.val.2 := by
  classical
  let long := (univ : Finset (Fin p)).filter fun i => 2 ≤ (paths i).length
  let short := longᶜ
  let head (i : short) : Fin n := (paths i.val)[0]'(List.length_pos_iff.mpr (well i.val).1)
  have single (i : short) : paths i.val = [head i] := by
    have positive := List.length_pos_iff.mpr (well i.val).1
    have small : ¬ 2 ≤ (paths i.val).length := fun enough => (mem_compl.mp i.property)
      (mem_filter.mpr ⟨mem_univ _,enough⟩)
    obtain ⟨x,equal⟩ := List.length_eq_one_iff.mp (by omega : (paths i.val).length = 1)
    have label : head i = x := by unfold head; rw [List.getElem_of_eq equal]; rfl
    rw [label]
    exact equal
  have headInjective : Function.Injective head := by
    intro i j same
    exact Subtype.ext (unique ((single i).trans ((congrArg (fun x => [x]) same).trans (single j).symm)))
  have shortCount : short.card ≤ n := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective head headInjective
  have counts : long.card+short.card = p := by
    rw [show short = longᶜ from rfl,card_compl,Fintype.card_fin]
    exact Nat.add_sub_of_le (by simpa using card_le_univ long)
  have length (i : long) : 2 ≤ (paths i.val).length := (mem_filter.mp i.property).2
  let dart (i : long) : Fin n × Fin n :=
    ((paths i.val)[0]'(by have := length i; omega),(paths i.val)[1]'(by have := length i; omega))
  have step (i : long) : Before paths i.val (dart i).1 (dart i).2 := by
    refine ⟨List.getElem_mem _,List.getElem_mem _,?_⟩
    dsimp only [dart]
    rw [(well i.val).2.idxOf_getElem,(well i.val).2.idxOf_getElem]
    decide
  have dartInjective : Function.Injective dart := by
    intro i j equal
    by_contra apart
    have comparison := step j
    rw [← equal] at comparison
    exact no_parallel_list_steps free two (fun same => apart (Subtype.ext same)) (step i) comparison
  let arcs := (univ : Finset long).image dart
  have countArcs : arcs.card = long.card := by
    rw [show arcs = univ.image dart from rfl,card_image_of_injective _ dartInjective,card_univ,Fintype.card_coe]
  have gives (edge : arcs) : ∃ i : long, dart i = edge.val := by
    obtain ⟨i,_,equal⟩ := mem_image.mp edge.property
    exact ⟨i,equal⟩
  let chosen (edge : arcs) := Classical.choose (gives edge)
  have identifies (edge : arcs) : dart (chosen edge) = edge.val := Classical.choose_spec (gives edge)
  let owner (edge : arcs) := (chosen edge).val
  have ownerUnique : Function.Injective owner := by
    intro e f same
    exact Subtype.ext ((identifies e).symm.trans ((congrArg dart (Subtype.ext same)).trans (identifies f)))
  refine ⟨arcs,by omega,owner,ownerUnique,?_⟩
  intro e
  have compare := step (chosen e)
  rw [identifies e] at compare
  exact compare

/-- Full exclusion through size three limits the exact number of
nonempty distinct rows to the balanced bidirectional bipartite capacity
plus one singleton for each vertex. -/
theorem literal_full_path_count_le_balanced_bipartite {n p cutoff : ℕ} (paths : Fin p → List (Fin n))
    (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (three : 3 ≤ cutoff) : p ≤ n+2*((n/2)*(n-n/2)) := by
  obtain ⟨arcs,count,owner,unique,compares⟩ := literal_first_darts paths distinct
    (fun i => ⟨nonempty i,simple i⟩) free.halfFree (by omega)
  have noTriangle {x y z : Fin n} (xy : (x,y) ∈ arcs) (yz : (y,z) ∈ arcs) (xz : (x,z) ∈ arcs) : False := by
    let a : arcs := ⟨(x,y),xy⟩
    let b : arcs := ⟨(y,z),yz⟩
    let r : arcs := ⟨(x,z),xz⟩
    have xyApart : x ≠ y := listBefore_ne (compares a)
    have yzApart : y ≠ z := listBefore_ne (compares b)
    have ab : owner a ≠ owner b := fun same => xyApart
      (congrArg (fun e : arcs => e.val.1) (unique same))
    have ra : owner r ≠ owner a := fun same => yzApart
      (congrArg (fun e : arcs => e.val.2) (unique same)).symm
    have rb : owner r ≠ owner b := fun same => xyApart
      (congrArg (fun e : arcs => e.val.1) (unique same))
    exact (free three).false (threeListBridge ab ra rb (compares a) (compares b) (compares r))
  have budget := directed_arcs_card_le_half_square_of_no_transitive_triangle arcs (fun {_ _ _} => noTriangle)
  rw [Fintype.card_fin] at budget
  exact count.trans (Nat.add_le_add_left (balancedLayer_product budget) n)

abbrev TwoLayerRow (a b : ℕ) := (Bool × Fin a × Fin b) ⊕ Fin (a+b)

def twoLayerBidirectionalRows {a b : ℕ} : TwoLayerRow a b → List (Fin (a+b))
  | Sum.inl (reverse,i,j) =>
    let left := Fin.castAdd b i
    let right := Fin.natAdd a j
    if reverse then [right,left] else [left,right]
  | Sum.inr v => [v]

theorem layer_vertices_different {a b : ℕ} (i : Fin a) (j : Fin b) : Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro equal
  have number := congrArg Fin.val equal
  change i.val = a+j.val at number
  have := i.isLt
  omega

private theorem twoLayerBidirectionalRows_injective {a b : ℕ} :
    Function.Injective (@twoLayerBidirectionalRows a b) := by
  have left : Function.Injective (Fin.castAdd b : Fin a → Fin (a+b)) :=
    fun _ _ eq => Fin.ext (congrArg (fun v : Fin (a+b) => v.val) eq)
  have right : Function.Injective (Fin.natAdd a : Fin b → Fin (a+b)) :=
    fun _ _ eq => Fin.ext (Nat.add_left_cancel (congrArg Fin.val eq))
  rintro (⟨r,i,j⟩ | v) (⟨s,i',j'⟩ | w) equal
  · cases r <;> cases s
    · have ends : Fin.castAdd b i = Fin.castAdd b i' ∧ Fin.natAdd a j = Fin.natAdd a j' := by
        simpa [twoLayerBidirectionalRows] using equal
      rw [left ends.1,right ends.2]
    · have crossed : Fin.castAdd b i = Fin.natAdd a j' := by
        simpa [twoLayerBidirectionalRows] using congrArg List.head? equal
      exact (layer_vertices_different i j' crossed).elim
    · have crossed : Fin.natAdd a j = Fin.castAdd b i' := by
        simpa [twoLayerBidirectionalRows] using congrArg List.head? equal
      exact (layer_vertices_different i' j crossed.symm).elim
    · have ends : Fin.natAdd a j = Fin.natAdd a j' ∧ Fin.castAdd b i = Fin.castAdd b i' := by
        simpa [twoLayerBidirectionalRows] using equal
      rw [left ends.2,right ends.1]
  · have lengths := congrArg List.length equal
    cases r <;> simp [twoLayerBidirectionalRows] at lengths
  · have lengths := congrArg List.length equal
    cases s <;> simp [twoLayerBidirectionalRows] at lengths
  · have vertex : v = w := by simpa [twoLayerBidirectionalRows] using equal
    rw [vertex]
/-- A strict comparison in an exact pair row has its two listed endpoints. -/
theorem listBefore_endpoints_of_pair {I V : Type*} [DecidableEq V]
    {paths : I → List V} {i : I} {u v x y : V} (row : paths i = [u,v])
    (step : Before paths i x y) : x = u ∧ y = v := by
  have start : x = u ∨ x = v := by simpa [row] using step.1
  have finish : y = u ∨ y = v := by simpa [row] using step.2.1
  rcases start with rfl | rfl <;> rcases finish with rfl | rfl
  · exact (listBefore_ne step rfl).elim
  · exact ⟨rfl,rfl⟩
  · have order := step.2.2
    rw [row] at order
    simp at order
  · exact (listBefore_ne step rfl).elim

private theorem twoLayerBidirectionalRows_step {a b : ℕ} {i : TwoLayerRow a b} {x y : Fin (a+b)}
    (step : Before twoLayerBidirectionalRows i x y) :
    twoLayerBidirectionalRows i = [x,y] ∧ (x.val < a ↔ ¬ y.val < a) := by
  rcases i with ⟨reverse,u,v⟩ | v
  · cases reverse
    · have row : twoLayerBidirectionalRows (Sum.inl (false,u,v)) = [Fin.castAdd b u,Fin.natAdd a v] := rfl
      obtain ⟨rfl,rfl⟩ := listBefore_endpoints_of_pair row step
      exact ⟨row,iff_of_true u.isLt (by change ¬ a+v.val < a; omega)⟩
    · have row : twoLayerBidirectionalRows (Sum.inl (true,u,v)) = [Fin.natAdd a v,Fin.castAdd b u] := rfl
      obtain ⟨rfl,rfl⟩ := listBefore_endpoints_of_pair row step
      refine ⟨row,iff_of_false (by change ¬ a+v.val < a; omega) ?_⟩
      change ¬ ¬ u.val < a
      exact not_not_intro u.isLt
  · have same : x = v ∧ y = v := by simpa [twoLayerBidirectionalRows] using And.intro step.1 step.2.1
    exact (listBefore_ne step (same.1.trans same.2.symm)).elim

theorem twoLayerBidirectionalRows_full_three (a b : ℕ) :
    BridgeFree (Before (@twoLayerBidirectionalRows a b)) 3 := by
  intro s size
  refine ⟨fun bridge => ?_⟩
  have possible : s = 0 ∨ s = 1 := by omega
  rcases possible with rfl | rfl
  · have river := (twoLayerBidirectionalRows_step bridge.riverStep).1
    have only := (twoLayerBidirectionalRows_step (bridge.arcStep 0)).1
    have equal : twoLayerBidirectionalRows bridge.river = twoLayerBidirectionalRows (bridge.arc 0) :=
      river.trans only.symm
    exact bridge.river_ne_arc 0 (twoLayerBidirectionalRows_injective equal)
  · have first : (bridge.vertex 0).val < a ↔ ¬ (bridge.vertex 1).val < a :=
      (twoLayerBidirectionalRows_step (bridge.arcStep 0)).2
    have second : (bridge.vertex 1).val < a ↔ ¬ (bridge.vertex 2).val < a :=
      (twoLayerBidirectionalRows_step (bridge.arcStep 1)).2
    have river : (bridge.vertex 0).val < a ↔ ¬ (bridge.vertex 2).val < a :=
      (twoLayerBidirectionalRows_step bridge.riverStep).2
    tauto

private theorem twoLayer_rows_of_budget {a b p : ℕ} (enough : p ≤ a+b+2*(a*b)) :
    ∃ paths : Fin p → List (Fin (a+b)), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧
      ∀ cutoff, BridgeFree (Before (@twoLayerBidirectionalRows a b)) cutoff → BridgeFree (Before paths) cutoff := by
  have count : Fintype.card (TwoLayerRow a b) = a+b+2*(a*b) := by
    simp only [TwoLayerRow,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
    ring
  let labels (i : Fin p) : TwoLayerRow a b := (Fintype.equivFinOfCardEq count).symm (Fin.castLE enough i)
  have labelsInjective : Function.Injective labels :=
    (Fintype.equivFinOfCardEq count).symm.injective.comp (Fin.castLE_injective _)
  let paths (i : Fin p) := twoLayerBidirectionalRows (labels i)
  have rows (i : Fin p) : paths i ≠ [] ∧ (paths i).Nodup := by
    unfold paths
    rcases labels i with ⟨reverse,u,v⟩ | v
    · cases reverse <;> simp [twoLayerBidirectionalRows,layer_vertices_different u v,(layer_vertices_different u v).symm]
    · simp [twoLayerBidirectionalRows]
  exact ⟨paths,twoLayerBidirectionalRows_injective.comp labelsInjective,rows,
    fun _ free _ bound => ⟨fun bridge => (free bound).false
      (bridge.mapPaths labels labelsInjective (fun _ _ _ step => step))⟩⟩

/-- Both orientations across the two balanced parts, together with all
singletons, attain the exact row-count upper bound at full cutoff three. -/
theorem literal_full_three_feasible_iff {n p : ℕ} :
    (∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) 3) ↔ p ≤ n+2*((n/2)*(n-n/2)) := by
  constructor
  · rintro ⟨paths,distinct,rows,free⟩
    exact literal_full_path_count_le_balanced_bipartite paths distinct (fun i => (rows i).1)
      (fun i => (rows i).2) free le_rfl
  · intro enough
    let a := n/2
    let b := n-a
    have vertices : a+b = n := Nat.add_sub_of_le (Nat.div_le_self n 2)
    obtain ⟨paths,unique,rows,free⟩ := twoLayer_rows_of_budget (show p ≤ a+b+2*(a*b) by rw [vertices]; exact enough)
    have witness : ∃ paths : Fin p → List (Fin (a+b)), Function.Injective paths ∧
        (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) 3 :=
      ⟨paths,unique,rows,free 3 (twoLayerBidirectionalRows_full_three a b)⟩
    exact vertices ▸ witness

/-- One orientation of the balanced bipartite arcs gives any prescribed
number of two-vertex rows up to the side product. Singleton rows can
be added independently, with full exclusion at every size. -/
theorem literal_full_all_short_rows {n darts singles : ℕ}
    (dartBudget : darts ≤ (n/2)*(n-n/2)) (singletonBudget : singles ≤ n) :
    ∃ paths : Fin (darts+singles) → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧
      (∀ d, IsEmpty (Bridge (Before paths) d)) ∧ (∑ i, (paths i).length) = 2*darts+singles := by
  let a := n/2
  let b := n-a
  have vertices : a+b = n := Nat.add_sub_of_le (Nat.div_le_self n 2)
  let pair (i : Fin darts) : Fin a × Fin b := finProdFinEquiv.symm (Fin.castLE dartBudget i)
  have pairInjective : Function.Injective pair := finProdFinEquiv.symm.injective.comp (Fin.castLE_injective _)
  let label : Fin darts ⊕ Fin singles → TwoLayerRow a b
    | Sum.inl i => Sum.inl (false,(pair i).1,(pair i).2)
    | Sum.inr j => Sum.inr (Fin.castLE (vertices ▸ singletonBudget) j)
  have labelInjective : Function.Injective label := by
    rintro (i | i) (j | j) same
    · have ends : (pair i).1 = (pair j).1 ∧ (pair i).2 = (pair j).2 := by
        simpa only [label,Sum.inl.injEq,Prod.mk.injEq,true_and] using same
      exact congrArg Sum.inl (pairInjective (Prod.ext ends.1 ends.2))
    · exact (Sum.inl_ne_inr same).elim
    · exact (Sum.inr_ne_inl same).elim
    · exact congrArg Sum.inr (Fin.castLE_injective _ (Sum.inr.inj same))
  let rows (i : Fin darts ⊕ Fin singles) := twoLayerBidirectionalRows (label i)
  have rowsInjective : Function.Injective rows := twoLayerBidirectionalRows_injective.comp labelInjective
  have well (i : Fin darts ⊕ Fin singles) : rows i ≠ [] ∧ (rows i).Nodup := by
    cases i with
    | inl i => simp [rows,label,twoLayerBidirectionalRows,layer_vertices_different]
    | inr j => simp [rows,label,twoLayerBidirectionalRows]
  have forward {i x y} (step : Before rows i x y) : x.val < a ∧ ¬ y.val < a := by
    cases i with
    | inl i =>
      obtain ⟨rfl,rfl⟩ := listBefore_endpoints_of_pair (rfl : rows (Sum.inl i) =
        [Fin.castAdd b (pair i).1,Fin.natAdd a (pair i).2]) step
      exact ⟨(pair i).1.isLt,by change ¬ a+(pair i).2.val < a; omega⟩
    | inr j =>
      have both : x = Fin.castLE (vertices ▸ singletonBudget) j ∧ y = Fin.castLE (vertices ▸ singletonBudget) j := by
        simpa [rows,label,twoLayerBidirectionalRows] using And.intro step.1 step.2.1
      exact (listBefore_ne step (both.1.trans both.2.symm)).elim
  have all (d : ℕ) : IsEmpty (Bridge (Before rows) d) := by
    refine ⟨fun bridge => ?_⟩
    cases d with
    | zero =>
      have river := (twoLayerBidirectionalRows_step (i := label bridge.river) bridge.riverStep).1
      have arc := (twoLayerBidirectionalRows_step (i := label (bridge.arc 0)) (bridge.arcStep 0)).1
      exact bridge.river_ne_arc 0 (rowsInjective (river.trans arc.symm))
    | succ d =>
      exact (forward (bridge.arcStep 0)).2 (forward (bridge.arcStep 1)).1
  have count : Fintype.card (Fin darts ⊕ Fin singles) = darts+singles := by simp
  let order := (Fintype.equivFinOfCardEq count).symm
  let paths (i : Fin (darts+singles)) := rows (order i)
  have total : (∑ i, (paths i).length) = 2*darts+singles := by
    calc
      _ = ∑ i, (rows i).length := Equiv.sum_comp order (fun i => (rows i).length)
      _ = _ := by
        rw [Fintype.sum_sum_type]
        simp [rows,label,twoLayerBidirectionalRows,Nat.mul_comm]
  have witness : ∃ paths : Fin (darts+singles) → List (Fin (a+b)), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧
      (∀ d, IsEmpty (Bridge (Before paths) d)) ∧ (∑ i, (paths i).length) = 2*darts+singles :=
    ⟨paths,rowsInjective.comp order.injective,fun i => well (order i),
      fun d => ⟨fun bridge => (all d).false (bridge.mapPaths order order.injective (fun _ _ _ step => step))⟩,total⟩
  exact vertices ▸ witness

/-- Whenever the literal full cutoff-three row-count bound holds, there
is an all-size full-free literal family of mass exactly the original row
budget, using at most that many rows on the original vertex ground set. -/
theorem literal_full_all_mass_at_path_budget {n p : ℕ} (enough : p ≤ n+2*((n/2)*(n-n/2))) :
    ∃ q ≤ p, ∃ paths : Fin q → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧
      (∀ d, IsEmpty (Bridge (Before paths) d)) ∧ (∑ i, (paths i).length) = p := by
  let capacity := (n/2)*(n-n/2)
  let darts := min capacity (p/2)
  let singles := p-2*darts
  have fits : 2*darts ≤ p := by
    have bound : darts ≤ p/2 := min_le_right _ _
    omega
  have singlesFit : singles ≤ n := by
    by_cases budget : capacity ≤ p/2
    · dsimp [singles,darts]
      rw [min_eq_left budget]
      change p ≤ n+2*capacity at enough
      omega
    · have hn : 0 < n := by
        by_contra! empty
        have zero : n = 0 := by omega
        simp [capacity,zero] at budget
      dsimp [singles,darts]
      rw [min_eq_right (le_of_not_ge budget)]
      omega
  obtain ⟨paths,unique,well,all,total⟩ := literal_full_all_short_rows (n := n) (singles := singles)
    (min_le_left capacity (p/2)) singlesFit
  exact ⟨darts+singles,by dsimp [singles]; omega,paths,unique,well,all,by rw [total]; dsimp [singles]; omega⟩

private theorem twoLayerBidirectionalRows_all_of_one_left (b d : ℕ) :
    IsEmpty (Bridge (Before (@twoLayerBidirectionalRows 1 b)) d) := by
  refine ⟨fun bridge => ?_⟩
  obtain ⟨river,side⟩ := twoLayerBidirectionalRows_step bridge.riverStep
  by_cases startsLeft : (bridge.vertex 0).val < 1
  · let i := Fin.last d
    obtain ⟨lastArc,arcSide⟩ := twoLayerBidirectionalRows_step (bridge.arcStep i)
    have onRight : ¬ (bridge.vertex i.succ).val < 1 := side.mp startsLeft
    have fromLeft : (bridge.vertex i.castSucc).val < 1 := arcSide.mpr onRight
    have same : bridge.vertex 0 = bridge.vertex i.castSucc := Fin.ext (by omega)
    rw [same] at river
    exact bridge.river_ne_arc i (twoLayerBidirectionalRows_injective (river.trans lastArc.symm))
  · obtain ⟨firstArc,arcSide⟩ := twoLayerBidirectionalRows_step (bridge.arcStep 0)
    have endsLeft : (bridge.vertex (Fin.last (d+1))).val < 1 := by
      by_contra absent
      exact startsLeft (side.mpr absent)
    have toLeft : (bridge.vertex (0 : Fin (d+1)).succ).val < 1 := by
      by_contra absent
      exact startsLeft (arcSide.mpr absent)
    have same : bridge.vertex (Fin.last (d+1)) = bridge.vertex (0 : Fin (d+1)).succ := Fin.ext (by omega)
    rw [same] at river
    exact bridge.river_ne_arc 0 (twoLayerBidirectionalRows_injective (river.trans firstArc.symm))

/-- A bidirectional star and singleton rows realize every literal row
count up to `n + 2*(n-1)`, with full exclusion at all sizes. -/
theorem literal_full_all_star_rows {n p : ℕ} (budget : p ≤ n+2*(n-1)) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ ∀ d, IsEmpty (Bridge (Before paths) d) := by
  cases n with
  | zero =>
    have empty : p = 0 := by omega
    subst p
    exact ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0,fun d => ⟨fun bridge => bridge.river.elim0⟩⟩
  | succ b =>
    have nEq : 1+b = b+1 := Nat.add_comm _ _
    have fits : p ≤ 1+b+2*(1*b) := by rw [nEq,Nat.one_mul]; simpa using budget
    obtain ⟨paths,unique,rows,free⟩ := twoLayer_rows_of_budget fits
    have witness : ∃ paths : Fin p → List (Fin (1+b)), Function.Injective paths ∧
        (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ ∀ d, IsEmpty (Bridge (Before paths) d) :=
      ⟨paths,unique,rows,fun d => free (d+2) (fun r _ => twoLayerBidirectionalRows_all_of_one_left b r) le_rfl⟩
    exact nEq ▸ witness

end OnlineReachabilityPreservers
