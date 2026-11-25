import Mathlib.Data.Prod.Lex
import OnlineReachabilityPreservers.AcyclicOverlay
import OnlineReachabilityPreservers.CyclicReturnOverlay
import OnlineReachabilityPreservers.OfflineComponentOrders

/-! Lattice paths for the lower-bound direction of the Independence Lemma.
The acyclic overlay gives a superlinear lower bound. Adding return paths
produces counterexamples to the cited overlay argument for cyclic systems. -/

namespace OnlineReachabilityPreservers.SourceAudit

local notation "ListBefore" => BeforeIn

section LayeredPaths

open Finset

abbrev LatticeVertex (steps slopes : ℕ) :=
  Fin (steps+1) × Fin (2*(steps*slopes)) × Fin (2*(steps*slopes^2))
abbrev LatticeLine (steps slopes : ℕ) := Fin slopes × Fin (steps*slopes) × Fin (steps*slopes^2)

private def latticeVertex {steps slopes : ℕ} (line : LatticeLine steps slopes)
    (j : Fin (steps+1)) : LatticeVertex steps slopes :=
  (j,⟨line.2.1.val + j.val*line.1.val,by
    have step : j.val*line.1.val ≤ steps*slopes :=
      Nat.mul_le_mul (Nat.le_of_lt_succ j.isLt) line.1.isLt.le
    have start := line.2.1.isLt
    omega⟩,⟨line.2.2.val + j.val*line.1.val^2,by
    have step : j.val*line.1.val^2 ≤ steps*slopes^2 :=
      Nat.mul_le_mul (Nat.le_of_lt_succ j.isLt) (Nat.pow_le_pow_left line.1.isLt.le _)
    have start := line.2.2.isLt
    omega⟩)

def latticePaths {steps slopes : ℕ} (line : LatticeLine steps slopes) : List (LatticeVertex steps slopes) :=
  List.ofFn (latticeVertex line)

private theorem latticePaths_simple {steps slopes : ℕ} (line : LatticeLine steps slopes) : (latticePaths line).Nodup :=
  List.nodup_ofFn.mpr (fun _ _ same => congrArg Prod.fst same)

private theorem idxOf_ofFn_injective {W : Type*} [DecidableEq W] {m : ℕ}
    (f : Fin m → W) (injective : Function.Injective f) (j : Fin m) :
    (List.ofFn f).idxOf (f j) = j.val := by
  have inBounds : j.val < (List.ofFn f).length := by simp
  have atIndex : (List.ofFn f)[j.val]'inBounds = f j := List.getElem_ofFn inBounds
  rw [← atIndex, (List.nodup_ofFn.mpr injective).idxOf_getElem]

private theorem lattice_before_geometry {steps slopes : ℕ} {line : LatticeLine steps slopes} {a b : LatticeVertex steps slopes}
    (step : ListBefore latticePaths line a b) :
    0 < (b.1.val : ℤ) - a.1.val ∧
      (b.2.1.val : ℤ) - a.2.1.val = ((b.1.val : ℤ) - a.1.val)*line.1.val ∧
      (b.2.2.val : ℤ) - a.2.2.val = ((b.1.val : ℤ) - a.1.val)*(line.1.val : ℤ)^2 := by
  obtain ⟨ha,hb,less⟩ := step
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  have inj : Function.Injective (latticeVertex line) := fun _ _ same => congrArg Prod.fst same
  have order : i.val < j.val := by
    unfold latticePaths at less
    simpa only [idxOf_ofFn_injective (latticeVertex line) inj i,
      idxOf_ofFn_injective (latticeVertex line) inj j] using less
  refine ⟨by simpa [latticeVertex, sub_pos] using (Int.ofNat_lt.mpr order),?_,?_⟩
  · simp only [latticeVertex,Nat.cast_add,Nat.cast_mul]
    ring
  · simp only [latticeVertex,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
    ring

private theorem lattice_line_eq_of_slope_of_mem {steps slopes : ℕ} {a b : LatticeLine steps slopes} {w : LatticeVertex steps slopes}
    (slope : a.1 = b.1) (ha : w ∈ latticePaths a) (hb : w ∈ latticePaths b) : a = b := by
  obtain ⟨i,ia⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,jb⟩ := List.mem_ofFn.mp hb
  have equal := ia.trans jb.symm
  have layer : i = j := congrArg Prod.fst equal
  subst j
  apply Prod.ext slope
  apply Prod.ext
  · apply Fin.ext
    have x := congrArg (fun v : LatticeVertex steps slopes => v.2.1.val) equal
    change a.2.1.val + i.val*a.1.val = b.2.1.val + i.val*b.1.val at x
    rw [slope] at x
    exact Nat.add_right_cancel x
  · apply Fin.ext
    have y := congrArg (fun v : LatticeVertex steps slopes => v.2.2.val) equal
    change a.2.2.val + i.val*a.1.val^2 = b.2.2.val + i.val*b.1.val^2 at y
    rw [slope] at y
    exact Nat.add_right_cancel y

private theorem fin_telescope {k : ℕ} (f : Fin (k+2) → ℤ) :
    (∑ i : Fin (k+1), (f i.succ-f i.castSucc)) = f (Fin.last (k+1))-f 0 := by
  have first := Fin.sum_univ_succ f
  have last := Fin.sum_univ_castSucc f
  rw [sum_sub_distrib]
  linarith

/-- Each layer grows by one slope and its square. The river's weighted
variance across the arcs of a putative bridge is zero. -/
private theorem latticePaths_fullFree (steps slopes k : ℕ) : IsEmpty (Bridge (ListBefore (@latticePaths steps slopes)) k) := by
  refine ⟨fun b => ?_⟩
  let layer (j : Fin (k+2)) : ℤ := (b.vertex j).1.val
  let first (j : Fin (k+2)) : ℤ := (b.vertex j).2.1.val
  let second (j : Fin (k+2)) : ℤ := (b.vertex j).2.2.val
  let h (i : Fin (k+1)) := layer i.succ-layer i.castSucc
  let slope (i : Fin (k+1)) : ℤ := (b.arc i).1.val
  let r : ℤ := b.river.1.val
  let total := layer (Fin.last (k+1))-layer 0
  have step (i : Fin (k+1)) : 0 < h i ∧
      first i.succ-first i.castSucc = h i*slope i ∧
      second i.succ-second i.castSucc = h i*(slope i)^2 := lattice_before_geometry (b.arcStep i)
  have river : first (Fin.last (k+1))-first 0 = total*r ∧
      second (Fin.last (k+1))-second 0 = total*r^2 := (lattice_before_geometry b.riverStep).2
  have widths : (∑ i, h i) = total := fin_telescope layer
  have linear : ∑ i, h i*slope i = total*r := by
    simp_rw [← (fun i => (step i).2.1)]
    exact (fin_telescope first).trans river.1
  have squared : ∑ i, h i*(slope i)^2 = total*r^2 := by
    simp_rw [← (fun i => (step i).2.2)]
    exact (fin_telescope second).trans river.2
  have variance : ∑ i, h i*(slope i-r)^2 = 0 := by
    have expand (i : Fin (k+1)) : h i*(slope i-r)^2 = h i*(slope i)^2-(2*r)*(h i*slope i)+r^2*h i := by ring
    simp_rw [expand, sum_add_distrib, sum_sub_distrib, ← mul_sum, linear, squared, widths]
    ring
  have nonneg (i : Fin (k+1)) (_ : i ∈ univ) : 0 ≤ h i*(slope i-r)^2 :=
    mul_nonneg (step i).1.le (sq_nonneg _)
  have zero := (sum_eq_zero_iff_of_nonneg nonneg).mp variance (0 : Fin (k+1)) (mem_univ _)
  have square := (mul_eq_zero.mp zero).resolve_left (step 0).1.ne'
  have same : slope 0 = r := sub_eq_zero.mp (sq_eq_zero_iff.mp square)
  have labels : (b.arc 0).1 = b.river.1 := Fin.ext (Int.ofNat_inj.mp same)
  exact b.river_ne_arc 0 (lattice_line_eq_of_slope_of_mem labels (b.arcStep 0).1 b.riverStep.1).symm

end LayeredPaths

open Finset

abbrev OrderedLatticeVertex (steps slopes : ℕ) :=
  Fin (steps+1) ×ₗ (Fin (2*(steps*slopes)) ×ₗ Fin (2*(steps*slopes^2)))

private def latticeVertexOrder (steps slopes : ℕ) : LatticeVertex steps slopes ≃ OrderedLatticeVertex steps slopes :=
  ((Equiv.refl _).prodCongr toLex).trans toLex

theorem orderedLatticeVertex_card (steps slopes : ℕ) :
    Fintype.card (OrderedLatticeVertex steps slopes) = 4*(steps+1)*steps^2*slopes^3 := by
  rw [← Fintype.card_congr (latticeVertexOrder steps slopes)]
  simp only [LatticeVertex, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Each row visits all layers in order. Full bridge exclusion makes all of
their consecutive arcs necessary for the endpoints in the layered overlay. -/
private theorem offline_layered_paths {X W I : Type*} [DecidableEq X] [LinearOrder W] [Fintype W] [Fintype I]
    {steps : ℕ} (positive : 0 < steps) (order : X ≃ W)
    (row : I → Fin (steps+1) → Fin (steps+1) × X)
    (first : ∀ i j, (row i j).1 = j)
    (free : ∀ k, IsEmpty (Bridge (BeforeIn (fun i => List.ofFn (row i))) k)) :
    ∃ (G D : Arcs (Fin (steps+1) ×ₗ W)),
      IsDAG G ∧ D.card = Fintype.card I ∧ (∀ d ∈ D, Reach G d.1 d.2) ∧
      ∀ H ⊆ G, Preserves G H D.toList → H.card = steps*Fintype.card I := by
  classical
  let count := Fintype.card I
  let index := (Fintype.equivFin I).symm
  let vertex : (Fin (steps+1) × X) ≃ (Fin (steps+1) ×ₗ W) :=
    ((Equiv.refl _).prodCongr order).trans toLex
  let paths (i : Fin count) := (List.ofFn (row (index i))).toFinset.map vertex.toEmbedding
  have injective (i : I) : Function.Injective (row i) := by
    intro j q same
    simpa only [first] using congrArg Prod.fst same
  have pathSize (i : Fin count) : (paths i).card = steps+1 := by
    rw [Finset.card_map, List.toFinset_card_of_nodup (List.nodup_ofFn.mpr (injective _))]
    simp
  have nonempty (i : Fin count) : (paths i).Nonempty := Finset.card_pos.mp (by rw [pathSize]; omega)
  have legal (k : ℕ) : IsEmpty (Bridge (PathBefore paths) k) := by
    refine ⟨fun b => (free k).false ?_⟩
    have translate (i : Fin count) (u v : Fin (steps+1) ×ₗ W) (step : PathBefore paths i u v) :
        BeforeIn (fun i => List.ofFn (row i)) (index i) (vertex.symm u) (vertex.symm v) := by
      obtain ⟨left,right,forward⟩ := step
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp left
      obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp right
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp ha)
      obtain ⟨q,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hb)
      have firstOrdered : j < q := by
        change toLex ((row (index i) j).1, order (row (index i) j).2) <
          toLex ((row (index i) q).1, order (row (index i) q).2) at forward
        rcases Prod.Lex.toLex_lt_toLex.mp forward with less | ⟨equal,_⟩
        · simpa only [first] using less
        · simp only [first] at equal
          subst q
          exact (lt_irrefl _ forward).elim
      simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
      refine ⟨List.mem_ofFn.mpr ⟨j,rfl⟩,List.mem_ofFn.mpr ⟨q,rfl⟩,?_⟩
      simpa only [idxOf_ofFn_injective _ (injective (index i))]
        using (show j.val < q.val from firstOrdered)
    exact (b.mapVertices vertex.symm vertex.symm.injective translate).mapPaths index index.injective
      (fun _ _ _ h => h)
  obtain ⟨G, pairs, dag, length, service, all⟩ := theorem14_acyclic_overlay_lower nonempty legal
  have mass : (∑ i : Fin count, (paths i).card) = count*(steps+1) := by simp [pathSize]
  have retain (H : Arcs (Fin (steps+1) ×ₗ W)) (sub : H ⊆ G) (preserved : Preserves G H pairs) :
      H.card = count*steps := by
    have same := all H sub preserved
    rw [length, Fintype.card_fin, mass, Nat.mul_succ] at same
    omega
  have graph : G.card = count*steps := retain G Subset.rfl (fun _ _ => Iff.rfl)
  let possible : Arcs (Fin (steps+1) ×ₗ W) := univ.filter fun d => Reach G d.1 d.2
  have enough : count ≤ possible.card := by
    have subset : G ⊆ possible := fun d edge => mem_filter.mpr ⟨mem_univ _, Relation.ReflTransGen.single edge⟩
    exact (Nat.le_mul_of_pos_right count positive).trans (graph ▸ card_le_card subset)
  have included : pairs.toFinset ⊆ possible := fun d inside => mem_filter.mpr
    ⟨mem_univ _, service d (List.mem_toFinset.mp inside)⟩
  have small : pairs.toFinset.card ≤ count := List.toFinset_card_le _ |>.trans_eq (length.trans (Fintype.card_fin _))
  obtain ⟨D, original, possibleD, size⟩ := exists_subsuperset_card_eq included small enough
  refine ⟨G,D,dag,size,fun d hd => (mem_filter.mp (possibleD hd)).2,?_⟩
  intro H sub preserves
  exact (retain H sub (fun d hd => preserves d (Finset.mem_toList.mpr (original (List.mem_toFinset.mpr hd))))).trans (mul_comm _ _)

/-- Independent layer and slope counts give exact demand and edge counts. -/
theorem two_parameter_offline_lattice_lower {steps slopes : ℕ} (positive : 0 < steps) :
    ∃ (G : Arcs (OrderedLatticeVertex steps slopes)) (D : Arcs (OrderedLatticeVertex steps slopes)),
      IsDAG G ∧ D.card = steps^2*slopes^4 ∧ (∀ d ∈ D, Reach G d.1 d.2) ∧
        ∀ H ⊆ G, Preserves G H D.toList → H.card = steps^3*slopes^4 := by
  obtain ⟨G,D,dag,count,service,lower⟩ :=
    offline_layered_paths positive (toLex : (Fin (2*(steps*slopes)) × Fin (2*(steps*slopes^2))) ≃ _)
      (@latticeVertex steps slopes) (fun _ _ => rfl) (latticePaths_fullFree steps slopes)
  have labels : Fintype.card (LatticeLine steps slopes) = steps^2*slopes^4 := by
    simp [LatticeLine]
    ring
  refine ⟨G,D,dag,count.trans labels,service,fun H sub preserves => ?_⟩
  rw [lower H sub preserves, labels]
  ring

abbrev LayerVertex (L : ℕ) := LatticeVertex L L
abbrev LayerLine (L : ℕ) := LatticeLine L L

def layerPaths {L : ℕ} : LayerLine L → List (LayerVertex L) := latticePaths

abbrev OrderedLayerVertex (L : ℕ) := OrderedLatticeVertex L L

theorem orderedLayerVertex_card (L : ℕ) :
    Fintype.card (OrderedLayerVertex L) = 4*(L+1)*L^5 := by
  rw [orderedLatticeVertex_card]
  ring

private theorem layer_vertex_card_le {L : ℕ} (positive : 0 < L) :
    Fintype.card (LayerVertex L) ≤ 8*Fintype.card (LayerLine L) := by
  simp only [LayerVertex, LayerLine, LatticeVertex, LatticeLine, Fintype.card_prod, Fintype.card_fin]
  calc
    _ = 4*((L+1)*L^5) := by ring
    _ ≤ 4*((2*L)*L^5) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by ring

/-- Even a constant-factor lower bound can fail for the specific graph
and endpoint demands in the cited overlay proof. -/
theorem lemma14_overlay_no_constant (C : ℕ) :
    let L := 22*C+1
    let base := @layerPaths L
    let paths := returnPaths base
    let demands := returnedDemands (LayerVertex L) (LayerLine L)
    (∀ i, (paths i).Nodup) ∧ (∀ i, 0 < (paths i).length) ∧
      (∀ k, IsEmpty (Bridge (ListBefore paths) k)) ∧ demands.Nodup ∧
      ∃ H ⊆ returnedOverlay base, Preserves (returnedOverlay base) H demands ∧
        C*H.card + demands.length < ∑ i, (paths i).length := by
  let L := 22*C+1
  have positive : 0 < L := by omega
  let base := @layerPaths L
  let p := Fintype.card (LayerLine L)
  have count : p = L^6 := by
    simp only [p, Fintype.card_prod, Fintype.card_fin]
    ring
  have pPos : 0 < p := count.symm ▸ pow_pos positive 6
  refine ⟨returnPaths_nodup latticePaths_simple,returnPaths_length_pos _,
    returnPaths_fullFree base (latticePaths_fullFree L L),returnedDemands_nodup _ _,?_⟩
  obtain ⟨H,sub,small,serve⟩ := returnedOverlay_preserver base
  refine ⟨H,sub,serve,?_⟩
  have edges : H.card ≤ 22*p := by
    refine small.trans ?_
    have n := layer_vertex_card_le positive
    change Fintype.card (LayerVertex L) ≤ 8*p at n
    change 2*(Fintype.card (LayerVertex L)+3*p) ≤ 22*p
    omega
  have incidences : (L+1)*p + 6*p = ∑ i, (returnPaths base i).length := by
    rw [returnPaths_mass]
    have total : ∑ i, (base i).length = (L+1)*p := by
      simp only [base, layerPaths, latticePaths, List.length_ofFn, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Finset.card_univ]
      exact Nat.mul_comm _ _
    rw [total]
  rw [returnedDemands_length]
  change C*H.card + 3*p < ∑ i, (returnPaths base i).length
  calc
    C*H.card + 3*p ≤ C*(22*p) + 3*p := Nat.add_le_add_right (Nat.mul_le_mul_left _ edges) _
    _ = (22*C+3)*p := by ring
    _ < (L+1)*p + 6*p := by
      rw [← Nat.add_mul]
      exact Nat.mul_lt_mul_of_pos_right (by omega) pPos
    _ = _ := incidences

theorem orderedLayerVertex_card_bounds {L : ℕ} (positive : 0 < L) :
    4*L^6 ≤ Fintype.card (OrderedLayerVertex L) ∧ Fintype.card (OrderedLayerVertex L) ≤ 8*L^6 := by
  rw [orderedLayerVertex_card]
  have first : 4*L ≤ 4*(L+1) := by omega
  have last : 4*(L+1) ≤ 8*L := by omega
  constructor
  · calc
      4*L^6 = (4*L)*L^5 := by ring
      _ ≤ _ := Nat.mul_le_mul_right (L^5) first
  · calc
      _ ≤ (8*L)*L^5 := Nat.mul_le_mul_right (L^5) last
      _ = 8*L^6 := by ring

/-- The acyclic lattice family forces a superlinear number of edges in the
intermediate range with comparable vertex and demand counts. -/
theorem layered_offline_lower {L : ℕ} (positive : 0 < L) :
    ∃ (G : Arcs (OrderedLayerVertex L)) (D : Arcs (OrderedLayerVertex L)),
      IsDAG G ∧ D.card = L^6 ∧ (∀ d ∈ D, Reach G d.1 d.2) ∧
        ∀ H ⊆ G, Preserves G H D.toList → H.card = L^7 := by
  rw [← show L^2*L^4 = L^6 by ring, ← show L^3*L^4 = L^7 by ring]
  exact two_parameter_offline_lattice_lower (slopes := L) positive

private theorem grid_weighted_variance {I J : Type*} [Fintype I] [Fintype J]
    (h : I → ℤ) (a : I → J → ℤ) (r : J → ℤ) (total : ℤ)
    (positive : ∀ i, 0 < h i) (widths : ∑ i, h i = total)
    (linear : ∀ j, ∑ i, h i*a i j = total*r j)
    (energy : ∑ i, h i*(∑ j, (a i j)^2) = total*(∑ j, (r j)^2)) :
    ∀ i, a i = r := by
  have expand (i : I) (j : J) :
      h i*(a i j-r j)^2 = h i*(a i j)^2-(2*r j)*(h i*a i j)+(r j)^2*h i := by ring
  have first : (∑ i, ∑ j, h i*(a i j)^2) = total*(∑ j, (r j)^2) := by
    simp_rw [← mul_sum]
    exact energy
  have second : (∑ i, ∑ j, (2*r j)*(h i*a i j)) = 2*total*(∑ j, (r j)^2) := by
    rw [sum_comm]
    simp_rw [← mul_sum, linear, mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  have third : (∑ i, ∑ j, (r j)^2*h i) = total*(∑ j, (r j)^2) := by
    rw [sum_comm]
    simp_rw [← mul_sum, widths, mul_comm (total : ℤ), sum_mul]
  have variance : (∑ i, ∑ j, h i*(a i j-r j)^2) = 0 := by
    simp_rw [expand, sum_add_distrib, sum_sub_distrib]
    rw [first,second,third]
    ring
  have nonneg (i : I) (j : J) : 0 ≤ h i*(a i j-r j)^2 :=
    mul_nonneg (positive i).le (sq_nonneg _)
  intro i
  funext j
  have rowZero := (sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ univ) => sum_nonneg (fun j _ => nonneg i j))).mp variance i (mem_univ i)
  have entryZero := (sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ univ) => nonneg i j)).mp rowZero j (mem_univ j)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp entryZero).resolve_left (positive i).ne'))

abbrev GridGround (dimension steps slopes : ℕ) :=
  (Fin dimension → Fin (2*(steps*slopes))) × Fin (2*(steps*dimension*slopes^2))

abbrev GridVertex (dimension steps slopes : ℕ) :=
  Fin (steps+1) × GridGround dimension steps slopes

abbrev GridLine (dimension steps slopes : ℕ) :=
  (Fin dimension → Fin slopes) × ((Fin dimension → Fin (steps*slopes)) × Fin (steps*dimension*slopes^2))

private def gridEnergy {dimension slopes : ℕ} (s : Fin dimension → Fin slopes) : ℕ :=
  ∑ j, (s j).val^2

private theorem gridEnergy_le {dimension slopes : ℕ} (s : Fin dimension → Fin slopes) :
    gridEnergy s ≤ dimension*slopes^2 := by
  have each (j : Fin dimension) : (s j).val^2 ≤ slopes^2 :=
    Nat.pow_le_pow_left (s j).isLt.le 2
  unfold gridEnergy
  calc
    _ ≤ ∑ _ : Fin dimension, slopes^2 := sum_le_sum fun j _ => each j
    _ = _ := by simp

private def gridVertex {dimension steps slopes : ℕ} (line : GridLine dimension steps slopes)
    (i : Fin (steps+1)) : GridVertex dimension steps slopes :=
  (i, (fun j =>
    ⟨(line.2.1 j).val + i.val*(line.1 j).val, by
      have base := (line.2.1 j).isLt
      have advance : i.val*(line.1 j).val ≤ steps*slopes :=
        Nat.mul_le_mul (by omega) (line.1 j).isLt.le
      omega⟩),
    ⟨line.2.2.val + i.val*gridEnergy line.1, by
      have base := line.2.2.isLt
      have advance : i.val*gridEnergy line.1 ≤ steps*dimension*slopes^2 := by
        simpa only [Nat.mul_assoc] using
          (Nat.mul_le_mul (Nat.le_of_lt_succ i.isLt) (gridEnergy_le line.1))
      omega⟩)

private def gridPaths {dimension steps slopes : ℕ} (line : GridLine dimension steps slopes) :
    List (GridVertex dimension steps slopes) :=
  List.ofFn (gridVertex line)

private theorem gridVertex_injective {dimension steps slopes : ℕ} (line : GridLine dimension steps slopes) :
    Function.Injective (gridVertex line) := fun _ _ eq => congrArg Prod.fst eq

private theorem gridBefore_geometry {dimension steps slopes : ℕ} {line : GridLine dimension steps slopes}
    {u v : GridVertex dimension steps slopes} (step : BeforeIn gridPaths line u v) :
    let h := (v.1.val : ℤ) - u.1.val
    0 < h ∧ (∀ j, ((v.2.1 j).val : ℤ) - (u.2.1 j).val = h*(line.1 j).val) ∧
      (v.2.2.val : ℤ) - u.2.2.val = h*∑ j, ((line.1 j).val : ℤ)^2 := by
  obtain ⟨ha,hb,less⟩ := step
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  have stage : i.val < j.val := by
    unfold gridPaths at less
    simpa only [idxOf_ofFn_injective (gridVertex line) (gridVertex_injective line)] using less
  refine ⟨by simpa [gridVertex, sub_pos] using (Int.ofNat_lt.mpr stage),?_,?_⟩
  · intro q
    simp only [gridVertex, Nat.cast_add, Nat.cast_mul]
    ring
  · simp only [gridVertex, gridEnergy, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow]
    ring

private theorem grid_line_eq_of_slope_of_mem {dimension steps slopes : ℕ} {a b : GridLine dimension steps slopes}
    {w : GridVertex dimension steps slopes}
    (slope : a.1 = b.1) (ha : w ∈ gridPaths a) (hb : w ∈ gridPaths b) : a = b := by
  obtain ⟨i,ia⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,jb⟩ := List.mem_ofFn.mp hb
  have equal := ia.trans jb.symm
  have layer : i = j := congrArg Prod.fst equal
  subst j
  apply Prod.ext slope
  apply Prod.ext
  · funext q
    apply Fin.ext
    have same := congrArg (fun v : GridVertex dimension steps slopes => (v.2.1 q).val) equal
    change (a.2.1 q).val + i.val*(a.1 q).val = (b.2.1 q).val + i.val*(b.1 q).val at same
    rw [slope] at same
    exact Nat.add_right_cancel same
  · apply Fin.ext
    have same := congrArg (fun v : GridVertex dimension steps slopes => v.2.2.val) equal
    change a.2.2.val + i.val*gridEnergy a.1 = b.2.2.val + i.val*gridEnergy b.1 at same
    rw [slope] at same
    exact Nat.add_right_cancel same

/-- The layer increments force the directional variance of every alleged
bridge to vanish, even when the slope has several coordinates. -/
theorem gridPaths_fullFree (dimension steps slopes k : ℕ) :
    IsEmpty (Bridge (BeforeIn (@gridPaths dimension steps slopes)) k) := by
  refine ⟨fun b => ?_⟩
  let layer (j : Fin (k+2)) : ℤ := (b.vertex j).1.val
  let coordinate (q : Fin dimension) (j : Fin (k+2)) : ℤ := ((b.vertex j).2.1 q).val
  let squareCoordinate (j : Fin (k+2)) : ℤ := (b.vertex j).2.2.val
  let h (i : Fin (k+1)) := layer i.succ-layer i.castSucc
  let a (i : Fin (k+1)) (q : Fin dimension) : ℤ := ((b.arc i).1 q).val
  let r (q : Fin dimension) : ℤ := (b.river.1 q).val
  let total := layer (Fin.last (k+1))-layer 0
  have step (i : Fin (k+1)) : 0 < h i ∧
      (∀ q, coordinate q i.succ-coordinate q i.castSucc = h i*a i q) ∧
      squareCoordinate i.succ-squareCoordinate i.castSucc = h i*∑ q, (a i q)^2 :=
    gridBefore_geometry (b.arcStep i)
  have river : (∀ q, coordinate q (Fin.last (k+1))-coordinate q 0 = total*r q) ∧
      squareCoordinate (Fin.last (k+1))-squareCoordinate 0 = total*∑ q, (r q)^2 :=
    (gridBefore_geometry b.riverStep).2
  have widths : ∑ i, h i = total := fin_telescope layer
  have linear (q : Fin dimension) : ∑ i, h i*a i q = total*r q := by
    simp_rw [← (fun i => (step i).2.1 q)]
    exact (fin_telescope (coordinate q)).trans (river.1 q)
  have energy : ∑ i, h i*(∑ q, (a i q)^2) = total*(∑ q, (r q)^2) := by
    simp_rw [← (fun i => (step i).2.2)]
    exact (fin_telescope squareCoordinate).trans river.2
  have same := grid_weighted_variance h a r total (fun i => (step i).1) widths linear energy
  have label : (b.arc 0).1 = b.river.1 :=
    funext fun q => Fin.ext (Int.ofNat_inj.mp (congrFun (same 0) q))
  exact b.river_ne_arc 0 (grid_line_eq_of_slope_of_mem label (b.arcStep 0).1 b.riverStep.1).symm

abbrev OrderedGridVertex (dimension steps slopes : ℕ) :=
  Fin (steps+1) ×ₗ Fin (Fintype.card (GridGround dimension steps slopes))

theorem orderedGridVertex_card (dimension steps slopes : ℕ) :
    Fintype.card (OrderedGridVertex dimension steps slopes) =
      (steps+1)*(2*(steps*slopes))^dimension*(2*(steps*dimension*slopes^2)) := by
  simp [OrderedGridVertex, GridGround, Fintype.card_prod, Fintype.card_pi, mul_assoc]

theorem gridLine_card (dimension steps slopes : ℕ) :
    Fintype.card (GridLine dimension steps slopes) =
      slopes^dimension*(steps*slopes)^dimension*(steps*dimension*slopes^2) := by
  simp [GridLine, Fintype.card_prod, Fintype.card_pi, mul_assoc]

/-- The multidimensional paraboloid gives an exact-size DAG with distinct
reachable demands, each forcing all of its consecutive edges. -/
theorem multidimensional_offline_lattice_lower {dimension steps slopes : ℕ} (positive : 0 < steps) :
    ∃ (G D : Arcs (OrderedGridVertex dimension steps slopes)),
      IsDAG G ∧ D.card = slopes^dimension*(steps*slopes)^dimension*(steps*dimension*slopes^2) ∧
      (∀ d ∈ D, Reach G d.1 d.2) ∧ ∀ H ⊆ G, Preserves G H D.toList → H.card = steps*D.card := by
  obtain ⟨G,D,dag,size,reachable,lower⟩ :=
    offline_layered_paths positive (Fintype.equivFin (GridGround dimension steps slopes))
      (@gridVertex dimension steps slopes) (fun _ _ => rfl) (gridPaths_fullFree dimension steps slopes)
  exact ⟨G,D,dag,size.trans (gridLine_card _ _ _),reachable,fun H sub preserves =>
    (lower H sub preserves).trans (congrArg (steps * ·) size.symm)⟩

private theorem layerPaths_unique {L : ℕ} {i j : LayerLine L} {x y : LayerVertex L}
    (distinct : i ≠ j) (xi : x ∈ layerPaths i) (xj : x ∈ layerPaths j)
    (yi : y ∈ layerPaths i) (yj : y ∈ layerPaths j) : x = y := by
  classical
  let number := Fintype.equivFin (LayerLine L)
  let _ : LinearOrder (LayerLine L) := LinearOrder.lift' number number.injective
  by_contra apart
  have noParallel {u v : LayerVertex L} (left : ListBefore layerPaths i u v)
      (right : ListBefore layerPaths j u v) : False :=
    no_parallel_list_steps (fun k _ b _ => (latticePaths_fullFree L L k).false b)
      (by decide : 2 ≤ 2) distinct left right
  rcases listBefore_total xi yi apart with up | down <;>
    rcases listBefore_total xj yj apart with forward | reverse
  · exact noParallel up forward
  · have a := (lattice_before_geometry up).1
    have b := (lattice_before_geometry reverse).1
    omega
  · have a := (lattice_before_geometry down).1
    have b := (lattice_before_geometry forward).1
    omega
  · exact noParallel down reverse

/-- Even after opposite-intersection pruning, total component visits plus
the vertex count can be arbitrarily smaller than the incidence mass. -/
theorem lemma14_aggregate_component_mass_no_constant (C : ℕ) :
    ∃ n p : ℕ, 2 ≤ n ∧ 0 < p ∧ p ≤ n^2 ∧ ∃ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) ∧ (∀ i, paths i ≠ []) ∧
      (∀ k, IsEmpty (Bridge (ListBefore paths) k)) ∧
      (∀ i, removeOppositeIntersections paths i = paths i) ∧
      C * (n + ∑ i, ((paths i).toFinset.image (componentLabel (pathPrecedenceGraph paths))).card) <
        ∑ i, (paths i).length := by
  classical
  let L := 22*C+1
  have positive : 0 < L := by omega
  let base := @layerPaths L
  let rows := returnPaths base
  let W := ReturnVertex (LayerVertex L) (LayerLine L)
  let R := ReturnPath (LayerLine L)
  let n := Fintype.card W
  let p := Fintype.card R
  let q := Fintype.card (LayerLine L)
  let enc := Fintype.equivFin W
  let ind := Fintype.equivFin R
  let paths (i : Fin p) := (rows (ind.symm i)).map enc
  have nCount : n = Fintype.card (LayerVertex L) + 3*q := by
    change Fintype.card (ReturnVertex (LayerVertex L) (LayerLine L)) = _
    exact returnVertex_card
  have pCount : p = 3*q := by
    change Fintype.card (ReturnPath (LayerLine L)) = _
    exact returnPath_card _
  have qCount : q = L^6 := by
    simp only [q, Fintype.card_prod, Fintype.card_fin]
    ring
  have qPos : 0 < q := qCount.symm ▸ pow_pos positive 6
  have atLeastTwo : 2 ≤ n := by omega
  have vertexCount : n ≤ 11*q := by
    have vertices := layer_vertex_card_le positive
    change Fintype.card (LayerVertex L) ≤ 8*q at vertices
    omega
  have demandCount : p ≤ n^2 := by
    have small : p ≤ n := by omega
    exact small.trans (by rw [pow_two]; exact Nat.le_mul_self n)
  have simple (i : R) : (rows i).Nodup := returnPaths_nodup latticePaths_simple i
  have rankedSimple (i : Fin p) : (paths i).Nodup := (simple _).map enc.injective
  refine ⟨n,p,atLeastTwo,by omega,demandCount,paths,?_,?_,?_,?_,?_⟩
  · exact rankedSimple
  · intro i
    have nonzero : 0 < (paths i).length := by
      simpa only [paths, List.length_map] using returnPaths_length_pos base (ind.symm i)
    intro empty
    simp [empty] at nonzero
  · intro k
    refine ⟨fun b => (returnPaths_fullFree base (latticePaths_fullFree L L) k).false ?_⟩
    have undo (i : Fin p) : (paths i).map enc.symm = rows (ind.symm i) := by
      simp [paths, List.map_map, Function.comp_def]
    have back := b.mapVertices enc.symm enc.symm.injective (fun i x y step => by
      have moved := listBefore_map enc.symm ((undo i).symm ▸ simple (ind.symm i)) step
      simpa only [undo] using moved)
    exact back.mapPaths ind.symm ind.symm.injective (fun _ _ _ step => step)
  · intro i
    have inOriginal {j : Fin p} {x : Fin n} (on : x ∈ paths j) : enc.symm x ∈ rows (ind.symm j) := by
      obtain ⟨v, onRow, rfl⟩ := List.mem_map.mp on
      simpa only [Equiv.symm_apply_apply] using onRow
    have sub := removeOppositeIntersections_sublist paths i
    apply sub.eq_of_length_le
    rw [← List.toFinset_card_of_nodup (rankedSimple i),
      ← List.toFinset_card_of_nodup (sub.nodup (rankedSimple i))]
    apply card_le_card
    intro x present
    apply List.mem_toFinset.mpr
    refine (removeOppositeIntersections_mem paths i x).mpr ⟨List.mem_toFinset.mp present, ?_⟩
    rintro ⟨j, earlier, y, forward, reverse⟩
    have back : ListBefore paths j y x := removeOppositeIntersections_before rankedSimple reverse
    exact (listBefore_ne forward) (enc.symm.injective <|
      returnPaths_unique_intersections base (fun {_ _ _ _} => layerPaths_unique)
        (fun eq => earlier.ne (ind.symm.injective eq))
        (inOriginal back.2.1) (inOriginal forward.1) (inOriginal back.1) (inOriginal forward.2.1))
  · have visits := returnedRows_visit base latticePaths_simple enc ind
    change ∀ i, ((paths i).toFinset.image (componentLabel (pathPrecedenceGraph paths))).card = 1 at visits
    simp_rw [visits, sum_const, nsmul_eq_mul, Nat.cast_id, card_univ, Fintype.card_fin, Nat.mul_one]
    have mass : (∑ i, (paths i).length) = (L+7)*q := by
      simp only [paths, List.length_map]
      rw [Equiv.sum_comp ind.symm (fun i => (rows i).length)]
      change (∑ i, (returnPaths base i).length) = _
      rw [returnPaths_mass]
      have original : (∑ i, (base i).length) = q*(L+1) := by
        simp only [base, layerPaths, latticePaths, List.length_ofFn, sum_const, nsmul_eq_mul,
          Nat.cast_id, card_univ, q]
      rw [original]
      ring
    rw [mass, pCount]
    calc
      _ ≤ C * (14*q) := Nat.mul_le_mul_left _ (by omega)
      _ = (14*C)*q := by ring
      _ < _ := Nat.mul_lt_mul_of_pos_right (by omega) qPos

end OnlineReachabilityPreservers.SourceAudit
