import Mathlib.Data.Prod.Lex
import OnlineReachabilityPreservers.AcyclicOverlay
import OnlineReachabilityPreservers.CyclicReturnOverlay

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

private theorem latticeBefore_of_ordered {steps slopes : ℕ} {line : LatticeLine steps slopes} {u v : LatticeVertex steps slopes}
    (left : u ∈ latticePaths line) (right : v ∈ latticePaths line)
    (ordered : latticeVertexOrder steps slopes u < latticeVertexOrder steps slopes v) : ListBefore latticePaths line u v := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp left
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp right
  have neither : i ≠ j := fun equal => (lt_irrefl _ : ¬ latticeVertexOrder steps slopes (latticeVertex line i) < _)
    (equal.symm ▸ ordered)
  have stage : i < j := by
    change toLex (latticeVertex line i |>.1, toLex (latticeVertex line i |>.2)) <
      toLex (latticeVertex line j |>.1, toLex (latticeVertex line j |>.2)) at ordered
    rcases Prod.Lex.toLex_lt_toLex.mp ordered with less | ⟨equal,_⟩
    · exact less
    · exact (neither equal).elim
  have injective : Function.Injective (latticeVertex line) := fun _ _ same => congrArg Prod.fst same
  refine ⟨List.mem_ofFn.mpr ⟨i,rfl⟩, List.mem_ofFn.mpr ⟨j,rfl⟩, ?_⟩
  simpa only [latticePaths, idxOf_ofFn_injective (latticeVertex line) injective i,
    idxOf_ofFn_injective (latticeVertex line) injective j] using (show i.val < j.val from stage)

/-- Independent layer and slope counts give exact demand and edge counts. -/
theorem two_parameter_offline_lattice_lower {steps slopes : ℕ} (positive : 0 < steps) :
    ∃ (G : Arcs (OrderedLatticeVertex steps slopes)) (D : Arcs (OrderedLatticeVertex steps slopes)),
      IsDAG G ∧ D.card = steps^2*slopes^4 ∧ (∀ d ∈ D, Reach G d.1 d.2) ∧
        ∀ H ⊆ G, Preserves G H D.toList → H.card = steps^3*slopes^4 := by
  classical
  let count := Fintype.card (LatticeLine steps slopes)
  let line := (Fintype.equivFin (LatticeLine steps slopes)).symm
  let vertex := latticeVertexOrder steps slopes
  let paths (i : Fin count) := (latticePaths (line i)).toFinset.map vertex.toEmbedding
  have pathSize (i : Fin count) : (paths i).card = steps+1 := by
    rw [Finset.card_map, List.toFinset_card_of_nodup (latticePaths_simple _)]
    simp [latticePaths]
  have nonempty (i : Fin count) : (paths i).Nonempty := Finset.card_pos.mp (by rw [pathSize]; omega)
  have free (k : ℕ) : IsEmpty (Bridge (PathBefore paths) k) := by
    refine ⟨fun b => (latticePaths_fullFree steps slopes k).false ?_⟩
    have steps (i : Fin count) (u v : OrderedLatticeVertex steps slopes) (step : PathBefore paths i u v) :
        ListBefore latticePaths (line i) (vertex.symm u) (vertex.symm v) := by
      obtain ⟨left,right,forward⟩ := step
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp left
      obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp right
      simpa only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using
        latticeBefore_of_ordered (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) forward
    exact (b.mapVertices vertex.symm vertex.symm.injective steps).mapPaths line line.injective
      (fun _ _ _ h => h)
  rw [show steps^2*slopes^4 = count from (by simp [count]; ring)]
  obtain ⟨G, pairs, dag, length, service, all⟩ := theorem14_acyclic_overlay_lower nonempty free
  have mass : (∑ i : Fin count, (paths i).card) = count*(steps+1) := by simp [pathSize]
  have retain (H : Arcs (OrderedLatticeVertex steps slopes)) (sub : H ⊆ G) (preserved : Preserves G H pairs) : H.card = count*steps := by
    have same := all H sub preserved
    rw [length, Fintype.card_fin, mass, Nat.mul_succ] at same
    omega
  have graph : G.card = count*steps := retain G Subset.rfl (fun _ _ => Iff.rfl)
  let possible : Arcs (OrderedLatticeVertex steps slopes) := univ.filter fun d => Reach G d.1 d.2
  have enough : count ≤ possible.card := by
    have subset : G ⊆ possible := fun d edge => mem_filter.mpr ⟨mem_univ _, Relation.ReflTransGen.single edge⟩
    exact (Nat.le_mul_of_pos_right count positive).trans (graph ▸ card_le_card subset)
  have included : pairs.toFinset ⊆ possible := fun d inside => mem_filter.mpr
    ⟨mem_univ _, service d (List.mem_toFinset.mp inside)⟩
  have small : pairs.toFinset.card ≤ count := List.toFinset_card_le _ |>.trans_eq (length.trans (Fintype.card_fin _))
  obtain ⟨D, original, possibleD, size⟩ := exists_subsuperset_card_eq included small enough
  refine ⟨G,D,dag,size,fun d hd => (mem_filter.mp (possibleD hd)).2,?_⟩
  intro H sub preserves
  have result := retain H sub (fun d hd => preserves d (Finset.mem_toList.mpr (original (List.mem_toFinset.mpr hd))))
  rw [result]
  simp [count]
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

end OnlineReachabilityPreservers.SourceAudit
