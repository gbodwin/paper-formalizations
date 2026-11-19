import OnlineReachabilityPreservers.CyclicReturnOverlay

/-! A family of counterexamples to using the consecutive overlay for the
lower-bound direction of the Independence Lemma. -/

namespace OnlineReachabilityPreservers.SourceAudit

local notation "ListBefore" => BeforeIn

section LayeredPaths

open Finset

abbrev LayerVertex (L : ℕ) := Fin (L+1) × Fin (2*L^2) × Fin (2*L^3)
abbrev LayerLine (L : ℕ) := Fin L × Fin (L^2) × Fin (L^3)

private def layerVertex {L : ℕ} (line : LayerLine L) (j : Fin (L+1)) : LayerVertex L :=
  (j,⟨line.2.1.val + j.val*line.1.val,by
    have step : j.val*line.1.val ≤ L^2 := by
      simpa only [pow_two] using Nat.mul_le_mul (Nat.le_of_lt_succ j.isLt) line.1.isLt.le
    have start := line.2.1.isLt
    omega⟩,⟨line.2.2.val + j.val*line.1.val^2,by
    have step : j.val*line.1.val^2 ≤ L*L^2 :=
      Nat.mul_le_mul (Nat.le_of_lt_succ j.isLt) (Nat.pow_le_pow_left line.1.isLt.le _)
    rw [show L*L^2 = L^3 by ring] at step
    have start := line.2.2.isLt
    omega⟩)

def layerPaths {L : ℕ} (line : LayerLine L) : List (LayerVertex L) :=
  List.ofFn (layerVertex line)

private theorem layerPaths_simple {L : ℕ} (line : LayerLine L) : (layerPaths line).Nodup :=
  List.nodup_ofFn.mpr (fun _ _ same => congrArg Prod.fst same)

private theorem idxOf_ofFn_injective {W : Type*} [DecidableEq W] {m : ℕ}
    (f : Fin m → W) (injective : Function.Injective f) (j : Fin m) :
    (List.ofFn f).idxOf (f j) = j.val := by
  have inBounds : j.val < (List.ofFn f).length := by simp
  have atIndex : (List.ofFn f)[j.val]'inBounds = f j := List.getElem_ofFn inBounds
  rw [← atIndex, (List.nodup_ofFn.mpr injective).idxOf_getElem]

private theorem layer_before_geometry {L : ℕ} {line : LayerLine L} {a b : LayerVertex L}
    (step : ListBefore layerPaths line a b) :
    0 < (b.1.val : ℤ) - a.1.val ∧
      (b.2.1.val : ℤ) - a.2.1.val = ((b.1.val : ℤ) - a.1.val)*line.1.val ∧
      (b.2.2.val : ℤ) - a.2.2.val = ((b.1.val : ℤ) - a.1.val)*(line.1.val : ℤ)^2 := by
  obtain ⟨ha,hb,less⟩ := step
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  have inj : Function.Injective (layerVertex line) := fun _ _ same => congrArg Prod.fst same
  have order : i.val < j.val := by
    unfold layerPaths at less
    simpa only [idxOf_ofFn_injective (layerVertex line) inj i,
      idxOf_ofFn_injective (layerVertex line) inj j] using less
  refine ⟨by simpa [layerVertex, sub_pos] using (Int.ofNat_lt.mpr order),?_,?_⟩
  · simp only [layerVertex,Nat.cast_add,Nat.cast_mul]
    ring
  · simp only [layerVertex,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
    ring

private theorem layer_line_eq_of_slope_of_mem {L : ℕ} {a b : LayerLine L} {w : LayerVertex L}
    (slope : a.1 = b.1) (ha : w ∈ layerPaths a) (hb : w ∈ layerPaths b) : a = b := by
  obtain ⟨i,ia⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,jb⟩ := List.mem_ofFn.mp hb
  have equal := ia.trans jb.symm
  have layer : i = j := congrArg Prod.fst equal
  subst j
  apply Prod.ext slope
  apply Prod.ext
  · apply Fin.ext
    have x := congrArg (fun v : LayerVertex L => v.2.1.val) equal
    change a.2.1.val + i.val*a.1.val = b.2.1.val + i.val*b.1.val at x
    rw [slope] at x
    exact Nat.add_right_cancel x
  · apply Fin.ext
    have y := congrArg (fun v : LayerVertex L => v.2.2.val) equal
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
private theorem layerPaths_fullFree (L : ℕ) (k : ℕ) : IsEmpty (Bridge (ListBefore (@layerPaths L)) k) := by
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
      second i.succ-second i.castSucc = h i*(slope i)^2 := layer_before_geometry (b.arcStep i)
  have river : first (Fin.last (k+1))-first 0 = total*r ∧
      second (Fin.last (k+1))-second 0 = total*r^2 := (layer_before_geometry b.riverStep).2
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
  exact b.river_ne_arc 0 (layer_line_eq_of_slope_of_mem labels (b.arcStep 0).1 b.riverStep.1).symm

end LayeredPaths

open Finset

private theorem layer_vertex_card_le {L : ℕ} (positive : 0 < L) :
    Fintype.card (LayerVertex L) ≤ 8*Fintype.card (LayerLine L) := by
  simp only [LayerVertex, LayerLine, Fintype.card_prod, Fintype.card_fin]
  calc
    (L+1)*(2*L^2*(2*L^3)) = 4*((L+1)*L^5) := by ring
    _ ≤ 4*((2*L)*L^5) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    _ = 8*(L*(L^2*L^3)) := by ring

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
  refine ⟨returnPaths_nodup layerPaths_simple,returnPaths_length_pos _,
    returnPaths_fullFree base (layerPaths_fullFree L),returnedDemands_nodup _ _,?_⟩
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
      simp only [base, layerPaths, List.length_ofFn, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Finset.card_univ]
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

end OnlineReachabilityPreservers.SourceAudit
