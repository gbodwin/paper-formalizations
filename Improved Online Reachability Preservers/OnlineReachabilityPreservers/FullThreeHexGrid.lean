import OnlineReachabilityPreservers.LocalOrderExtremal

/-! Three cyclically oriented directions on a finite hexagonal grid. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Prod.Lex
local notation "Before" => SourceAudit.BeforeIn

abbrev HexGridCoordinate (w : ℕ) := Fin (2*w-1)
abbrev HexGridPoint (w : ℕ) := {v : HexGridCoordinate w ×ₗ HexGridCoordinate w //
  w-1 ≤ (ofLex v).1.val+(ofLex v).2.val ∧ (ofLex v).1.val+(ofLex v).2.val ≤ 3*(w-1)}
abbrev HexGridPath (w : ℕ) := Fin 3 ×ₗ HexGridCoordinate w

private def hexX {w} (v : HexGridPoint w) : ℕ := (ofLex v.val).1.val
private def hexY {w} (v : HexGridPoint w) : ℕ := (ofLex v.val).2.val
private def hexDir {w} (i : HexGridPath w) : Fin 3 := (ofLex i).1
private def hexLine {w} (i : HexGridPath w) : ℕ := (ofLex i).2.val

private def hexKey {w} (direction : Fin 3) (v : HexGridPoint w) : ℕ :=
  if direction = 0 then hexX v else if direction = 1 then hexY v else hexX v+hexY v-(w-1)

private def hexGridMembers {w} (i : HexGridPath w) : Finset (HexGridPoint w) :=
  univ.filter fun v => hexKey (hexDir i) v = hexLine i

/-- The three directions are downwards, rightwards, and up-left along a
fixed sum of coordinates. -/
def hexGridRows (w : ℕ) (i : HexGridPath w) : List (HexGridPoint w) :=
  if hexDir i = 1 then (hexGridMembers i).sort else (hexGridMembers i).sort (· ≥ ·)

private theorem hexGridRows_mem {w} {i : HexGridPath w} {v : HexGridPoint w} :
    v ∈ hexGridRows w i ↔ hexKey (hexDir i) v = hexLine i := by
  unfold hexGridRows
  split <;> simp [hexGridMembers]

theorem hexGridRows_simple {w} (i : HexGridPath w) : (hexGridRows w i).Nodup := by
  unfold hexGridRows
  split <;> exact sort_nodup _ _

private theorem hexGridRows_length_eq {w} (i : HexGridPath w) : (hexGridRows w i).length = (hexGridMembers i).card := by
  unfold hexGridRows
  split <;> exact length_sort _

private theorem hexPoint_ext {w} {a b : HexGridPoint w} (x : hexX a = hexX b) (y : hexY a = hexY b) : a = b :=
  Subtype.ext (ofLex.injective (Prod.ext (Fin.ext x) (Fin.ext y)))

private theorem hexPath_eq {w} {i j : HexGridPath w} (direction : hexDir i = hexDir j) (line : hexLine i = hexLine j) :
    i = j := ofLex.injective (Prod.ext direction (Fin.ext line))

private theorem hex_same_direction {w} {i j : HexGridPath w} {v : HexGridPoint w}
    (first : v ∈ hexGridRows w i) (second : v ∈ hexGridRows w j) (same : hexDir i = hexDir j) : i = j := by
  have key := hexGridRows_mem.mp first
  rw [same] at key
  exact hexPath_eq same (key.symm.trans (hexGridRows_mem.mp second))

private theorem listBefore_rel_of_pairwise {V I : Type*} [DecidableEq V]
    {paths : I → List V} {i : I} {a b : V} {r : V → V → Prop}
    (pairwise : (paths i).Pairwise r) (step : Before paths i a b) : r a b := by
  have apos := List.idxOf_lt_length_of_mem step.1
  have bpos := List.idxOf_lt_length_of_mem step.2.1
  have rel := List.pairwise_iff_getElem.mp pairwise _ _ apos bpos step.2.2
  rwa [List.getElem_idxOf apos,List.getElem_idxOf bpos] at rel

private theorem hex_step {w} {i : HexGridPath w} {a b : HexGridPoint w}
    (step : Before (hexGridRows w) i a b) :
    (hexDir i = 0 ∧ hexX a = hexX b ∧ hexY b < hexY a) ∨
    (hexDir i = 1 ∧ hexY a = hexY b ∧ hexX a < hexX b) ∨
    (hexDir i = 2 ∧ hexX a+hexY a = hexX b+hexY b ∧ hexX b < hexX a) := by
  have key : hexKey (hexDir i) a = hexKey (hexDir i) b :=
    (hexGridRows_mem.mp step.1).trans (hexGridRows_mem.mp step.2.1).symm
  have apart := listBefore_ne step
  by_cases east : hexDir i = 1
  · have y : hexY a = hexY b := by simpa [hexKey,east] using key
    have ordered : (hexGridRows w i).Pairwise (· ≤ ·) := by
      rw [hexGridRows,ite_eq_left east]
      exact pairwise_sort _ _
    have increasing : a < b := (listBefore_rel_of_pairwise ordered step).lt_of_ne apart
    have x : hexX a < hexX b := by
      rcases Prod.Lex.lt_iff.mp (show a.val < b.val from increasing) with less | ⟨_,less⟩
      · exact less
      · exact (Nat.ne_of_lt less y).elim
    exact Or.inr (Or.inl ⟨east,y,x⟩)
  have ordered : (hexGridRows w i).Pairwise (· ≥ ·) := by
    rw [hexGridRows,ite_eq_right east]
    exact pairwise_sort _ _
  have decreasing : b < a := (listBefore_rel_of_pairwise ordered step).lt_of_ne apart.symm
  by_cases south : hexDir i = 0
  · have x : hexX a = hexX b := by simpa [hexKey,south] using key
    have y : hexY b < hexY a := by
      rcases Prod.Lex.lt_iff.mp (show b.val < a.val from decreasing) with less | ⟨_,less⟩
      · exact (Nat.ne_of_lt less x.symm).elim
      · exact less
    exact Or.inl ⟨south,x,y⟩
  have dir : hexDir i = 2 := by
    have h := (hexDir i).isLt
    apply Fin.ext
    have a0 : (hexDir i).val ≠ 0 := fun e => south (Fin.ext e)
    have a1 : (hexDir i).val ≠ 1 := fun e => east (Fin.ext e)
    change (hexDir i).val = 2
    omega
  have ax : w-1 ≤ hexX a+hexY a := a.property.1
  have bx : w-1 ≤ hexX b+hexY b := b.property.1
  have sumEq : hexX a+hexY a = hexX b+hexY b := by
    simp only [hexKey,south,east,ite_false] at key
    omega
  have x : hexX b < hexX a := by
    rcases Prod.Lex.lt_iff.mp (show b.val < a.val from decreasing) with less | ⟨equal,less⟩
    · exact less
    · have h : hexX b = hexX a := congrArg Fin.val equal
      change hexY b < hexY a at less
      omega
  exact Or.inr (Or.inr ⟨dir,sumEq,x⟩)

/-- No three distinct cyclically oriented directions can support a
river and a two-step detour. Two rows in one direction are disjoint. -/
theorem hexGridRows_full_three (w : ℕ) : BridgeFree (Before (hexGridRows w)) 3 := by
  intro d small
  refine ⟨fun b => ?_⟩
  have length : d = 0 ∨ d = 1 := by omega
  rcases length with rfl | rfl
  · have r : Before (hexGridRows w) b.river (b.vertex 0) (b.vertex 1) := b.riverStep
    have a : Before (hexGridRows w) (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
    have different : hexDir b.river ≠ hexDir (b.arc 0) :=
      fun eq => b.river_ne_arc 0 (hex_same_direction r.1 a.1 eq)
    rcases hex_step r with r | r | r <;> rcases hex_step a with a | a | a <;> omega
  · have r : Before (hexGridRows w) b.river (b.vertex 0) (b.vertex 2) := b.riverStep
    have a : Before (hexGridRows w) (b.arc 0) (b.vertex 0) (b.vertex 1) := b.arcStep 0
    have c : Before (hexGridRows w) (b.arc 1) (b.vertex 1) (b.vertex 2) := b.arcStep 1
    have ra : hexDir b.river ≠ hexDir (b.arc 0) := fun eq => b.river_ne_arc 0 (hex_same_direction r.1 a.1 eq)
    have rc : hexDir b.river ≠ hexDir (b.arc 1) := fun eq => b.river_ne_arc 1 (hex_same_direction r.2.1 c.2.1 eq)
    have ac : hexDir (b.arc 0) ≠ hexDir (b.arc 1) := fun eq =>
      (by decide : (0:Fin 2) ≠ 1) (b.distinctArcs (hex_same_direction a.2.1 c.1 eq))
    rcases hex_step r with r | r | r <;> rcases hex_step a with a | a | a <;> rcases hex_step c with c | c | c <;> omega

/-- Every point lies on precisely one row in each of the three directions. -/
theorem hexGridRows_degree {w} (v : HexGridPoint w) :
    (occurrences (fun i => (hexGridRows w i).toFinset) v).card = 3 := by
  have keyFits (d : Fin 3) : hexKey d v < 2*w-1 := by
    by_cases south : d = 0
    · simp [hexKey,south,hexX]
    by_cases east : d = 1
    · simp [hexKey,east,hexY]
    have upper : hexX v+hexY v ≤ 3*(w-1) := v.property.2
    have nonempty := (ofLex v.val).1.isLt
    simp only [hexKey,south,east,ite_false]
    omega
  let row : Fin 3 ↪ HexGridPath w := ⟨fun d => toLex (d,⟨hexKey d v,keyFits d⟩),fun _ _ equal => congrArg hexDir equal⟩
  have same : occurrences (fun i => (hexGridRows w i).toFinset) v = univ.map row := by
    ext i
    simp only [mem_occurrences,List.mem_toFinset,hexGridRows_mem,mem_map,mem_univ,true_and]
    refine ⟨fun on => ⟨hexDir i,hexPath_eq rfl on⟩,?_⟩
    rintro ⟨d,rfl⟩
    rfl
  rw [same,card_map,card_univ,Fintype.card_fin]

private theorem hex_grid_side_bounds {w c : ℕ} (fit : c < 2*w-1) (j : Fin w) :
    let other := (w-1-c)+j.val
    other < 2*w-1 ∧ w-1 ≤ c+other ∧ c+other ≤ 3*(w-1) := by
  have hi := j.isLt
  dsimp only
  omega

private def hexPointOf (w x y : ℕ) (xFit : x < 2*w-1) (yFit : y < 2*w-1)
    (low : w-1 ≤ x+y) (high : x+y ≤ 3*(w-1)) : HexGridPoint w :=
  ⟨toLex (⟨x,xFit⟩,⟨y,yFit⟩),low,high⟩

private theorem hex_grid_diag_bounds {w c : ℕ} (fit : c < 2*w-1) (j : Fin w) :
    let x := (c-(w-1))+j.val
    let y := c+(w-1)-x
    x < 2*w-1 ∧ y < 2*w-1 ∧ x+y = c+(w-1) ∧ w-1 ≤ x+y ∧ x+y ≤ 3*(w-1) := by
  have hi := j.isLt
  dsimp only
  omega

/-- Every line in each direction has between `w` and `2w-1` points. -/
theorem hexGridRows_length {w} (i : HexGridPath w) : w ≤ (hexGridRows w i).length ∧ (hexGridRows w i).length ≤ 2*w-1 := by
  rw [hexGridRows_length_eq]
  have lower (f : Fin w → HexGridPoint w) (injective : Function.Injective f) (on : ∀ j, f j ∈ hexGridMembers i) :
      w ≤ (hexGridMembers i).card := by
    have bound : (univ : Finset (Fin w)).card ≤ (hexGridMembers i).card :=
      card_le_card_of_injOn f (fun j _ => on j) (fun _ _ _ _ equal => injective equal)
    simpa only [card_univ,Fintype.card_fin] using bound
  have upper (f : HexGridPoint w → HexGridCoordinate w) (injective : Set.InjOn f (hexGridMembers i)) :
      (hexGridMembers i).card ≤ 2*w-1 := by
    have bound : (hexGridMembers i).card ≤ (univ : Finset (HexGridCoordinate w)).card :=
      card_le_card_of_injOn f (fun v _ => mem_univ (f v)) injective
    simpa only [card_univ,Fintype.card_fin] using bound
  let c := hexLine i
  have cFits : c < 2*w-1 := (ofLex i).2.isLt
  have line {v} (on : v ∈ hexGridMembers i) : hexKey (hexDir i) v = c := (mem_filter.mp on).2
  have member {v} (on : hexKey (hexDir i) v = c) : v ∈ hexGridMembers i := mem_filter.mpr ⟨mem_univ _,on⟩
  by_cases south : hexDir i = 0
  · let f (j : Fin w) : HexGridPoint w :=
      let h := hex_grid_side_bounds cFits j
      hexPointOf w c ((w-1-c)+j.val) cFits h.1 h.2.1 h.2.2
    constructor
    · apply lower f
      · intro a b equal
        have same : (w-1-c)+a.val = (w-1-c)+b.val := congrArg hexY equal
        exact Fin.ext (by omega)
      · intro j
        exact member (by simp [f,hexKey,south,hexX,hexPointOf])
    · apply upper (fun v => (ofLex v.val).2)
      intro a ha b hb same
      have qa : hexX a = c := by simpa [hexKey,south] using line ha
      have qb : hexX b = c := by simpa [hexKey,south] using line hb
      exact hexPoint_ext (qa.trans qb.symm) (congrArg Fin.val same)
  by_cases east : hexDir i = 1
  · let f (j : Fin w) : HexGridPoint w :=
      let h := hex_grid_side_bounds cFits j
      hexPointOf w ((w-1-c)+j.val) c h.1 cFits (by simpa [Nat.add_comm] using h.2.1)
        (by simpa [Nat.add_comm] using h.2.2)
    constructor
    · apply lower f
      · intro a b equal
        have same : (w-1-c)+a.val = (w-1-c)+b.val := congrArg hexX equal
        exact Fin.ext (by omega)
      · intro j
        exact member (by simp [f,hexKey,east,hexY,hexPointOf])
    · apply upper (fun v => (ofLex v.val).1)
      intro a ha b hb same
      have qa : hexY a = c := by simpa [hexKey,south,east] using line ha
      have qb : hexY b = c := by simpa [hexKey,south,east] using line hb
      exact hexPoint_ext (congrArg Fin.val same) (qa.trans qb.symm)
  let f (j : Fin w) : HexGridPoint w :=
    let h := hex_grid_diag_bounds cFits j
    let x := (c-(w-1))+j.val
    let y := c+(w-1)-x
    hexPointOf w x y h.1 h.2.1 h.2.2.2.1 h.2.2.2.2
  constructor
  · apply lower f
    · intro a b equal
      have same : (c-(w-1))+a.val = (c-(w-1))+b.val := congrArg hexX equal
      exact Fin.ext (by omega)
    · intro j
      apply member
      have h := (hex_grid_diag_bounds cFits j).2.2.1
      change (c-(w-1)+j.val)+(c+(w-1)-(c-(w-1)+j.val)) = c+(w-1) at h
      simp only [hexKey,south,east,ite_false]
      change ((c-(w-1)+j.val)+(c+(w-1)-(c-(w-1)+j.val)))-(w-1) = c
      omega
  · apply upper (fun v => (ofLex v.val).1)
    intro a ha b hb same
    have x : hexX a = hexX b := congrArg Fin.val same
    have qa : hexX a+hexY a-(w-1) = c := by simpa [hexKey,south,east] using line ha
    have qb : hexX b+hexY b-(w-1) = c := by simpa [hexKey,south,east] using line hb
    have lowA : w-1 ≤ hexX a+hexY a := a.property.1
    have lowB : w-1 ≤ hexX b+hexY b := b.property.1
    exact hexPoint_ext x (by omega)

theorem hexGridRows_card_vertices (w : ℕ) : Fintype.card (HexGridPoint w) ≤ (2*w-1)^2 := calc
  _ ≤ Fintype.card (HexGridCoordinate w ×ₗ HexGridCoordinate w) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  _ = (2*w-1)^2 := by
    rw [Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_fin,pow_two]

theorem hexGridRows_card_paths (w : ℕ) : Fintype.card (HexGridPath w) = 3*(2*w-1) := by
  rw [Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]

theorem hexGridRows_mass (w : ℕ) : (∑ i, (hexGridRows w i).length) = 3*Fintype.card (HexGridPoint w) := calc
  _ = ∑ i, (hexGridRows w i).toFinset.card :=
    sum_congr rfl (fun i _ => (List.toFinset_card_of_nodup (hexGridRows_simple i)).symm)
  _ = ∑ v, (occurrences (fun i => (hexGridRows w i).toFinset) v).card :=
    (sum_occurrences (fun i => (hexGridRows w i).toFinset)).symm
  _ = _ := by simp [hexGridRows_degree,Nat.mul_comm]

end OnlineReachabilityPreservers
