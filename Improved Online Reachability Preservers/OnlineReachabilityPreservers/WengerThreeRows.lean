import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Vandermonde
import OnlineReachabilityPreservers.LocalAverageCleaning
import OnlineReachabilityPreservers.HalfThreeUpstreamMass

/-! Regular full-three-free rows from affine lines with moment-curve slopes. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private abbrev FieldTriple (F : Type*) := F × F × F

variable {F : Type*} [Field F] [Fintype F]

private def affinePoint (line : FieldTriple F) (x : F) : FieldTriple F :=
  (x,line.2.1+line.1*x,line.2.2+line.1^2*x)

private noncomputable def affineRow (line : FieldTriple F) : List (FieldTriple F) :=
  List.ofFn (fun i : Fin (Fintype.card F) => affinePoint line ((Fintype.equivFin F).symm i))

private theorem affineRow_simple (line : FieldTriple F) : (affineRow line).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j same
  exact (Fintype.equivFin F).symm.injective (congrArg Prod.fst same)

private theorem mem_affineRow {line v : FieldTriple F} :
    v ∈ affineRow line ↔ v.2.1 = line.2.1+line.1*v.1 ∧ v.2.2 = line.2.2+line.1^2*v.1 := by
  rw [affineRow,List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨rfl,rfl⟩
  · intro eq
    refine ⟨Fintype.equivFin F v.1,?_⟩
    rw [Equiv.symm_apply_apply]
    exact Prod.ext rfl (Prod.ext eq.1.symm eq.2.symm)

private theorem affineRows_slope_owner {a b x : FieldTriple F} (slope : a.1 = b.1)
    (first : x ∈ affineRow a) (next : x ∈ affineRow b) : a = b := by
  obtain ⟨ay,az⟩ := mem_affineRow.mp first
  obtain ⟨by_,bz⟩ := mem_affineRow.mp next
  rw [slope] at ay az
  exact Prod.ext slope (Prod.ext (by linear_combination by_ - ay) (by linear_combination bz - az))

private theorem affineRow_point_eq_of_first_eq {a x y : FieldTriple F} (first : x ∈ affineRow a)
    (next : y ∈ affineRow a) (same : x.1 = y.1) : x = y := by
  obtain ⟨xy,xz⟩ := mem_affineRow.mp first
  obtain ⟨yy,yz⟩ := mem_affineRow.mp next
  rw [same] at xy xz
  exact Prod.ext same (Prod.ext (xy.trans yy.symm) (xz.trans yz.symm))

private theorem affineRow_difference {line x y : FieldTriple F} (first : x ∈ affineRow line)
    (next : y ∈ affineRow line) :
    y.2.1-x.2.1 = (y.1-x.1)*line.1 ∧ y.2.2-x.2.2 = (y.1-x.1)*line.1^2 := by
  obtain ⟨xy,xz⟩ := mem_affineRow.mp first
  obtain ⟨yy,yz⟩ := mem_affineRow.mp next
  constructor
  · rw [xy,yy]; ring
  · rw [xz,yz]; ring

private theorem affineRows_pair_owner {a b x y : FieldTriple F} (apart : x ≠ y)
    (ax : x ∈ affineRow a) (ay : y ∈ affineRow a) (bx : x ∈ affineRow b) (by_ : y ∈ affineRow b) : a = b := by
  have position : y.1-x.1 ≠ 0 := sub_ne_zero.mpr (fun h => apart (affineRow_point_eq_of_first_eq ax ay h.symm))
  have first := (affineRow_difference ax ay).1
  have second := (affineRow_difference bx by_).1
  have product : (y.1-x.1)*(a.1-b.1) = 0 := by linear_combination second - first
  have slope : a.1 = b.1 := sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left position)
  exact affineRows_slope_owner slope ax bx

private theorem affineRows_no_triangle {a b r x y z : FieldTriple F}
    (ab : a ≠ b) (ra : r ≠ a) (rb : r ≠ b) (xz : x ≠ z)
    (ax : x ∈ affineRow a) (ay : y ∈ affineRow a) (by_ : y ∈ affineRow b)
    (bz : z ∈ affineRow b) (rx : x ∈ affineRow r) (rz : z ∈ affineRow r) : False := by
  let slope : Fin 3 → F := ![a.1,b.1,r.1]
  let changeX : Fin 3 → F := ![y.1-x.1,z.1-y.1,x.1-z.1]
  have abSlope : a.1 ≠ b.1 := fun eq => ab (affineRows_slope_owner eq ay by_)
  have raSlope : r.1 ≠ a.1 := fun eq => ra (affineRows_slope_owner eq rx ax)
  have rbSlope : r.1 ≠ b.1 := fun eq => rb (affineRows_slope_owner eq rz bz)
  have injective : Function.Injective slope := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp_all [slope]
  have first := affineRow_difference ax ay
  have second := affineRow_difference by_ bz
  have third := affineRow_difference rz rx
  have moments (j : Fin 3) : (∑ i : Fin 3, changeX i * slope i ^ (j:ℕ)) = 0 := by
    fin_cases j
    · simp [Fin.sum_univ_three,changeX,slope]
    · simp [Fin.sum_univ_three,changeX,slope]; linear_combination -first.1-second.1-third.1
    · simp [Fin.sum_univ_three,changeX,slope]; linear_combination -first.2-second.2-third.2
  have zero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero injective moments
  have last : x.1-z.1 = 0 := congrFun zero 2
  exact xz (affineRow_point_eq_of_first_eq rx rz (sub_eq_zero.mp last))

private theorem affineRows_fullThree [DecidableEq F] : BridgeFree (Before (affineRow (F := F))) 3 := by
  intro d size
  refine ⟨fun b => ?_⟩
  obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
  · exact b.river_ne_arc 0 (affineRows_pair_owner (listBefore_ne b.riverStep)
      b.riverStep.1 b.riverStep.2.1 (b.arcStep 0).1 (b.arcStep 0).2.1)
  · exact affineRows_no_triangle (fun eq => (by decide : (0:Fin 2) ≠ 1) (b.distinctArcs eq))
      (b.river_ne_arc 0) (b.river_ne_arc 1) (listBefore_ne b.riverStep)
      (b.arcStep 0).1 (b.arcStep 0).2.1 (b.arcStep 1).1 (b.arcStep 1).2.1 b.riverStep.1 b.riverStep.2.1

private theorem affineRows_injective : Function.Injective (affineRow (F := F)) := by
  intro a b equal
  let x := affinePoint a 0
  let y := affinePoint a 1
  have different : x ≠ y := fun h => zero_ne_one (congrArg Prod.fst h)
  have ax : x ∈ affineRow a := mem_affineRow.mpr ⟨rfl,rfl⟩
  have ay : y ∈ affineRow a := mem_affineRow.mpr ⟨rfl,rfl⟩
  exact affineRows_pair_owner different ax ay (equal ▸ ax) (equal ▸ ay)

private def lineThrough (v : FieldTriple F) (slope : F) : FieldTriple F :=
  (slope,v.2.1-slope*v.1,v.2.2-slope^2*v.1)

private theorem lineThrough_contains (v : FieldTriple F) (slope : F) : v ∈ affineRow (lineThrough v slope) :=
  mem_affineRow.mpr ⟨by simp [lineThrough],by simp [lineThrough]⟩

private theorem lineThrough_eq {v line : FieldTriple F} (on : v ∈ affineRow line) : lineThrough v line.1 = line := by
  obtain ⟨y,z⟩ := mem_affineRow.mp on
  exact Prod.ext rfl (Prod.ext (by rw [lineThrough]; dsimp; linear_combination y)
    (by rw [lineThrough]; dsimp; linear_combination z))

/-- Over a field of order `q`, the moment-slope lines give `q³` simple
distinct rows on `q³` vertices. Every row and every vertex have incidence
count `q`. The rows exclude full bridges through size three. -/
theorem wenger_full_three_rows (F : Type*) [Field F] [Fintype F] :
    let q := Fintype.card F
    ∃ rows : Fin (q^3) → List (Fin (q^3)), Function.Injective rows ∧
      (∀ i, (rows i).Nodup ∧ (rows i).length = q) ∧
      BridgeFree (Before rows) 3 ∧ (∑ i, (rows i).length) = q^4 ∧
      (∀ v, (occurrences (fun i => (rows i).toFinset) v).card = q) ∧ listOutputAverageCaps rows := by
  classical
  let q := Fintype.card F
  let encode : FieldTriple F ≃ Fin (q^3) := Fintype.equivFinOfCardEq (by simp [q,pow_succ,Nat.mul_assoc])
  let rows (i : Fin (q^3)) := (affineRow (encode.symm i)).map encode
  have undo (i : Fin (q^3)) : (rows i).map encode.symm = affineRow (encode.symm i) := by simp [rows,List.map_map]
  have simple (i : Fin (q^3)) : (rows i).Nodup := (affineRow_simple (encode.symm i)).map encode.injective
  have lengths (i : Fin (q^3)) : (rows i).length = q := by simp [rows,affineRow,q]
  have injective : Function.Injective rows := by
    intro i j eq
    have untagged := congrArg (List.map encode.symm) eq
    rw [undo i,undo j] at untagged
    exact encode.symm.injective (affineRows_injective untagged)
  have free : BridgeFree (Before rows) 3 := by
    intro d size
    refine ⟨fun b => ?_⟩
    let untitled : Bridge (Before (fun i => affineRow (encode.symm i))) d :=
      b.mapVertices encode.symm encode.symm.injective (fun i _ _ before => by
        simpa only [SourceAudit.BeforeIn,undo] using
          listBefore_map encode.symm (by rw [undo i]; exact affineRow_simple _) before)
    exact (affineRows_fullThree size).false (untitled.mapPaths encode.symm encode.symm.injective (fun _ _ _ step => step))
  have mass : (∑ i, (rows i).length) = q^4 := by simp [lengths,pow_succ]
  have contains (i v : Fin (q^3)) : v ∈ rows i ↔ encode.symm v ∈ affineRow (encode.symm i) := by
    rw [← undo i]
    constructor
    · exact List.mem_map_of_mem
    · intro on
      obtain ⟨x,hit,equal⟩ := List.mem_map.mp on
      exact (encode.symm.injective equal) ▸ hit
  have degree (v : Fin (q^3)) : (occurrences (fun i => (rows i).toFinset) v).card = q := by
    let through (a : F) := encode (lineThrough (encode.symm v) a)
    have unique : Function.Injective through := by
      intro a b equal
      exact congrArg Prod.fst (encode.injective equal)
    have same : occurrences (fun i => (rows i).toFinset) v = univ.image through := by
      ext i
      rw [mem_occurrences,List.mem_toFinset,contains,mem_image]
      constructor
      · intro on
        refine ⟨(encode.symm i).1,mem_univ _,?_⟩
        change encode (lineThrough (encode.symm v) (encode.symm i).1) = i
        rw [lineThrough_eq on,Equiv.apply_symm_apply]
      · rintro ⟨a,_,rfl⟩
        simpa only [through,Equiv.symm_apply_apply] using lineThrough_contains (encode.symm v) a
    rw [same,card_image_of_injective _ unique,card_univ]
  have qPos : (0:ℝ) < q := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have avg : ((q^4 : ℕ):ℝ)/Fintype.card (Fin (q^3)) = (q:ℝ) := by
    simp only [Fintype.card_fin,Nat.cast_pow]
    field_simp [qPos.ne']
  have caps : listOutputAverageCaps rows := by
    unfold listOutputAverageCaps
    dsimp only
    rw [mass,avg]
    simp only [lengths,degree]
    exact ⟨fun _ => ⟨by linarith,by linarith⟩,fun _ => ⟨by linarith,by linarith⟩⟩
  exact ⟨rows,injective,fun i => ⟨simple i,lengths i⟩,free,mass,degree,caps⟩

/-- If both budgets lie between `q³` and `B q³`, the finite-field witness
controls the mass of every half-three-free family by a factor `16 B²`.
The resulting literal witness has the four caps at its own averages and
full exclusion through size three. -/
theorem wenger_full_three_witness_controls_half (F : Type*) [Field F] [Fintype F]
    {n p k B : ℕ} (nFits : (Fintype.card F)^3 ≤ n) (pFits : (Fintype.card F)^3 ≤ p)
    (nBound : n ≤ B*(Fintype.card F)^3) (pBound : p ≤ B*(Fintype.card F)^3)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) :
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧
      BridgeFree (Before rows) 3 ∧ listOutputAverageCaps rows ∧
      (∑ i, (rows i).length) = (Fintype.card F)^4 ∧
      (∑ i, (paths i).length) ≤ 16*B^2*(∑ i, (rows i).length) := by
  let q := Fintype.card F
  have qPos : 0 < q := Fintype.card_pos
  have BPos : 0 < B := by
    by_contra! zero
    have qPower : 0 < q^3 := by positivity
    change n ≤ B*q^3 at nBound
    have b0 : B = 0 := by omega
    rw [b0,zero_mul] at nBound
    exact (not_le_of_gt qPower) (nFits.trans nBound)
  obtain ⟨rows,injective,lengths,free,mass,_,caps⟩ := wenger_full_three_rows F
  refine ⟨q^3,nFits,q^3,pFits,rows,injective,?_,free,caps,mass,?_⟩
  · intro i
    refine ⟨fun empty => ?_,(lengths i).1⟩
    have len := (lengths i).2
    rw [empty,List.length_nil] at len
    exact (Nat.ne_of_gt qPos) len.symm
  let M := ∑ i, (paths i).length
  rw [mass]
  rcases half_three_mass_cubic_or_linear paths simple half three with linear | cube
  · calc
      M ≤ 8*(n+p) := linear
      _ ≤ 8*(B*q^3+B*q^3) := Nat.mul_le_mul_left _ (Nat.add_le_add nBound pBound)
      _ = 16*(B*q^3) := by ring
      _ ≤ 16*(B^2*q^4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul
        (by simpa using Nat.pow_le_pow_right BPos (show 1 ≤ 2 by decide))
        (Nat.pow_le_pow_right qPos (by decide)))
      _ = _ := by ring
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (Nat.zero_le _)
  calc
    M^3 ≤ 1024*(n*p)^2 := cube
    _ ≤ 1024*((B*q^3)*(B*q^3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul nBound pBound) _)
    _ = (1024*B^4)*q^12 := by ring
    _ ≤ (16^3*B^6)*q^12 := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right BPos (by decide)))
    _ = _ := by ring

/-- At comparable positive budgets, a literal full-three-free witness
retains a fixed fraction of every nonzero half-three-free mass without
exceeding it. The four caps use the witness's own averages. -/
theorem comparable_budgets_full_three_witness_controls_half {n p k C : ℕ}
    (hn : 0 < n) (hp : 0 < p) (ratioPos : 0 < C) (np : n ≤ C*p) (pn : p ≤ C*n)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) (massPos : 0 < ∑ i, (paths i).length) :
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧
      BridgeFree (Before rows) 3 ∧ listOutputAverageCaps rows ∧
      (∑ i, (rows i).length) ≤ ∑ i, (paths i).length ∧
      (∑ i, (paths i).length) ≤ 16*(8*C)^2*(∑ i, (rows i).length) := by
  let b := min n p
  let M := ∑ i, (paths i).length
  let B := 8*C
  have BPos : 0 < B := by positivity
  have Bsquare : B ≤ B^2 := by simpa using Nat.pow_le_pow_right BPos (show 1 ≤ 2 by decide)
  have nScale : n ≤ C*b := by
    rcases le_total n p with a | b'
    · rw [show b = n from min_eq_left a]
      exact Nat.le_mul_of_pos_left _ ratioPos
    · simpa only [b,min_eq_right b'] using np
  have pScale : p ≤ C*b := by
    rcases le_total p n with a | b'
    · rw [show b = p from min_eq_right a]
      exact Nat.le_mul_of_pos_left _ ratioPos
    · simpa only [b,min_eq_left b'] using pn
  have factor : 16 ≤ 16*B^2 := by omega
  by_cases large : 8 ≤ b ∧ 16 ≤ M
  · let d := Nat.log 8 b
    let e := Nat.log 16 M
    let m := min d e
    let q := 2^m
    have mPos : 0 < m := lt_min (Nat.log_pos (by decide) large.1) (Nat.log_pos (by decide) large.2)
    have bPos : 0 < b := Nat.lt_of_lt_of_le (by decide) large.1
    have cubePower : q^3 = 8^m := by dsimp only [q]; rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    have fourthPower : q^4 = 16^m := by dsimp only [q]; rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    have fit : q^3 ≤ b := cubePower.trans_le ((Nat.pow_le_pow_right (by decide) (min_le_left d e)).trans
      (Nat.pow_log_le_self 8 bPos.ne'))
    have massFit : q^4 ≤ M := fourthPower.trans_le ((Nat.pow_le_pow_right (by decide) (min_le_right d e)).trans
      (Nat.pow_log_le_self 16 massPos.ne'))
    let : Fact (Nat.Prime 2) := ⟨by decide⟩
    let K := GaloisField 2 m
    let : Fintype K := Fintype.ofFinite K
    have card : Fintype.card K = q := (Nat.card_eq_fintype_card).symm.trans (GaloisField.card 2 m mPos.ne')
    have nFits : (Fintype.card K)^3 ≤ n := by rw [card]; exact fit.trans (min_le_left _ _)
    have pFits : (Fintype.card K)^3 ≤ p := by rw [card]; exact fit.trans (min_le_right _ _)
    rcases le_total d e with budgetLimits | massLimits
    · have full : b ≤ 8*q^3 := calc
        b ≤ 8^(d+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 8) b).le
        _ = _ := by rw [cubePower,show m = d from min_eq_left budgetLimits,pow_succ,Nat.mul_comm]
      have nBound : n ≤ B*(Fintype.card K)^3 := by
        rw [card]
        exact nScale.trans ((Nat.mul_le_mul_left C full).trans_eq (by dsimp [B]; ring))
      have pBound : p ≤ B*(Fintype.card K)^3 := by
        rw [card]
        exact pScale.trans ((Nat.mul_le_mul_left C full).trans_eq (by dsimp [B]; ring))
      obtain ⟨v,vFit,a,aFit,rows,injective,present,free,caps,exactMass,comparison⟩ :=
        wenger_full_three_witness_controls_half K nFits pFits nBound pBound paths simple half three
      exact ⟨v,vFit,a,aFit,rows,injective,present,free,caps,by rw [exactMass,card]; exact massFit,comparison⟩
    have enough : M ≤ 16*q^4 := calc
      M ≤ 16^(e+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 16) M).le
      _ = _ := by rw [fourthPower,show m = e from min_eq_right massLimits,pow_succ,Nat.mul_comm]
    obtain ⟨rows,injective,lengths,free,exactMass,_,caps⟩ := wenger_full_three_rows K
    refine ⟨(Fintype.card K)^3,nFits,(Fintype.card K)^3,pFits,rows,injective,?_,free,caps,?_,?_⟩
    · intro i
      refine ⟨fun empty => ?_,(lengths i).1⟩
      have len := (lengths i).2
      rw [empty,List.length_nil] at len
      exact (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card K)) len.symm
    · rw [exactMass,card]
      exact massFit
    · rw [exactMass,card]
      exact enough.trans (Nat.mul_le_mul_right _ factor)
  let v := min n M
  have vPos : 0 < v := lt_min hn massPos
  let rows : Fin 1 → List (Fin v) := fun _ => List.finRange v
  have nodup (i : Fin 1) : (rows i).Nodup := List.nodup_finRange _
  have present (i : Fin 1) : rows i ≠ [] := fun empty => by
    have length : (rows i).length = v := List.length_finRange
    rw [empty,List.length_nil] at length
    exact (Nat.ne_of_gt vPos) length.symm
  have free : BridgeFree (Before rows) 3 := fun _ _ => ⟨fun bridge => bridge.river_ne_arc 0 (Subsingleton.elim _ _)⟩
  have degree (x : Fin v) : (occurrences (fun i => (rows i).toFinset) x).card = 1 := by simp [occurrences,rows]
  have mass : (∑ i, (rows i).length) = v := by simp [rows]
  have caps : listOutputAverageCaps rows := by
    apply listOutputAverageCaps_of_widths rows nodup 1 (v:ℝ)
    · intro x
      norm_num [degree x]
    · intro i
      change (v:ℝ)/4 ≤ ((List.finRange v).length:ℝ) ∧ _
      rw [List.length_finRange]
      exact ⟨by linarith only [Nat.cast_nonneg (α := ℝ) v],le_rfl⟩
  refine ⟨v,min_le_left _ _,1,hp,rows,fun _ _ _ => Subsingleton.elim _ _,fun i => ⟨present i,nodup i⟩,free,caps,?_,?_⟩
  · rw [mass]
    exact min_le_right _ _
  rw [mass]
  by_cases room : 8 ≤ b
  · have smallMass : M ≤ 16 := Nat.le_of_lt (lt_of_not_ge (fun big => large ⟨room,big⟩))
    exact smallMass.trans (factor.trans (Nat.le_mul_of_pos_right _ vPos))
  have lengthBound (i : Fin p) : (paths i).length ≤ n := by
    rw [← List.toFinset_card_of_nodup (simple i)]
    simpa only [card_univ,Fintype.card_fin] using card_le_univ (paths i).toFinset
  have smallP : p ≤ B := pScale.trans (Nat.mul_le_mul_left C (show b ≤ 8 by omega)) |>.trans_eq (Nat.mul_comm _ _)
  have linearBound : M ≤ B*n := calc
    _ ≤ ∑ _i : Fin p, n := sum_le_sum fun i _ => lengthBound i
    _ = p*n := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ smallP
  have reduced : M ≤ B*v := by
    rcases le_total n M with first | next
    · simpa [v,min_eq_left first] using linearBound
    · rw [show v = M from min_eq_right next]
      exact Nat.le_mul_of_pos_left _ BPos
  exact reduced.trans (Nat.mul_le_mul_right _ (Bsquare.trans (Nat.le_mul_of_pos_left _ (by decide))))

end OnlineReachabilityPreservers
