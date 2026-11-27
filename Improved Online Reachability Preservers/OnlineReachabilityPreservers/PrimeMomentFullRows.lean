import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Vandermonde
import OnlineReachabilityPreservers.LocalAverageCleaning

/-! Regular full-bridge-free rows through a prescribed cutoff. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private abbrev MomentVertex (q k : ℕ) := Fin q × (Fin (k-1) → ZMod q)
private abbrev MomentLine (q k : ℕ) := ZMod q × (Fin (k-1) → ZMod q)

private def primeMomentPoint {q k : ℕ} (line : MomentLine q k) (x : Fin q) : MomentVertex q k :=
  (x,fun slot => line.2 slot+line.1^(slot.val+1)*(x.val:ZMod q))

private def primeMomentRow {q k : ℕ} (line : MomentLine q k) : List (MomentVertex q k) :=
  List.ofFn (primeMomentPoint line)

private theorem primeMomentRow_simple {q k : ℕ} (line : MomentLine q k) : (primeMomentRow line).Nodup :=
  List.nodup_ofFn.mpr fun _ _ same => congrArg Prod.fst same

private theorem on_primeMomentRow {q k : ℕ} {line : MomentLine q k} {v : MomentVertex q k} :
    v ∈ primeMomentRow line ↔ primeMomentPoint line v.1 = v := by
  rw [primeMomentRow,List.mem_ofFn]
  constructor
  · rintro ⟨x,rfl⟩
    rfl
  · intro same
    exact ⟨v.1,same⟩

private theorem idxOf_ofFn_at {V : Type*} [DecidableEq V] {n : ℕ} {f : Fin n → V}
    (simple : (List.ofFn f).Nodup) (index : Fin n) {v : V} (on : f index = v) :
    (List.ofFn f).idxOf v = index.val := by
  have bound : index.val < (List.ofFn f).length := by simp
  have equal : (List.ofFn f).idxOf (f index) = index.val := by
    simpa only [List.getElem_ofFn] using simple.idxOf_getElem _ bound
  rwa [on] at equal

private theorem primeMomentRow_increases {q k : ℕ} [DecidableEq (MomentVertex q k)]
    {line : MomentLine q k} {u v : MomentVertex q k} (step : Before (primeMomentRow (q := q) (k := k)) line u v) :
    u.1.val < v.1.val := by
  have ordered := step.2.2
  unfold primeMomentRow at ordered
  rwa [idxOf_ofFn_at (primeMomentRow_simple line) u.1 (on_primeMomentRow.mp step.1),
    idxOf_ofFn_at (primeMomentRow_simple line) v.1 (on_primeMomentRow.mp step.2.1)] at ordered

private theorem primeMomentRow_at_slope {q k : ℕ} {a b : MomentLine q k} {v : MomentVertex q k}
    (onA : v ∈ primeMomentRow a) (onB : v ∈ primeMomentRow b) (same : a.1 = b.1) : a = b := by
  have joined := (on_primeMomentRow.mp onA).trans (on_primeMomentRow.mp onB).symm
  have coords := congrArg Prod.snd joined
  refine Prod.ext same (funext fun slot => ?_)
  have atSlot := congrFun coords slot
  dsimp only [primeMomentPoint] at atSlot
  rw [same] at atSlot
  exact add_right_cancel atSlot

private theorem primeMomentRow_difference {q k : ℕ} {line : MomentLine q k} {u v : MomentVertex q k}
    (onU : u ∈ primeMomentRow line) (onV : v ∈ primeMomentRow line) (j : Fin (k-1)) :
    v.2 j-u.2 j = ((v.1.val:ZMod q)-(u.1.val:ZMod q))*line.1^(j.val+1) := by
  have atU := congrFun (congrArg Prod.snd (on_primeMomentRow.mp onU)) j
  have atV := congrFun (congrArg Prod.snd (on_primeMomentRow.mp onV)) j
  dsimp only [primeMomentPoint] at atU atV
  linear_combination atU-atV

private theorem fin_sum_consecutive_sub {E : Type*} [AddCommGroup E] {d : ℕ}
    (f : Fin (d+2) → E) :
    (∑ i : Fin (d+1), (f i.succ-f i.castSucc)) = f (Fin.last (d+1))-f 0 := by
  rw [sum_sub_distrib]
  have first := Fin.sum_univ_succ f
  have last := Fin.sum_univ_castSucc f
  exact sub_eq_sub_iff_add_eq_add.mpr (by
    calc
      _ = f 0 + ∑ i : Fin (d+1), f i.succ := add_comm _ _
      _ = ∑ j, f j := first.symm
      _ = (∑ i : Fin (d+1), f i.castSucc) + f (Fin.last (d+1)) := last
      _ = _ := add_comm _ _)

private theorem primeMomentVandermonde_coefficients {q k d : ℕ} [Fact (Nat.Prime q)]
    (fits : d+2 ≤ k) (labels shifts : Fin (d+2) → ZMod q)
    (moment : ∀ j < k, (∑ i, shifts i*(labels i)^j) = 0) (value : ZMod q)
    (present : value ∈ Finset.univ.image labels) :
    (∑ i, if labels i = value then shifts i else 0) = 0 := by
  classical
  let support := univ.image labels
  let coefficient (v : ZMod q) := ∑ i, if labels i = v then shifts i else 0
  have rearranged (j : ℕ) (jFit : j < k) : (∑ v ∈ support, coefficient v*v^j) = 0 := calc
    _ = ∑ i, ∑ v ∈ support, (if labels i = v then shifts i else 0)*v^j := by
      simp only [coefficient,sum_mul]
      rw [sum_comm]
    _ = ∑ i, shifts i*(labels i)^j := by
      apply sum_congr rfl
      intro i _
      rw [sum_eq_single_of_mem (labels i) (mem_image.mpr ⟨i,mem_univ _,rfl⟩)]
      · simp
      · intro v _ unequal
        simp [unequal.symm]
    _ = 0 := moment j jFit
  let S := {v : ZMod q // v ∈ support}
  let enumeration := (Fintype.equivFin S).symm
  let slopes (i : Fin (Fintype.card S)) := (enumeration i).val
  have injective : Function.Injective slopes := Subtype.val_injective.comp enumeration.injective
  have few : Fintype.card S ≤ k := by
    rw [Fintype.card_coe]
    exact (card_image_le.trans (by simp)).trans fits
  have all (j : Fin (Fintype.card S)) : (∑ i, coefficient (slopes i)*(slopes i)^(j:ℕ)) = 0 := calc
    _ = ∑ v : S, coefficient v.val*v.val^(j:ℕ) :=
      Equiv.sum_comp enumeration (fun v => coefficient v.val*v.val^(j:ℕ))
    _ = ∑ v ∈ support, coefficient v*v^(j:ℕ) := Finset.sum_coe_sort support (fun v => coefficient v*v^(j:ℕ))
    _ = 0 := rearranged _ (j.isLt.trans_le few)
  have zero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero injective all
  have selected := congrFun zero ((Fintype.equivFin S) ⟨value,present⟩)
  change coefficient (slopes ((Fintype.equivFin S) ⟨value,present⟩)) = 0 at selected
  simpa only [slopes,enumeration,Equiv.symm_apply_apply,coefficient] using selected

private theorem primeMomentRows_full {q k cutoff : ℕ} [Fact (Nat.Prime q)] (enough : min cutoff q ≤ k) :
    BridgeFree (Before (primeMomentRow (q := q) (k := k))) cutoff := by
  classical
  intro d size
  refine ⟨fun bridge => ?_⟩
  let x (j : Fin (d+2)) : ℕ := (bridge.vertex j).1.val
  let xField (j : Fin (d+2)) : ZMod q := x j
  let labels : Fin (d+2) → ZMod q := Fin.cases bridge.river.1 (fun i => (bridge.arc i).1)
  let shifts : Fin (d+2) → ZMod q :=
    Fin.cases (xField 0-xField (Fin.last (d+1))) (fun i => xField i.succ-xField i.castSucc)
  have ordered (i : Fin (d+1)) : x i.castSucc < x i.succ := primeMomentRow_increases (bridge.arcStep i)
  have strictly : StrictMono (fun j => (bridge.vertex j).1) :=
    Fin.strictMono_iff_lt_succ.mpr ordered
  have layerBound : d+2 ≤ q := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ strictly.injective
  have sizeBound : d+2 ≤ k := (le_min size layerBound).trans enough
  have ends : x 0 ≤ x (Fin.last (d+1)) := (primeMomentRow_increases bridge.riverStep).le
  have moments (j : ℕ) (jFit : j < k) : (∑ i, shifts i*(labels i)^j) = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [labels,shifts,Fin.cases_zero,Fin.cases_succ]
    by_cases zero : j = 0
    · subst j
      simp only [pow_zero,mul_one]
      rw [fin_sum_consecutive_sub xField]
      ring
    · let slot : Fin (k-1) := ⟨j-1,by omega⟩
      let coord (i : Fin (d+2)) := (bridge.vertex i).2 slot
      have exponent : slot.val+1 = j := by dsimp only [slot]; omega
      have river : coord (Fin.last (d+1))-coord 0 =
          (xField (Fin.last (d+1))-xField 0)*bridge.river.1^j := by
        have step := primeMomentRow_difference bridge.riverStep.1 bridge.riverStep.2.1 slot
        rw [exponent] at step
        exact step
      have arc (i : Fin (d+1)) : coord i.succ-coord i.castSucc =
          (xField i.succ-xField i.castSucc)*(bridge.arc i).1^j := by
        have step := primeMomentRow_difference (bridge.arcStep i).1 (bridge.arcStep i).2.1 slot
        rw [exponent] at step
        exact step
      have backward : (xField 0-xField (Fin.last (d+1)))*bridge.river.1^j =
          coord 0-coord (Fin.last (d+1)) := by linear_combination river
      rw [backward]
      simp_rw [← arc]
      rw [fin_sum_consecutive_sub coord]
      ring
  let slope := (bridge.arc 0).1
  have riverSlope : bridge.river.1 ≠ slope := fun same =>
    bridge.river_ne_arc 0 (primeMomentRow_at_slope bridge.riverStep.1 (bridge.arcStep 0).1 same)
  have occurs : slope ∈ univ.image labels := by
    refine mem_image.mpr ⟨(0:Fin (d+1)).succ,mem_univ _,?_⟩
    exact Fin.cases_succ _
  have forced := primeMomentVandermonde_coefficients sizeBound labels shifts moments slope occurs
  have riverOut : ¬ labels 0 = slope := by
    change Fin.cases bridge.river.1 (fun i => (bridge.arc i).1) 0 ≠ slope
    rwa [Fin.cases_zero]
  rw [Fin.sum_univ_succ,ite_eq_right riverOut,zero_add] at forced
  have labelOfArc (i : Fin (d+1)) : labels i.succ = (bridge.arc i).1 := Fin.cases_succ _
  have shiftOfArc (i : Fin (d+1)) : shifts i.succ = xField i.succ-xField i.castSucc := Fin.cases_succ _
  let increment (i : Fin (d+1)) := x i.succ-x i.castSucc
  have total : (∑ i, increment i) = x (Fin.last (d+1))-x 0 := by
    apply Int.ofNat_inj.mp
    calc
      _ = ∑ i : Fin (d+1), ((x i.succ:ℤ)-(x i.castSucc:ℤ)) := by
        rw [Nat.cast_sum]
        exact sum_congr rfl (fun i _ => Nat.cast_sub (ordered i).le)
      _ = (x (Fin.last (d+1)):ℤ)-(x 0:ℤ) :=
        fin_sum_consecutive_sub (fun j => (x j:ℤ))
      _ = _ := (Nat.cast_sub ends).symm
  let count := ∑ i : Fin (d+1), if (bridge.arc i).1 = slope then increment i else 0
  have positive : 0 < count := by
    have bound : (if (bridge.arc 0).1 = slope then increment 0 else 0) ≤ count := single_le_sum
      (f := fun i : Fin (d+1) => if (bridge.arc i).1 = slope then increment i else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ (0:Fin (d+1)))
    rw [ite_eq_left (rfl : (bridge.arc 0).1 = slope)] at bound
    exact (Nat.sub_pos_of_lt (ordered 0)).trans_le bound
  have smaller : count < q := calc
    _ ≤ ∑ i, increment i := sum_le_sum (fun i _ => by split <;> simp)
    _ = x (Fin.last (d+1))-x 0 := total
    _ ≤ x (Fin.last (d+1)) := Nat.sub_le _ _
    _ < q := (bridge.vertex (Fin.last (d+1))).1.isLt
  have castZero : (count:ZMod q) = 0 := by
    dsimp only [count]
    rw [Nat.cast_sum]
    refine (sum_congr rfl (fun i _ => ?_)).trans forced
    by_cases same : (bridge.arc i).1 = slope
    · rw [ite_eq_left same,ite_eq_left ((labelOfArc i).trans same),shiftOfArc]
      exact Nat.cast_sub (ordered i).le
    · have absent : labels i.succ ≠ slope := fun h => same ((labelOfArc i).symm.trans h)
      rw [ite_eq_right same,ite_eq_right absent,Nat.cast_zero]
  exact (not_le_of_gt smaller) (Nat.le_of_dvd positive ((ZMod.natCast_eq_zero_iff count q).mp castZero))

private theorem primeMomentRow_injective {q k : ℕ} [Fact (Nat.Prime q)] (two : 2 ≤ k) :
    Function.Injective (primeMomentRow (q := q) (k := k)) := by
  intro a b equal
  have prime : Nat.Prime q := Fact.out
  let u := primeMomentPoint a ⟨0,prime.pos⟩
  let v := primeMomentPoint a ⟨1,prime.one_lt⟩
  let slot : Fin (k-1) := ⟨0,by omega⟩
  have uOn : u ∈ primeMomentRow a := on_primeMomentRow.mpr rfl
  have vOn : v ∈ primeMomentRow a := on_primeMomentRow.mpr rfl
  have slopeOf {line} (onU : u ∈ primeMomentRow line) (onV : v ∈ primeMomentRow line) :
      v.2 slot-u.2 slot = line.1 := by
    have compare := primeMomentRow_difference onU onV slot
    change v.2 slot-u.2 slot = (((1:ℕ):ZMod q)-((0:ℕ):ZMod q))*line.1^1 at compare
    simpa only [Nat.cast_one,Nat.cast_zero,sub_zero,pow_one,one_mul] using compare
  have otherU : u ∈ primeMomentRow b := equal ▸ uOn
  have otherV : v ∈ primeMomentRow b := equal ▸ vOn
  exact primeMomentRow_at_slope uOn otherU ((slopeOf uOn vOn).symm.trans (slopeOf otherU otherV))

private def primeMomentLineThrough {q k : ℕ} (v : MomentVertex q k) (slope : ZMod q) : MomentLine q k :=
  (slope,fun j => v.2 j-slope^(j.val+1)*(v.1.val:ZMod q))

private theorem primeMomentLineThrough_on {q k : ℕ} (v : MomentVertex q k) (slope : ZMod q) :
    v ∈ primeMomentRow (primeMomentLineThrough v slope) := by
  apply on_primeMomentRow.mpr
  exact Prod.ext rfl (funext fun j => sub_add_cancel _ _)

/-- Over the field of prime order `q`, use the first `k-1` moments of
the slope and order every row by the natural first coordinate. For
any `k ≥ 2` this gives `q^k` distinct nonempty simple rows on `q^k`
vertices, all degrees and lengths `q`, mass `q^(k+1)`, and full
exclusion through size `k`. When `q ≤ k`, it excludes every full bridge. -/
theorem prime_moment_full_rows (q k : ℕ) [Fact (Nat.Prime q)] (two : 2 ≤ k) :
    ∃ rows : Fin (q^k) → List (Fin (q^k)), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup ∧ (rows i).length = q) ∧
      (∀ cutoff, min cutoff q ≤ k → BridgeFree (Before rows) cutoff) ∧
      (∑ i, (rows i).length) = q^(k+1) ∧
      (∀ v, (occurrences (fun i => (rows i).toFinset) v).card = q) ∧ listOutputAverageCaps rows := by
  classical
  have prime : Nat.Prime q := Fact.out
  let : NeZero q := ⟨prime.ne_zero⟩
  have cardCoordinates : Fintype.card (Fin (k-1) → ZMod q) = q^(k-1) := by
    rw [Fintype.card_fun,ZMod.card,Fintype.card_fin]
  have volume : q*q^(k-1) = q^k := by rw [← pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have vertexCard : Fintype.card (MomentVertex q k) = q^k := by
    change Fintype.card (Fin q × (Fin (k-1) → ZMod q)) = q^k
    rw [Fintype.card_prod,Fintype.card_fin,cardCoordinates,volume]
  have lineCard : Fintype.card (MomentLine q k) = q^k := by
    change Fintype.card (ZMod q × (Fin (k-1) → ZMod q)) = q^k
    rw [Fintype.card_prod,ZMod.card,cardCoordinates,volume]
  let vertex := Fintype.equivFinOfCardEq vertexCard
  let line := Fintype.equivFinOfCardEq lineCard
  let rows (i : Fin (q^k)) := (primeMomentRow (line.symm i)).map vertex
  have decode (i) : (rows i).map vertex.symm = primeMomentRow (line.symm i) := by simp [rows,List.map_map]
  have simple (i) : (rows i).Nodup := (primeMomentRow_simple (line.symm i)).map vertex.injective
  have lengths (i) : (rows i).length = q := by simp [rows,primeMomentRow]
  have injective : Function.Injective rows :=
    (List.map_injective_iff.mpr vertex.injective).comp ((primeMomentRow_injective two).comp line.symm.injective)
  have free (cutoff : ℕ) (enough : min cutoff q ≤ k) : BridgeFree (Before rows) cutoff := by
    intro d size
    refine ⟨fun bridge => ?_⟩
    let moved : Bridge (Before (fun i => primeMomentRow (line.symm i))) d :=
      bridge.mapVertices vertex.symm vertex.symm.injective (fun i _ _ step => by
        simpa only [SourceAudit.BeforeIn,decode] using listBefore_map vertex.symm
          ((decode i).symm ▸ primeMomentRow_simple (line.symm i)) step)
    exact (primeMomentRows_full enough size).false (moved.mapPaths line.symm line.symm.injective (fun _ _ _ step => step))
  have contains (i v) : v ∈ rows i ↔ vertex.symm v ∈ primeMomentRow (line.symm i) := by
    rw [← decode i]
    constructor
    · exact List.mem_map_of_mem
    · intro on
      obtain ⟨u,hit,equal⟩ := List.mem_map.mp on
      exact (vertex.symm.injective equal) ▸ hit
  have degrees (v : Fin (q^k)) : (occurrences (fun i => (rows i).toFinset) v).card = q := by
    let through (slope : ZMod q) := line (primeMomentLineThrough (vertex.symm v) slope)
    have unique : Function.Injective through := fun _ _ equal => congrArg Prod.fst (line.injective equal)
    have exactLines : occurrences (fun i => (rows i).toFinset) v = univ.image through := by
      ext i
      rw [mem_occurrences,List.mem_toFinset,contains,mem_image]
      constructor
      · intro on
        let slope := (line.symm i).1
        refine ⟨slope,mem_univ _,?_⟩
        have same : primeMomentLineThrough (vertex.symm v) slope = line.symm i :=
          primeMomentRow_at_slope (primeMomentLineThrough_on _ _) on rfl
        rw [show through slope = line (primeMomentLineThrough (vertex.symm v) slope) from rfl,same,Equiv.apply_symm_apply]
      · rintro ⟨slope,_,rfl⟩
        simpa only [through,Equiv.symm_apply_apply] using primeMomentLineThrough_on (vertex.symm v) slope
    rw [exactLines,card_image_of_injective _ unique,card_univ,ZMod.card]
  have caps : listOutputAverageCaps rows := by
    apply listOutputAverageCaps_of_widths rows simple q q
    · intro v
      rw [degrees]
      exact ⟨div_le_self (by positivity) (by norm_num),le_rfl⟩
    · intro i
      rw [lengths]
      exact ⟨div_le_self (by positivity) (by norm_num),le_rfl⟩
  exact ⟨rows,injective,fun i => ⟨List.length_pos_iff.mp (by rw [lengths]; exact prime.pos),simple i,lengths i⟩,
    free,by simp [lengths,pow_succ],degrees,caps⟩

end OnlineReachabilityPreservers
