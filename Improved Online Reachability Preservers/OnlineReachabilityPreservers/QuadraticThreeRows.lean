import Mathlib.FieldTheory.Finite.Basic
import OnlineReachabilityPreservers.HalfThreeUpstreamMass
import OnlineReachabilityPreservers.LocalAverageCleaning
import OnlineReachabilityPreservers.LocalFrozenCleaning
import OnlineReachabilityPreservers.DistinctPathBudgets

/-! Regular full-three-free families with unequal vertex and path counts. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private def IncidencePairUnique {I V : Type*} (hit : I → V → Prop) : Prop :=
  ∀ {a b x y}, x ≠ y → hit a x → hit a y → hit b x → hit b y → a = b

private def IncidenceNoTriangle {I V : Type*} (hit : I → V → Prop) : Prop :=
  ∀ {a b r x y z}, a ≠ b → r ≠ a → r ≠ b → x ≠ y → y ≠ z → x ≠ z →
    hit a x → hit a y → hit b y → hit b z → hit r x → hit r z → False

private theorem IncidencePairUnique.swap {I V : Type*} {hit : I → V → Prop}
    (unique : IncidencePairUnique hit) : IncidencePairUnique (fun v i => hit i v) := by
  intro a b x y apart ax ay bx by_
  by_contra different
  exact apart (unique different ax bx ay by_)

private theorem IncidenceNoTriangle.swap {I V : Type*} {hit : I → V → Prop}
    (noTriangle : IncidenceNoTriangle hit) : IncidenceNoTriangle (fun v i => hit i v) := by
  intro a b r x y z ab ra rb xy yz xz ax ay by_ bz rx rz
  exact noTriangle yz xy xz ab rb.symm ra.symm ay by_ bz rz ax rx

private theorem incidenceRowsFullThree {I V : Type*} [DecidableEq V] {hit : I → V → Prop}
    (pairUnique : IncidencePairUnique hit) (noTriangle : IncidenceNoTriangle hit)
    (rows : I → List V) (sound : ∀ i v, v ∈ rows i → hit i v) :
    BridgeFree (Before rows) 3 := by
  intro d size
  refine ⟨fun bridge => ?_⟩
  obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
  · exact bridge.river_ne_arc 0 (pairUnique (listBefore_ne bridge.riverStep)
      (sound _ _ bridge.riverStep.1) (sound _ _ bridge.riverStep.2.1)
      (sound _ _ (bridge.arcStep 0).1) (sound _ _ (bridge.arcStep 0).2.1))
  · exact noTriangle (bridge.distinctArcs.ne (by decide : (0:Fin 2) ≠ 1))
      (bridge.river_ne_arc 0) (bridge.river_ne_arc 1)
      (bridge.distinctVertices.ne (by decide : (0:Fin 3) ≠ 1))
      (bridge.distinctVertices.ne (by decide : (1:Fin 3) ≠ 2))
      (bridge.distinctVertices.ne (by decide : (0:Fin 3) ≠ 2))
      (sound _ _ (bridge.arcStep 0).1) (sound _ _ (bridge.arcStep 0).2.1)
      (sound _ _ (bridge.arcStep 1).1) (sound _ _ (bridge.arcStep 1).2.1)
      (sound _ _ bridge.riverStep.1) (sound _ _ bridge.riverStep.2.1)

private theorem incidenceRows {I V : Type*} [Fintype I] [Fintype V]
    (hit : I → V → Prop) [DecidableRel hit]
    (pairUnique : IncidencePairUnique hit) (noTriangle : IncidenceNoTriangle hit)
    {n p length degree : ℕ} (vCard : Fintype.card V = n) (iCard : Fintype.card I = p)
    (rowSize : ∀ i, (univ.filter (hit i)).card = length)
    (vertexSize : ∀ v, (univ.filter (fun i => hit i v)).card = degree)
    (long : 2 ≤ length) :
    ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
      (∀ i, (rows i).Nodup ∧ (rows i).length = length) ∧ BridgeFree (Before rows) 3 ∧
      (∑ i, (rows i).length) = p*length ∧
      (∀ v, (occurrences (fun i => (rows i).toFinset) v).card = degree) ∧
      listOutputAverageCaps rows := by
  classical
  let label := Fintype.equivFinOfCardEq iCard
  let vertex := Fintype.equivFinOfCardEq vCard
  let on (i : Fin p) := (univ.filter (hit (label.symm i))).map vertex.toEmbedding
  let rows (i : Fin p) := (on i).toList
  have contains (i v) : v ∈ rows i ↔ hit (label.symm i) (vertex.symm v) := by
    dsimp only [rows,on]
    simp only [Finset.mem_toList,Finset.mem_map,Finset.mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨x,hx,equal⟩
      change vertex x = v at equal
      simpa only [← equal,Equiv.symm_apply_apply] using hx
    · intro hv
      exact ⟨vertex.symm v,hv,vertex.apply_symm_apply v⟩
  have simple (i) : (rows i).Nodup := nodup_toList _
  have lengths (i) : (rows i).length = length := by simp [rows,on,rowSize]
  have injective : Function.Injective rows := by
    intro i j eq
    have enough : 2 ≤ (rows i).length := (lengths i).symm ▸ long
    let x := (rows i)[0]'(by omega)
    let y := (rows i)[1]'(by omega)
    have different : x ≠ y := fun h => by
      have := (simple i).getElem_inj_iff.mp h
      omega
    have xOn : x ∈ rows i := List.getElem_mem _
    have yOn : y ∈ rows i := List.getElem_mem _
    exact label.symm.injective (pairUnique (vertex.symm.injective.ne different)
      ((contains i x).mp xOn) ((contains i y).mp yOn)
      ((contains j x).mp (eq ▸ xOn)) ((contains j y).mp (eq ▸ yOn)))
  have free : BridgeFree (Before rows) 3 := by
    apply incidenceRowsFullThree (hit := fun i v => hit (label.symm i) (vertex.symm v))
    · intro a b x y apart ax ay bx by_
      exact label.symm.injective (pairUnique (vertex.symm.injective.ne apart) ax ay bx by_)
    · intro a b r x y z ab ra rb xy yz xz ax ay by_ bz rx rz
      exact noTriangle (label.symm.injective.ne ab) (label.symm.injective.ne ra) (label.symm.injective.ne rb)
        (vertex.symm.injective.ne xy) (vertex.symm.injective.ne yz) (vertex.symm.injective.ne xz)
        ax ay by_ bz rx rz
    · exact fun i v => (contains i v).mp
  have degrees (v) : (occurrences (fun i => (rows i).toFinset) v).card = degree := by
    have same : occurrences (fun i => (rows i).toFinset) v =
        ((univ : Finset I).filter (fun i => hit i (vertex.symm v))).map label.toEmbedding := by
      ext i
      rw [mem_occurrences,List.mem_toFinset,contains]
      simp only [Finset.mem_map,Finset.mem_filter,mem_univ,true_and]
      constructor
      · intro h
        exact ⟨label.symm i,h,label.apply_symm_apply i⟩
      · rintro ⟨j,h,equal⟩
        change label j = i at equal
        simpa only [← equal,Equiv.symm_apply_apply] using h
    rw [same,card_map,vertexSize]
  have caps : listOutputAverageCaps rows := by
    apply listOutputAverageCaps_of_widths rows simple degree length
    · intro v
      rw [degrees]
      exact ⟨div_le_self (by positivity) (by norm_num),le_rfl⟩
    · intro i
      rw [lengths]
      exact ⟨div_le_self (by positivity) (by norm_num),le_rfl⟩
  exact ⟨rows,injective,fun i => ⟨simple i,lengths i⟩,free,by simp [lengths],degrees,caps⟩

private abbrev QuadraticPoint (F : Type*) := F × F × F × F
private abbrev QuadraticLine (F : Type*) := (F × F) × F × F × F

variable {F : Type*} [Field F]

private def quadraticValue (ν : F) (s : F × F) : F := s.1^2+s.1*s.2-ν*s.2^2

private def quadraticHit (ν : F) (line : QuadraticLine F) (v : QuadraticPoint F) : Prop :=
  v.2.1 = line.2.1+line.1.1*v.1 ∧
  v.2.2.1 = line.2.2.1+line.1.2*v.1 ∧
  v.2.2.2 = line.2.2.2+quadraticValue ν line.1*v.1

private theorem quadraticHit_point_eq {ν : F} {line : QuadraticLine F} {x y : QuadraticPoint F}
    (hx : quadraticHit ν line x) (hy : quadraticHit ν line y) (same : x.1 = y.1) : x = y := by
  obtain ⟨ax,ay,az⟩ := hx
  obtain ⟨bx,by_,bz⟩ := hy
  rw [same] at ax ay az
  exact Prod.ext same (Prod.ext (ax.trans bx.symm) (Prod.ext (ay.trans by_.symm) (az.trans bz.symm)))

private theorem quadraticHit_line_eq {ν : F} {a b : QuadraticLine F} {x : QuadraticPoint F}
    (ax : quadraticHit ν a x) (bx : quadraticHit ν b x) (same : a.1 = b.1) : a = b := by
  obtain ⟨ax,ay,az⟩ := ax
  obtain ⟨bx,by_,bz⟩ := bx
  rw [same] at ax ay az
  exact Prod.ext same (Prod.ext (by linear_combination bx-ax)
    (Prod.ext (by linear_combination by_-ay) (by linear_combination bz-az)))

private theorem quadraticHit_difference {ν : F} {line : QuadraticLine F} {x y : QuadraticPoint F}
    (hx : quadraticHit ν line x) (hy : quadraticHit ν line y) :
    y.2.1-x.2.1 = (y.1-x.1)*line.1.1 ∧ y.2.2.1-x.2.2.1 = (y.1-x.1)*line.1.2 ∧
      y.2.2.2-x.2.2.2 = (y.1-x.1)*quadraticValue ν line.1 := by
  obtain ⟨ax,ay,az⟩ := hx
  obtain ⟨bx,by_,bz⟩ := hy
  exact ⟨by rw [ax,bx]; ring,by rw [ay,by_]; ring,by rw [az,bz]; ring⟩

private theorem quadraticHit_unique (ν : F) : IncidencePairUnique (quadraticHit ν) := by
  intro a b x y apart ax ay bx by_
  have step : y.1-x.1 ≠ 0 := sub_ne_zero.mpr (fun eq => apart (quadraticHit_point_eq ax ay eq.symm))
  obtain ⟨a₁,a₂,_⟩ := quadraticHit_difference ax ay
  obtain ⟨b₁,b₂,_⟩ := quadraticHit_difference bx by_
  have first : (y.1-x.1)*(a.1.1-b.1.1) = 0 := by linear_combination b₁-a₁
  have second : (y.1-x.1)*(a.1.2-b.1.2) = 0 := by linear_combination b₂-a₂
  exact quadraticHit_line_eq ax bx
    (Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp first).resolve_left step))
      (sub_eq_zero.mp ((mul_eq_zero.mp second).resolve_left step)))

private theorem quadraticValue_ne_zero {ν s t : F} (avoids : ∀ z : F, z^2+z ≠ ν)
    (apart : (s,t) ≠ 0) : s^2+s*t-ν*t^2 ≠ 0 := by
  intro zero
  have same := sub_eq_zero.mp zero
  by_cases t0 : t = 0
  · have s0 : s = 0 := by simpa [t0,pow_two] using same
    exact apart (Prod.ext s0 t0)
  · apply avoids (s/t)
    field_simp
    linear_combination same

private theorem quadraticHit_noTriangle {ν : F} (avoids : ∀ z : F, z^2+z ≠ ν) :
    IncidenceNoTriangle (quadraticHit ν) := by
  intro a b r x y z _ ra _ xy _ xz ax ay by_ bz rx rz
  let α := y.1-x.1
  let β := z.1-y.1
  let γ := x.1-z.1
  have total : α+β+γ = 0 := by dsimp [α,β,γ]; ring
  have αne : α ≠ 0 := sub_ne_zero.mpr (fun eq => xy (quadraticHit_point_eq ax ay eq.symm))
  have γne : γ ≠ 0 := sub_ne_zero.mpr (fun eq => xz (quadraticHit_point_eq rx rz eq))
  have last : α+β ≠ 0 := by intro eq; exact γne (by rw [eq,zero_add] at total; exact total)
  have different : a.1 ≠ r.1 := fun eq => ra (quadraticHit_line_eq ax rx eq).symm
  obtain ⟨ay₁,ay₂,ay₃⟩ := quadraticHit_difference ax ay
  obtain ⟨bz₁,bz₂,bz₃⟩ := quadraticHit_difference by_ bz
  obtain ⟨rx₁,rx₂,rx₃⟩ := quadraticHit_difference rz rx
  have first : α*a.1.1+β*b.1.1+γ*r.1.1 = 0 := by
    dsimp [α,β,γ]
    linear_combination -ay₁-bz₁-rx₁
  have second : α*a.1.2+β*b.1.2+γ*r.1.2 = 0 := by
    dsimp [α,β,γ]
    linear_combination -ay₂-bz₂-rx₂
  have value : α*quadraticValue ν a.1+β*quadraticValue ν b.1+γ*quadraticValue ν r.1 = 0 := by
    dsimp [α,β,γ]
    linear_combination -ay₃-bz₃-rx₃
  let a₁ := a.1.1-r.1.1
  let a₂ := a.1.2-r.1.2
  let b₁ := b.1.1-r.1.1
  let b₂ := b.1.2-r.1.2
  have summed₁ : α*a₁+β*b₁ = 0 := by dsimp [a₁,b₁]; linear_combination first-r.1.1*total
  have summed₂ : α*a₂+β*b₂ = 0 := by dsimp [a₂,b₂]; linear_combination second-r.1.2*total
  have centered : α*(a₁^2+a₁*a₂-ν*a₂^2)+β*(b₁^2+b₁*b₂-ν*b₂^2) = 0 := by
    dsimp [a₁,a₂,b₁,b₂,quadraticValue] at value ⊢
    linear_combination value-(2*r.1.1+r.1.2)*first-(r.1.1-2*ν*r.1.2)*second+
      (r.1.1^2+r.1.1*r.1.2-ν*r.1.2^2)*total
  have square₁ : β^2*b₁^2 = α^2*a₁^2 := by linear_combination (β*b₁-α*a₁)*summed₁
  have square₂ : β^2*b₂^2 = α^2*a₂^2 := by linear_combination (β*b₂-α*a₂)*summed₂
  have cross : β^2*b₁*b₂ = α^2*a₁*a₂ := by linear_combination β*b₂*summed₁-α*a₁*summed₂
  have zero : α*(α+β)*(a₁^2+a₁*a₂-ν*a₂^2) = 0 := by
    linear_combination β*centered-square₁-cross+ν*square₂
  have slopeNe : (a₁,a₂) ≠ 0 := by
    intro eq
    exact different (Prod.ext (sub_eq_zero.mp (congrArg Prod.fst eq)) (sub_eq_zero.mp (congrArg Prod.snd eq)))
  exact (mul_ne_zero (mul_ne_zero αne last) (quadraticValue_ne_zero avoids slopeNe)) zero

private def quadraticPointAt (ν : F) (line : QuadraticLine F) (x : F) : QuadraticPoint F :=
  (x,line.2.1+line.1.1*x,line.2.2.1+line.1.2*x,line.2.2.2+quadraticValue ν line.1*x)

private def quadraticLineAt (ν : F) (v : QuadraticPoint F) (s : F × F) : QuadraticLine F :=
  (s,v.2.1-s.1*v.1,v.2.2.1-s.2*v.1,v.2.2.2-quadraticValue ν s*v.1)

private theorem quadraticHit_card_points [Fintype F] (ν : F) (line : QuadraticLine F)
    [DecidablePred (quadraticHit ν line)] : (univ.filter (quadraticHit ν line)).card = Fintype.card F := by
  classical
  let point := quadraticPointAt ν line
  have hits (x : F) : quadraticHit ν line (point x) := ⟨rfl,rfl,rfl⟩
  have same : univ.filter (quadraticHit ν line) = univ.image point := by
    ext v
    simp only [mem_filter,mem_image,mem_univ,true_and]
    constructor
    · intro on
      exact ⟨v.1,quadraticHit_point_eq (hits v.1) on rfl⟩
    · rintro ⟨x,rfl⟩
      exact hits x
  rw [same,card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq),card_univ]

private theorem quadraticHit_card_lines [Fintype F] (ν : F) (v : QuadraticPoint F)
    [DecidablePred (fun line => quadraticHit ν line v)] :
    (univ.filter (fun line => quadraticHit ν line v)).card = (Fintype.card F)^2 := by
  classical
  let line := quadraticLineAt ν v
  have hits (s : F × F) : quadraticHit ν (line s) v := by
    simp [line,quadraticLineAt,quadraticHit]
  have same : univ.filter (fun line => quadraticHit ν line v) = univ.image line := by
    ext r
    simp only [mem_filter,mem_image,mem_univ,true_and]
    constructor
    · intro on
      exact ⟨r.1,quadraticHit_line_eq (hits r.1) on rfl⟩
    · rintro ⟨s,rfl⟩
      exact hits s
  rw [same,card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq),card_univ,Fintype.card_prod,pow_two]

private theorem exists_missing_quadratic_value [Finite F] : ∃ ν : F, ∀ z : F, z^2+z ≠ ν := by
  have notInjective : ¬Function.Injective (fun z : F => z^2+z) := by
    intro injective
    have values : (0:F)^2+0 = (-1)^2+(-1) := by ring
    exact neg_ne_zero.mpr (one_ne_zero : (1:F) ≠ 0) (injective values).symm
  have notSurjective : ¬Function.Surjective (fun z : F => z^2+z) := by
    rwa [← Finite.injective_iff_surjective]
  unfold Function.Surjective at notSurjective
  push Not at notSurjective
  exact notSurjective

/-- Over a finite field of order `q`, a quadratic family and
its transposed incidence relation give regular full-three-free paths at
budgets `(q⁴,q⁵)` and `(q⁵,q⁴)`. In each orientation the total mass is
the path count times the common path length. -/
theorem quadratic_full_three_rows (F : Type*) [Field F] [Fintype F]
    {n p length degree : ℕ}
    (shape : let q := Fintype.card F
      (n = q^4 ∧ p = q^5 ∧ length = q ∧ degree = q^2) ∨
      (n = q^5 ∧ p = q^4 ∧ length = q^2 ∧ degree = q)) :
    ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
      (∀ i, (rows i).Nodup ∧ (rows i).length = length) ∧ BridgeFree (Before rows) 3 ∧
      (∑ i, (rows i).length) = p*length ∧
      (∀ v, (occurrences (fun i => (rows i).toFinset) v).card = degree) ∧
      listOutputAverageCaps rows := by
  classical
  obtain ⟨ν,avoids⟩ := exists_missing_quadratic_value (F := F)
  have qLarge : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have pointCard : Fintype.card (QuadraticPoint F) = (Fintype.card F)^4 := by
    simp [QuadraticPoint,pow_succ,Nat.mul_assoc]
  have lineCard : Fintype.card (QuadraticLine F) = (Fintype.card F)^5 := by
    simp [QuadraticLine,pow_succ,Nat.mul_assoc]
  rcases shape with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩
  · exact incidenceRows (quadraticHit ν) (quadraticHit_unique ν) (quadraticHit_noTriangle avoids)
      pointCard lineCard (fun line => quadraticHit_card_points ν line) (fun v => quadraticHit_card_lines ν v) qLarge
  · exact incidenceRows (fun point line => quadraticHit ν line point)
      (IncidencePairUnique.swap (quadraticHit_unique ν))
      (IncidenceNoTriangle.swap (quadraticHit_noTriangle avoids)) lineCard pointCard
      (fun v => quadraticHit_card_lines ν v) (fun line => quadraticHit_card_points ν line) (by nlinarith)

/-- At either quadratic family budget, every half-three-free family has
at most four times the mass of the regular full witness. -/
theorem half_three_mass_le_four_on_quadratic_budgets {n p q cutoff : ℕ} (large : 5 ≤ q)
    (shape : (n = q^4 ∧ p = q^5) ∨ (n = q^5 ∧ p = q^4))
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) cutoff) (three : 3 ≤ cutoff) :
    (∑ i, (paths i).length) ≤ 4*q^6 := by
  have qPos : 0 < q := by omega
  have hn : 0 < n := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity
  have hp : 0 < p := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity
  have smaller : q^4 ≤ q^5 := Nat.pow_le_pow_right qPos (by decide)
  have bounds : n ≤ q^5 ∧ p ≤ q^5 := by
    rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨smaller,le_rfl⟩
    · exact ⟨le_rfl,smaller⟩
  have volume : n*p = q^9 := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> ring
  have charge : 4*n+p ≤ q^6 := calc
    _ ≤ 4*q^5+q^5 := Nat.add_le_add (Nat.mul_le_mul_left _ bounds.1) bounds.2
    _ = 5*q^5 := by ring
    _ ≤ q*q^5 := Nat.mul_le_mul_right _ large
    _ = _ := by ring
  let M := ∑ i, (paths i).length
  let S := M-M/4-(4*n+p)
  have cube : S^3 ≤ 6*(n*p)^2 :=
    half_three_latest_intersection_shifted_mass_cube_le hn hp paths simple half three 3
  by_contra! excess
  have floor : 4*(M/4) ≤ M := Nat.mul_div_le _ _
  have gap : 2*q^6 < S := by dsimp only [S]; omega
  have cap : S^3 ≤ (2*q^6)^3 := calc
    _ ≤ 6*(n*p)^2 := cube
    _ = 6*q^18 := by rw [volume]; ring
    _ ≤ 8*q^18 := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring
  exact (not_lt_of_ge cap) (pow_lt_pow_left₀ gap (Nat.zero_le _) (by decide : 3 ≠ 0))

/-- At the exact budgets of the quadratic family or its transpose, the
literal half-three maximum exists. The same-budget full-three witness
has mass between a quarter and all of the maximum and satisfies the
four starting-average caps. -/
theorem localOrderDistinctExtremal_frozen_full_three_at_quadratic_budgets (F : Type*)
    [Field F] [Fintype F] (large : 5 ≤ Fintype.card F) {n p : ℕ}
    (shape : let q := Fintype.card F; (n = q^4 ∧ p = q^5) ∨ (n = q^5 ∧ p = q^4)) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (∑ i, (rows i).length) = (Fintype.card F)^6 ∧
        (∑ i, (rows i).length) ≤ M ∧ M ≤ 4*(∑ i, (rows i).length) ∧
        frozenListCaps n p M rows := by
  let q := Fintype.card F
  have qPos : 0 < q := Fintype.card_pos
  have hn : 0 < n := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity
  have hp : 0 < p := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity
  obtain ⟨length,degree,sized⟩ : ∃ length degree : ℕ,
      (n = q^4 ∧ p = q^5 ∧ length = q ∧ degree = q^2) ∨
      (n = q^5 ∧ p = q^4 ∧ length = q^2 ∧ degree = q) := by
    rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨q,q^2,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
    · exact ⟨q^2,q,Or.inr ⟨rfl,rfl,rfl,rfl⟩⟩
  have positive : 0 < length := by rcases sized with ⟨_,_,rfl,_⟩ | ⟨_,_,rfl,_⟩ <;> positivity
  have balance : p*length = q^6 ∧ n*degree = q^6 := by
    rcases sized with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ <;> constructor <;> ring
  obtain ⟨rows,injective,lengths,free,mass,degrees,_⟩ := quadratic_full_three_rows F sized
  have present (i) : rows i ≠ [] ∧ (rows i).Nodup := by
    refine ⟨List.length_pos_iff.mp (by rw [(lengths i).2]; exact positive),(lengths i).1⟩
  obtain ⟨paths,distinct,valid,half,maximal,_,_⟩ := localOrderDistinctExtremal_isDense (k := 3) true hp
    ⟨rows,injective,present,free.halfFree⟩
  let M := ∑ i, (paths i).length
  have exactMass : (∑ i, (rows i).length) = q^6 := mass.trans balance.1
  have witnessLe : (∑ i, (rows i).length) ≤ M := maximal rows injective present free.halfFree
  have lower : q^6 ≤ M := exactMass.symm.trans_le witnessLe
  have upper : M ≤ 4*q^6 := half_three_mass_le_four_on_quadratic_budgets large shape paths
    (fun i => (valid i).2) half le_rfl
  have intervals {budget width : ℕ} (budgetPos : 0 < budget) (same : budget*width = q^6) :
      (M:ℝ)/(4*(budget:ℝ)) ≤ width ∧ (width:ℝ) ≤ 4*(M:ℝ)/budget := by
    have exactVolume : (budget:ℝ)*width = (q:ℝ)^6 := by exact_mod_cast same
    have pos : (0:ℝ) < budget := Nat.cast_pos.mpr budgetPos
    have lowerR : (q:ℝ)^6 ≤ M := by exact_mod_cast lower
    have upperR : (M:ℝ) ≤ 4*(q:ℝ)^6 := by exact_mod_cast upper
    refine ⟨(div_le_iff₀ (by positivity)).mpr ?_,(le_div_iff₀ pos).mpr ?_⟩
    · calc
        _ ≤ 4*((budget:ℝ)*width) := by rw [exactVolume]; exact upperR
        _ = _ := by ring
    · calc
        _ = (q:ℝ)^6 := by rw [mul_comm,exactVolume]
        _ ≤ _ := by linarith only [lowerR,show (0:ℝ) ≤ M by positivity]
  have caps : frozenListCaps n p M rows := by
    simp only [frozenListCaps,degrees,fun i => (lengths i).2]
    exact ⟨fun _ => intervals hn balance.2,fun _ => intervals hp balance.1⟩
  exact ⟨paths,distinct,valid,half,maximal,rows,injective,present,free,exactMass,witnessLe,
    by rw [exactMass]; exact upper,caps⟩

/-- Keeping any prescribed number of first-coordinate layers preserves
full-three exclusion and the incidence degrees on the remaining points.
The transposed family has the same total incidence mass. -/
theorem quadratic_full_three_rows_on_layers (F : Type*) [Field F] [Fintype F]
    {layers n p length degree : ℕ} (two : 2 ≤ layers) (fits : layers ≤ Fintype.card F)
    (shape : let q := Fintype.card F
      (n = layers*q^3 ∧ p = q^5 ∧ length = layers ∧ degree = q^2) ∨
      (n = q^5 ∧ p = layers*q^3 ∧ length = q^2 ∧ degree = layers)) :
    ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
      (∀ i, (rows i).Nodup ∧ (rows i).length = length) ∧ BridgeFree (Before rows) 3 ∧
      (∑ i, (rows i).length) = p*length ∧
      (∀ v, (occurrences (fun i => (rows i).toFinset) v).card = degree) ∧
      listOutputAverageCaps rows := by
  classical
  let q := Fintype.card F
  let Points := Fin layers × F × F × F
  let coordinate (i : Fin layers) := (Fintype.equivFin F).symm (Fin.castLE fits i)
  have coordinateInjective : Function.Injective coordinate :=
    (Fintype.equivFin F).symm.injective.comp (Fin.castLE_injective _)
  let project (v : Points) : QuadraticPoint F := (coordinate v.1,v.2)
  have projectInjective : Function.Injective project := fun _ _ same =>
    Prod.ext (coordinateInjective (congrArg Prod.fst same)) (congrArg (fun v : QuadraticPoint F => v.2) same)
  obtain ⟨ν,avoids⟩ := exists_missing_quadratic_value (F := F)
  let hit (line : QuadraticLine F) (v : Points) := quadraticHit ν line (project v)
  have pairUnique : IncidencePairUnique hit := by
    intro a b x y apart ax ay bx by_
    exact quadraticHit_unique ν (projectInjective.ne apart) ax ay bx by_
  have noTriangle : IncidenceNoTriangle hit := by
    intro a b r x y z ab ra rb xy yz xz ax ay by_ bz rx rz
    exact quadraticHit_noTriangle avoids ab ra rb (projectInjective.ne xy)
      (projectInjective.ne yz) (projectInjective.ne xz) ax ay by_ bz rx rz
  have rowSize (line) : (univ.filter (hit line)).card = layers := by
    let rowAt (i : Fin layers) : Points := (i,(quadraticPointAt ν line (coordinate i)).2)
    have hits (i : Fin layers) : hit line (rowAt i) := ⟨rfl,rfl,rfl⟩
    have same : univ.filter (hit line) = univ.image rowAt := by
      ext v
      simp only [mem_filter,mem_image,mem_univ,true_and]
      constructor
      · intro hv
        exact ⟨v.1,projectInjective (quadraticHit_point_eq (hits v.1) hv rfl)⟩
      · rintro ⟨i,rfl⟩
        exact hits i
    rw [same,card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq),card_univ,Fintype.card_fin]
  have vertexSize (v) : (univ.filter (fun i => hit i v)).card = q^2 :=
    quadraticHit_card_lines ν (project v)
  have pointCard : Fintype.card Points = layers*q^3 := by simp [Points,q,pow_succ,Nat.mul_assoc]
  have lineCard : Fintype.card (QuadraticLine F) = q^5 := by simp [QuadraticLine,q,pow_succ,Nat.mul_assoc]
  rcases shape with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩
  · exact incidenceRows hit pairUnique noTriangle pointCard lineCard rowSize vertexSize two
  · exact incidenceRows (fun v i => hit i v) (IncidencePairUnique.swap (hit := hit) pairUnique)
      (IncidenceNoTriangle.swap (hit := hit) noTriangle) lineCard pointCard vertexSize rowSize (by nlinarith [fits, two])

end OnlineReachabilityPreservers
