import Mathlib.Algebra.QuadraticAlgebra.Basic
import OnlineReachabilityPreservers.IncidenceFullThree

/-! Regular full-three-free affine Hermitian incidence families. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private structure HermitianCoordinates (E : Type*) where
  x : E
  y : E
  z : E
  w : E

private def hermitianPair {E : Type*} [CommRing E] [StarRing E]
    (u v : HermitianCoordinates E) : E :=
  v.w+star u.w+star u.x*v.z+star u.z*v.x+star u.y*v.y

private def hermitianAffinePoint {E : Type*} [CommRing E] [StarRing E]
    (b c d s t x : E) : HermitianCoordinates E :=
  ⟨x,b+s*x,c+t*x,d+(-star c-star b*s)*x⟩

private theorem hermitianPair_affine {E : Type*} [CommRing E] [StarRing E]
    (b c d s t x y : E) :
    hermitianPair (hermitianAffinePoint b c d s t x) (hermitianAffinePoint b c d s t y) =
      d+star d+star b*b+star x*y*(t+star t+star s*s) := by
  simp only [hermitianPair,hermitianAffinePoint,star_add,star_sub,star_neg,star_mul,star_star]
  ring

private theorem hermitian_same_slope_of_orthogonal {E : Type*} [Field E] [StarRing E]
    {s t s' t' : E} (first : t+star t+star s*s = 0)
    (second : t'+star t'+star s'*s' = 0) (crossed : t'+star t+star s*s' = 0) :
    s = s' ∧ t = t' := by
  have conjugate := congrArg star crossed
  simp only [star_add,star_mul,star_star,star_zero] at conjugate
  have norm : star (s-s')*(s-s') = 0 := by
    rw [star_sub]
    linear_combination first+second-crossed-conjugate
  have sEq : s = s' := by
    rcases mul_eq_zero.mp norm with zero | zero
    · exact sub_eq_zero.mp (star_injective (show star (s-s') = star 0 by simpa using zero))
    · exact sub_eq_zero.mp zero
  refine ⟨sEq,?_⟩
  rw [sEq] at first crossed
  linear_combination first-crossed

private theorem hermitian_mixed_slope_eq {E : Type*} [Field E] [StarRing E]
    {x y z : HermitianCoordinates E} {s t s' t' : E}
    (xy : y.x ≠ x.x) (xz : z.x ≠ x.x)
    (hxx : hermitianPair x x = 0) (hyx : hermitianPair y x = 0)
    (hxz : hermitianPair x z = 0) (hyz : hermitianPair y z = 0)
    (ys : y.y-x.y = (y.x-x.x)*s) (yt : y.z-x.z = (y.x-x.x)*t)
    (zs : z.y-x.y = (z.x-x.x)*s') (zt : z.z-x.z = (z.x-x.x)*t') :
    t'+star t+star s*s' = 0 := by
  have crossed : star (y.x-x.x)*(z.z-x.z)+star (y.z-x.z)*(z.x-x.x)+
      star (y.y-x.y)*(z.y-x.y) = 0 := by
    simp only [hermitianPair] at hxx hyx hxz hyz
    simp only [star_sub]
    linear_combination hyz-hyx-hxz+hxx
  rw [ys,yt,zs,zt,star_mul,star_mul] at crossed
  have product : (star (y.x-x.x)*(z.x-x.x))*(t'+star t+star s*s') = 0 := by
    linear_combination crossed
  have left : star (y.x-x.x) ≠ 0 := by
    intro zero
    exact xy (sub_eq_zero.mp (star_injective (show star (y.x-x.x) = star 0 by simpa using zero)))
  exact (mul_eq_zero.mp product).resolve_left (mul_ne_zero left (sub_ne_zero.mpr xz))

private abbrev HermitianExtension (F : Type*) [Neg F] [One F] (ν : F) := QuadraticAlgebra F ν (-1)

private def withHermitianTrace {F : Type*} [Field F] {ν : F} (tr real : F) : HermitianExtension F ν :=
  ⟨real,2*real-tr⟩

private theorem withHermitianTrace_trace {F : Type*} [Field F] {ν : F} (tr real : F) :
    (withHermitianTrace (ν := ν) tr real).trace = tr := by
  rw [QuadraticAlgebra.trace_def]
  simp [withHermitianTrace]

private theorem withHermitianTrace_eq {F : Type*} [Field F] {ν : F} (z : HermitianExtension F ν) :
    withHermitianTrace z.trace z.re = z := by
  refine QuadraticAlgebra.ext rfl ?_
  simp [withHermitianTrace,QuadraticAlgebra.trace_def]

private theorem hermitian_trace_norm_eq_zero {F : Type*} [Field F] {ν : F}
    {d b : HermitianExtension F ν} : d+star d+star b*b = 0 ↔ d.trace = -b.norm := by
  rw [mul_comm (star b),← QuadraticAlgebra.algebraMap_norm_eq_mul_star,
    ← QuadraticAlgebra.algebraMap_trace_eq_add_star,← map_add]
  rw [← map_zero (algebraMap F (HermitianExtension F ν)),
    (algebraMap F (HermitianExtension F ν)).injective.eq_iff]
  exact add_eq_zero_iff_eq_neg

section FiniteFieldCoordinates

variable {F : Type*} [Field F] {ν : F}

private abbrev AffineHermitianPoint (F : Type*) [Field F] (ν : F) :=
  HermitianExtension F ν × HermitianExtension F ν × HermitianExtension F ν × F

private abbrev AffineHermitianLine (F : Type*) [Field F] (ν : F) :=
  HermitianExtension F ν × HermitianExtension F ν × HermitianExtension F ν × F × F

private def hermitianEncode (point : HermitianCoordinates (HermitianExtension F ν)) :
    AffineHermitianPoint F ν := (point.x,point.y,point.z,point.w.re)

private def hermitianDecode (point : AffineHermitianPoint F ν) :
    HermitianCoordinates (HermitianExtension F ν) :=
  ⟨point.1,point.2.1,point.2.2.1,
    withHermitianTrace (-((star point.1*point.2.2.1).trace+point.2.1.norm)) point.2.2.2⟩

private theorem hermitianPair_self_zero_iff {point : HermitianCoordinates (HermitianExtension F ν)} :
    hermitianPair point point = 0 ↔ point.w.trace = -((star point.x*point.z).trace+point.y.norm) := by
  let lift := algebraMap F (HermitianExtension F ν)
  have value : hermitianPair point point = lift (point.w.trace+((star point.x*point.z).trace+point.y.norm)) := by
    rw [map_add,map_add,QuadraticAlgebra.algebraMap_trace_eq_add_star,
      QuadraticAlgebra.algebraMap_trace_eq_add_star,QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    simp only [hermitianPair,star_mul,star_star]
    ring
  rw [value,← map_zero lift,lift.injective.eq_iff,add_eq_zero_iff_eq_neg]

private theorem hermitianDecode_isotropic (point : AffineHermitianPoint F ν) :
    hermitianPair (hermitianDecode point) (hermitianDecode point) = 0 :=
  hermitianPair_self_zero_iff.mpr (withHermitianTrace_trace _ _)

private theorem hermitianDecode_encode {point : HermitianCoordinates (HermitianExtension F ν)}
    (isotropic : hermitianPair point point = 0) : hermitianDecode (hermitianEncode point) = point := by
  have traceEq := hermitianPair_self_zero_iff.mp isotropic
  have wEq : withHermitianTrace (-((star point.x*point.z).trace+point.y.norm)) point.w.re = point.w :=
    traceEq ▸ withHermitianTrace_eq point.w
  cases point
  simp only [hermitianEncode,hermitianDecode]
  congr 1

private def hermitianSlopeZ (line : AffineHermitianLine F ν) : HermitianExtension F ν :=
  withHermitianTrace (-line.1.norm) line.2.2.2.1

private def hermitianBaseW (line : AffineHermitianLine F ν) : HermitianExtension F ν :=
  withHermitianTrace (-line.2.1.norm) line.2.2.2.2

private def hermitianLinePoint (line : AffineHermitianLine F ν) (x : HermitianExtension F ν) :
    HermitianCoordinates (HermitianExtension F ν) :=
  hermitianAffinePoint line.2.1 line.2.2.1 (hermitianBaseW line) line.1 (hermitianSlopeZ line) x

private theorem hermitianSlope_isotropic (line : AffineHermitianLine F ν) :
    hermitianSlopeZ line+star (hermitianSlopeZ line)+star line.1*line.1 = 0 :=
  hermitian_trace_norm_eq_zero.mpr (withHermitianTrace_trace _ _)

private theorem hermitianLinePair_zero (line : AffineHermitianLine F ν) (x y : HermitianExtension F ν) :
    hermitianPair (hermitianLinePoint line x) (hermitianLinePoint line y) = 0 := by
  have base : hermitianBaseW line+star (hermitianBaseW line)+star line.2.1*line.2.1 = 0 :=
    hermitian_trace_norm_eq_zero.mpr (withHermitianTrace_trace _ _)
  rw [hermitianLinePoint,hermitianLinePoint,hermitianPair_affine,base,hermitianSlope_isotropic,mul_zero,add_zero]

private def hermitianHit (line : AffineHermitianLine F ν) (point : AffineHermitianPoint F ν) : Prop :=
  point = hermitianEncode (hermitianLinePoint line point.1)

private theorem hermitianHit_at (line : AffineHermitianLine F ν) (x : HermitianExtension F ν) :
    hermitianHit line (hermitianEncode (hermitianLinePoint line x)) := rfl

private theorem hermitianHit_decode {line : AffineHermitianLine F ν} {point : AffineHermitianPoint F ν}
    (on : hermitianHit line point) : hermitianDecode point = hermitianLinePoint line point.1 :=
  (congrArg hermitianDecode on).trans (hermitianDecode_encode (hermitianLinePair_zero line _ _))

private theorem hermitianHit_pair_zero {line : AffineHermitianLine F ν} {x y : AffineHermitianPoint F ν}
    (hx : hermitianHit line x) (hy : hermitianHit line y) :
    hermitianPair (hermitianDecode x) (hermitianDecode y) = 0 := by
  rw [hermitianHit_decode hx,hermitianHit_decode hy]
  exact hermitianLinePair_zero _ _ _

private theorem hermitianHit_point_unique {line : AffineHermitianLine F ν} {x y : AffineHermitianPoint F ν}
    (hx : hermitianHit line x) (hy : hermitianHit line y) (same : x.1 = y.1) : x = y := by
  change x = hermitianEncode (hermitianLinePoint line x.1) at hx
  rw [same] at hx
  exact hx.trans hy.symm

private theorem hermitianHit_difference {line : AffineHermitianLine F ν} {x y : AffineHermitianPoint F ν}
    (hx : hermitianHit line x) (hy : hermitianHit line y) :
    y.2.1-x.2.1 = (y.1-x.1)*line.1 ∧
    y.2.2.1-x.2.2.1 = (y.1-x.1)*hermitianSlopeZ line := by
  have xY := congrArg HermitianCoordinates.y (hermitianHit_decode hx)
  have yY := congrArg HermitianCoordinates.y (hermitianHit_decode hy)
  have xZ := congrArg HermitianCoordinates.z (hermitianHit_decode hx)
  have yZ := congrArg HermitianCoordinates.z (hermitianHit_decode hy)
  dsimp [hermitianDecode,hermitianLinePoint,hermitianAffinePoint] at xY yY xZ yZ
  exact ⟨by rw [xY,yY]; ring,by rw [xZ,yZ]; ring⟩

private theorem hermitianHit_line_unique {a b : AffineHermitianLine F ν} {x : AffineHermitianPoint F ν}
    (ax : hermitianHit a x) (bx : hermitianHit b x) (slopeY : a.1 = b.1)
    (slopeZ : hermitianSlopeZ a = hermitianSlopeZ b) : a = b := by
  have coords := (hermitianHit_decode ax).symm.trans (hermitianHit_decode bx)
  have sameY := congrArg HermitianCoordinates.y coords
  have sameZ := congrArg HermitianCoordinates.z coords
  have sameW := congrArg HermitianCoordinates.w coords
  dsimp [hermitianLinePoint,hermitianAffinePoint] at sameY sameZ sameW
  rw [slopeY] at sameY
  rw [slopeZ] at sameZ
  have baseY : a.2.1 = b.2.1 := by linear_combination sameY
  have baseZ : a.2.2.1 = b.2.2.1 := by linear_combination sameZ
  rw [baseY,baseZ,slopeY] at sameW
  have baseW : hermitianBaseW a = hermitianBaseW b := by linear_combination sameW
  exact Prod.ext slopeY (Prod.ext baseY (Prod.ext baseZ
    (Prod.ext (congrArg QuadraticAlgebra.re slopeZ) (congrArg QuadraticAlgebra.re baseW))))

private theorem hermitianHit_unique [Fact (∀ r : F, r^2 ≠ ν+(-1)*r)] :
    ∀ {a b : AffineHermitianLine F ν} {x y : AffineHermitianPoint F ν},
    x ≠ y → hermitianHit a x → hermitianHit a y → hermitianHit b x → hermitianHit b y → a = b := by
  intro a b x y apart ax ay bx by_
  have step : y.1-x.1 ≠ 0 :=
    sub_ne_zero.mpr fun eq => apart (hermitianHit_point_unique ax ay eq.symm)
  obtain ⟨aY,aZ⟩ := hermitianHit_difference ax ay
  obtain ⟨bY,bZ⟩ := hermitianHit_difference bx by_
  have yProd : (y.1-x.1)*(a.1-b.1) = 0 := by linear_combination bY-aY
  have zProd : (y.1-x.1)*(hermitianSlopeZ a-hermitianSlopeZ b) = 0 := by linear_combination bZ-aZ
  exact hermitianHit_line_unique ax bx (sub_eq_zero.mp ((mul_eq_zero.mp yProd).resolve_left step))
    (sub_eq_zero.mp ((mul_eq_zero.mp zProd).resolve_left step))

private theorem hermitianHit_noTriangle [Fact (∀ r : F, r^2 ≠ ν+(-1)*r)] :
    ∀ {a b r : AffineHermitianLine F ν} {x y z : AffineHermitianPoint F ν},
      a ≠ b → r ≠ a → r ≠ b → x ≠ y → y ≠ z → x ≠ z →
      hermitianHit a x → hermitianHit a y → hermitianHit b y → hermitianHit b z →
      hermitianHit r x → hermitianHit r z → False := by
  intro a b r x y z _ ra _ xy _ xz ax ay by_ bz rx rz
  have dx : y.1 ≠ x.1 := fun eq => xy (hermitianHit_point_unique ax ay eq.symm)
  have dz : z.1 ≠ x.1 := fun eq => xz (hermitianHit_point_unique rx rz eq.symm)
  obtain ⟨aY,aZ⟩ := hermitianHit_difference ax ay
  obtain ⟨rY,rZ⟩ := hermitianHit_difference rx rz
  have mixed := hermitian_mixed_slope_eq dx dz (hermitianDecode_isotropic x)
    (hermitianHit_pair_zero ay ax) (hermitianHit_pair_zero rx rz) (hermitianHit_pair_zero by_ bz)
    aY aZ rY rZ
  obtain ⟨s,t⟩ := hermitian_same_slope_of_orthogonal
    (hermitianSlope_isotropic a) (hermitianSlope_isotropic r) mixed
  exact ra (hermitianHit_line_unique ax rx s t).symm

private def hermitianLineThrough (point : AffineHermitianPoint F ν)
    (slope : HermitianExtension F ν × F) : AffineHermitianLine F ν :=
  let t := withHermitianTrace (-slope.1.norm) slope.2
  let b := point.2.1-slope.1*point.1
  let c := point.2.2.1-t*point.1
  let d := (hermitianDecode point).w+(star c+star b*slope.1)*point.1
  (slope.1,b,c,slope.2,d.re)

private theorem hermitianLineThrough_hit (point : AffineHermitianPoint F ν)
    (slope : HermitianExtension F ν × F) : hermitianHit (hermitianLineThrough point slope) point := by
  let s := slope.1
  let t : HermitianExtension F ν := withHermitianTrace (-s.norm) slope.2
  let b := point.2.1-s*point.1
  let c := point.2.2.1-t*point.1
  let d := (hermitianDecode point).w+(star c+star b*s)*point.1
  have rebuilt : hermitianAffinePoint b c d s t point.1 = hermitianDecode point := by
    have yEq : b+s*point.1 = point.2.1 := by dsimp only [b]; ring
    have zEq : c+t*point.1 = point.2.2.1 := by dsimp only [c]; ring
    have wEq : d+(-star c-star b*s)*point.1 = (hermitianDecode point).w := by dsimp only [d]; ring
    unfold hermitianAffinePoint
    rw [yEq,zEq,wEq]
    rfl
  have slopeZero : t+star t+star s*s = 0 := hermitian_trace_norm_eq_zero.mpr (withHermitianTrace_trace _ _)
  have baseZero := hermitianDecode_isotropic point
  rw [← rebuilt,hermitianPair_affine,slopeZero,mul_zero,add_zero] at baseZero
  have sameTrace := hermitian_trace_norm_eq_zero.mp baseZero
  have baseW : withHermitianTrace (-b.norm) d.re = d := sameTrace ▸ withHermitianTrace_eq d
  change point = hermitianEncode (hermitianAffinePoint b c (withHermitianTrace (-b.norm) d.re) s t point.1)
  rw [baseW,rebuilt]
  rfl

private theorem hermitianHit_card_points [Fintype F] [Fintype (HermitianExtension F ν)]
    (line : AffineHermitianLine F ν) [DecidablePred (hermitianHit line)] :
    (univ.filter (hermitianHit line)).card = Fintype.card (HermitianExtension F ν) := by
  classical
  let point (x : HermitianExtension F ν) := hermitianEncode (hermitianLinePoint line x)
  have same : univ.filter (hermitianHit line) = univ.image point := by
    ext v
    simp only [mem_filter,mem_image,mem_univ,true_and]
    constructor
    · intro on
      exact ⟨v.1,on.symm⟩
    · rintro ⟨x,rfl⟩
      exact hermitianHit_at line x
  rw [same,card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq),card_univ]

private theorem hermitianHit_card_lines [Fintype F] [Fintype (HermitianExtension F ν)]
    (point : AffineHermitianPoint F ν) [DecidablePred (fun line => hermitianHit line point)] :
    (univ.filter (fun line => hermitianHit line point)).card = Fintype.card (HermitianExtension F ν)*Fintype.card F := by
  classical
  let line := hermitianLineThrough point
  have same : univ.filter (fun r => hermitianHit r point) = univ.image line := by
    ext r
    simp only [mem_filter,mem_image,mem_univ,true_and]
    constructor
    · intro on
      let slope := (r.1,r.2.2.2.1)
      exact ⟨slope,hermitianHit_line_unique (hermitianLineThrough_hit point slope) on rfl rfl⟩
    · rintro ⟨slope,rfl⟩
      exact hermitianLineThrough_hit point slope
  have distinct : Function.Injective line := by
    intro a b eq
    exact Prod.ext (congrArg (fun r : AffineHermitianLine F ν => r.1) eq)
      (congrArg (fun r : AffineHermitianLine F ν => r.2.2.2.1) eq)
  rw [same,card_image_of_injective _ distinct,card_univ,Fintype.card_prod]

end FiniteFieldCoordinates

/-- Over a finite field of order `q`, the affine Hermitian incidence
family and its transpose give regular full-three-free rows with
budget pairs `(q⁷,q⁸)` and `(q⁸,q⁷)`. -/
theorem hermitian_full_three_rows (F : Type*) [Field F] [Fintype F] {n p length degree : ℕ}
    (shape : let q := Fintype.card F
      (n = q^7 ∧ p = q^8 ∧ length = q^2 ∧ degree = q^3) ∨
      (n = q^8 ∧ p = q^7 ∧ length = q^3 ∧ degree = q^2)) :
    ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
      (∀ i, (rows i).Nodup ∧ (rows i).length = length) ∧ BridgeFree (Before rows) 3 ∧
      (∑ i, (rows i).length) = p*length ∧
      (∀ v, (occurrences (fun i => (rows i).toFinset) v).card = degree) ∧
      listOutputAverageCaps rows := by
  classical
  let q := Fintype.card F
  obtain ⟨ν,avoids⟩ := exists_missing_quadratic_value (F := F)
  let E := HermitianExtension F ν
  let : Fact (∀ r : F, r^2 ≠ ν+(-1)*r) := ⟨fun r eq => avoids r (by linear_combination eq)⟩
  let : Fintype E := Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd ν (-1)).symm
  have extensionCard : Fintype.card E = q^2 := by
    rw [Fintype.card_congr (QuadraticAlgebra.equivProd ν (-1)),Fintype.card_prod,pow_two]
  have pointCard : Fintype.card (AffineHermitianPoint F ν) = q^7 := by
    change Fintype.card (E × E × E × F) = _
    simp only [Fintype.card_prod,extensionCard]
    change q^2*(q^2*(q^2*q)) = q^7
    ring
  have lineCard : Fintype.card (AffineHermitianLine F ν) = q^8 := by
    change Fintype.card (E × E × E × F × F) = _
    simp only [Fintype.card_prod,extensionCard]
    change q^2*(q^2*(q^2*(q*q))) = q^8
    ring
  let hit := hermitianHit (F := F) (ν := ν)
  have pairUnique : IncidencePairUnique hit := hermitianHit_unique
  have noTriangle : IncidenceNoTriangle hit := hermitianHit_noTriangle
  have lineSize (line) : (univ.filter (hit line)).card = q^2 :=
    (hermitianHit_card_points line).trans extensionCard
  have pointSize (point) : (univ.filter (fun line => hit line point)).card = q^3 := calc
    _ = Fintype.card E*q := hermitianHit_card_lines point
    _ = _ := by rw [extensionCard]; ring
  have qLarge : 2 ≤ q := Fintype.one_lt_card
  have two : 2 ≤ q^2 := by nlinarith
  have three : 2 ≤ q^3 := by
    exact two.trans (Nat.pow_le_pow_right (by omega : 0 < q) (by decide))
  rcases shape with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩
  · exact fullThreeRows_of_finiteIncidence hit pairUnique noTriangle pointCard lineCard lineSize pointSize two
  · exact fullThreeRows_of_finiteIncidence (fun point line => hit line point)
      (IncidencePairUnique.swap (hit := hit) pairUnique)
      (IncidenceNoTriangle.swap (hit := hit) noTriangle) lineCard pointCard pointSize lineSize three

/-- The regular Hermitian witness has at least a quarter of the maximum
half-three mass at either of its exact budgets when `q ≥ 3`. -/
theorem half_three_mass_le_four_on_hermitian_budgets {n p q cutoff : ℕ} (large : 3 ≤ q)
    (shape : (n = q^7 ∧ p = q^8) ∨ (n = q^8 ∧ p = q^7))
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) cutoff) (three : 3 ≤ cutoff) :
    (∑ i, (paths i).length) ≤ 4*q^10 := by
  have qPos : 0 < q := by omega
  have hn : 0 < n := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity
  have hp : 0 < p := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity
  have smaller : q^7 ≤ q^8 := Nat.pow_le_pow_right qPos (by decide)
  have bounds : n ≤ q^8 ∧ p ≤ q^8 := by
    rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨smaller,le_rfl⟩
    · exact ⟨le_rfl,smaller⟩
  have charge : 4*n+p ≤ q^10 := calc
    _ ≤ 4*q^8+q^8 := Nat.add_le_add (Nat.mul_le_mul_left _ bounds.1) bounds.2
    _ = 5*q^8 := by ring
    _ ≤ q^2*q^8 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = _ := by ring
  have volume : (n*p)^2 = (q^10)^3 := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> ring
  exact half_three_mass_le_four_of_volume hn hp charge volume.le paths simple half three

/-- At the exact Hermitian budgets, a full-three witness has mass
`q¹⁰` between a quarter and all of the literal half maximum at cutoff
three and meets the four starting-average caps. -/
theorem localOrderDistinctExtremal_frozen_full_three_at_hermitian_budgets (F : Type*)
    [Field F] [Fintype F] (large : 3 ≤ Fintype.card F) {n p : ℕ}
    (shape : let q := Fintype.card F; (n = q^7 ∧ p = q^8) ∨ (n = q^8 ∧ p = q^7)) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (∑ i, (rows i).length) = (Fintype.card F)^10 ∧
        (∑ i, (rows i).length) ≤ M ∧ M ≤ 4*(∑ i, (rows i).length) ∧
        frozenListCaps n p M rows := by
  let q := Fintype.card F
  have qPos : 0 < q := Fintype.card_pos
  have hn : 0 < n := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity
  have hp : 0 < p := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity
  obtain ⟨length,degree,sized⟩ : ∃ length degree : ℕ,
      (n = q^7 ∧ p = q^8 ∧ length = q^2 ∧ degree = q^3) ∨
      (n = q^8 ∧ p = q^7 ∧ length = q^3 ∧ degree = q^2) := by
    rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨q^2,q^3,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
    · exact ⟨q^3,q^2,Or.inr ⟨rfl,rfl,rfl,rfl⟩⟩
  have positive : 0 < length := by rcases sized with ⟨_,_,rfl,_⟩ | ⟨_,_,rfl,_⟩ <;> positivity
  have balance : p*length = q^10 ∧ n*degree = p*length := by
    rcases sized with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ <;> constructor <;> ring
  obtain ⟨rows,injective,lengths,free,mass,degrees,_⟩ := hermitian_full_three_rows F sized
  have present (i) : rows i ≠ [] ∧ (rows i).Nodup :=
    ⟨List.length_pos_iff.mp (by rw [(lengths i).2]; exact positive),(lengths i).1⟩
  have upper (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
      (half : HalfBridgeFree (Before paths) 3) : (∑ i, (paths i).length) ≤ 4*(p*length) := by
    rw [balance.1]
    exact half_three_mass_le_four_on_hermitian_budgets large shape paths simple half le_rfl
  obtain ⟨paths,distinct,valid,half,maximal,lower,retain,caps⟩ :=
    literal_half_maximum_frozen_full_three_of_regular_rows hn hp rows injective present free
      (fun i => (lengths i).2) degrees balance.2 upper
  exact ⟨paths,distinct,valid,half,maximal,rows,injective,present,free,mass.trans balance.1,lower,retain,caps⟩

end OnlineReachabilityPreservers
