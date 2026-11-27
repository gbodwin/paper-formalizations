import OnlineReachabilityPreservers.IncidenceFullThree

/-! Regular full-three-free families with unequal vertex and path counts. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

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
  · exact fullThreeRows_of_finiteIncidence (quadraticHit ν) (quadraticHit_unique ν) (quadraticHit_noTriangle avoids)
      pointCard lineCard (fun line => quadraticHit_card_points ν line) (fun v => quadraticHit_card_lines ν v) qLarge
  · exact fullThreeRows_of_finiteIncidence (fun point line => quadraticHit ν line point)
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
  have scale : (n*p)^2 = (q^6)^3 := by rw [volume]; ring
  exact half_three_mass_le_four_of_volume hn hp charge scale.le paths simple half three

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
  have upper (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
      (half : HalfBridgeFree (Before paths) 3) : (∑ i, (paths i).length) ≤ 4*(p*length) := by
    rw [balance.1]
    exact half_three_mass_le_four_on_quadratic_budgets large shape paths simple half le_rfl
  obtain ⟨paths,distinct,valid,half,maximal,lower,retain,caps⟩ :=
    literal_half_maximum_frozen_full_three_of_regular_rows hn hp rows injective present free
      (fun i => (lengths i).2) degrees (balance.2.trans balance.1.symm) upper
  exact ⟨paths,distinct,valid,half,maximal,rows,injective,present,free,mass.trans balance.1,lower,retain,caps⟩

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
  · exact fullThreeRows_of_finiteIncidence hit pairUnique noTriangle pointCard lineCard rowSize vertexSize two
  · exact fullThreeRows_of_finiteIncidence (fun v i => hit i v) (IncidencePairUnique.swap (hit := hit) pairUnique)
      (IncidenceNoTriangle.swap (hit := hit) noTriangle) lineCard pointCard vertexSize rowSize (by nlinarith [fits, two])

end OnlineReachabilityPreservers
