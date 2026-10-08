import LinearDistancePreservers.ModularObstacle
import LinearDistancePreservers.ObstacleWeights

/-! The metric hypotheses of the weighted obstacle product are discharged
for the repaired modular construction. Outer routes use quadratic integer
weights; sufficiently large integer separation protects them from savings
inside the gadgets. -/
namespace LinearDistancePreservers.ModularObstacle
open SimpleGraph ObstacleProduct
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {n k x σ : ℕ} [NeZero n] [NeZero σ]

noncomputable def portSlope (p : ZMod n × Fin x) : ℕ :=
  (Fintype.equivFin (ZMod n × Fin x) p).val

theorem portSlope_lt (p : ZMod n × Fin x) : portSlope p < n*x := by
  simpa [portSlope] using (Fintype.equivFin (ZMod n × Fin x) p).isLt

theorem portSlope_injective : Function.Injective (portSlope (n := n) (x := x)) := by
  intro p q h
  exact (Fintype.equivFin (ZMod n × Fin x)).injective (Fin.ext h)

theorem portCode_val (hsize : n*x ≤ σ) (p : ZMod n × Fin x) :
    (portCode σ p).val = portSlope p :=
  ZMod.val_natCast_of_lt ((portSlope_lt p).trans_le hsize)

noncomputable def leftWeight (n x : ℕ) (a b : ZMod σ) : ℕ :=
  2*(n*x)^2+1+(b-a).val^2

noncomputable def rightWeight (n x : ℕ) (b c : ZMod σ) : ℕ :=
  2*(n*x)^2+1+(c-b).val^2

theorem leftWeight_port (hx : x ≤ n) (hsize : n*x ≤ σ) (b : ZMod σ) (j : ZMod n × Fin x) :
    leftWeight n x ((data (k := k) hx hsize).left b j) b =
      2*(n*x)^2+1+(portSlope j)^2 := by
  simp [leftWeight,data,portCode_val hsize]

theorem rightWeight_port (hx : x ≤ n) (hsize : n*x ≤ σ) (b : ZMod σ) (j : ZMod n × Fin x) :
    rightWeight n x b ((data (k := k) hx hsize).right b j) =
      2*(n*x)^2+1+(portSlope j)^2 := by
  simp [rightWeight,data,portCode_val hsize]

/-- No wraparound in a competing two-edge outer route. -/
theorem two_port_sum (houter : 3*(n*x) ≤ σ)
    {b b' : ZMod σ} {j j₁ j₂ : ZMod n × Fin x}
    (hl : b' - portCode σ j₁ = b - portCode σ j)
    (hr : b' + portCode σ j₂ = b + portCode σ j) :
    portSlope j₁ + portSlope j₂ = 2*portSlope j := by
  have hm : ((portSlope j₁ + portSlope j₂ : ℕ) : ZMod σ) =
      ((2*portSlope j : ℕ) : ZMod σ) := by
    dsimp [portCode] at hl hr
    change b' - (portSlope j₁ : ZMod σ) = b - (portSlope j : ZMod σ) at hl
    change b' + (portSlope j₂ : ZMod σ) = b + (portSlope j : ZMod σ) at hr
    push_cast
    linear_combination hr - hl
  have h1 := portSlope_lt j₁
  have h2 := portSlope_lt j₂
  have hj := portSlope_lt j
  simpa only [ZMod.val_natCast_of_lt (show portSlope j₁ + portSlope j₂ < σ by omega),
    ZMod.val_natCast_of_lt (show 2*portSlope j < σ by omega)] using congrArg ZMod.val hm

theorem outer_optimal (hx : x ≤ n) (hsize : n*x ≤ σ) (houter : 3*(n*x) ≤ σ) :
    OuterOptimal (data (k := k) hx hsize) (leftWeight n x) (rightWeight n x) := by
  intro b j b' j₁ j₂ hl hr
  have hsum := two_port_sum houter hl hr
  simp only [leftWeight_port,rightWeight_port]
  have hsq : 2*(portSlope j)^2 ≤ (portSlope j₁)^2 + (portSlope j₂)^2 := by
    nlinarith [sq_nonneg ((portSlope j₁ : ℤ) - portSlope j₂)]
  refine ⟨by omega,?_⟩
  intro he
  have hj₁ : portSlope j₁ = portSlope j := by nlinarith
  have hj₂ : portSlope j₂ = portSlope j := by omega
  have h1 := portSlope_injective hj₁
  have h2 := portSlope_injective hj₂
  subst j₁ j₂
  exact ⟨sub_left_inj.mp hl,rfl,rfl⟩

theorem outer_small (hx : x ≤ n) (hsize : n*x ≤ σ)
    (b : ZMod σ) (j : ZMod n × Fin x) :
    leftWeight n x ((data (k := k) hx hsize).left b j) b +
      rightWeight n x b ((data (k := k) hx hsize).right b j) < 3*(2*(n*x)^2+1) := by
  rw [leftWeight_port,rightWeight_port]
  have h := portSlope_lt j
  nlinarith

noncomputable def innerWeight (n k x : ℕ) [NeZero n] (u v : ModularGraph.Vertex n k) : ℕ :=
  k*x^2+1+(ModularGraph.columnSlope u v)^2

noncomputable def innerHom (hx : x ≤ n) (hsize : n*x ≤ σ) :
    innerGraph (data (k := k) hx hsize) →g ModularGraph.graph n k x where
  toFun := id
  map_rel' := by
    rintro u v ⟨i,j,h⟩
    apply (ModularGraph.adj_iff_arc u v).mpr
    exact ⟨(i,j), by simpa only [ModularGraph.arc,Prod.mk.injEq,data] using h⟩

theorem inner_map_cost (hx : x ≤ n) (hsize : n*x ≤ σ)
    {u v : ModularGraph.Vertex n k} (w : (innerGraph (data hx hsize)).Walk u v) :
    WeightedNativeForcing.realCost (ModularGraph.weight n k x) (w.map (innerHom hx hsize)) =
      (natCost (innerWeight n k x) w : ℝ) := by
  induction w with
  | nil => simp [WeightedNativeForcing.realCost]
  | cons h w ih =>
    simpa [WeightedNativeForcing.realCost,Walk.map_cons,Walk.darts_cons,
      natCost,innerHom,ModularGraph.weight,innerWeight] using ih

theorem inner_map_route (hx : x ≤ n) (hsize : n*x ≤ σ) (j : ZMod n × Fin x) :
    ((innerRoute (data (k := k) hx hsize) j).map (innerHom hx hsize)) =
      ModularGraph.canonicalWalk j.1 j.2 := by
  apply Walk.ext_support
  simp [Walk.support_map,innerRoute_support,innerHom,data]

theorem inner_route_cost (hx : x ≤ n) (hsize : n*x ≤ σ) (j : ZMod n × Fin x) :
    natCost (innerWeight n k x) (innerRoute (data hx hsize) j) =
      k*(k*x^2+1+j.2.val^2) := by
  have hc := ModularGraph.canonical_native_cost (k := k) hx j.1 j.2
  have hm := inner_map_cost hx hsize (innerRoute (data (k := k) hx hsize) j)
  rw [inner_map_route] at hm
  change WeightedNativeForcing.realCost (ModularGraph.weight n k x)
    (ModularGraph.canonicalWalk j.1 j.2) = _ at hc
  have he := hm.symm.trans hc
  have hb : ((QuadraticRepair.baseline k x : ℤ) : ℝ) = (k : ℝ)*x^2+1 := by
    simp [QuadraticRepair.baseline]
  rw [hb] at he
  exact_mod_cast he

theorem inner_optimal (hx : x ≤ n) (hsize : n*x ≤ σ) (hn : (k+1)*x ≤ n) :
    InnerOptimal (data (k := k) hx hsize) (innerWeight n k x) := by
  intro j w
  obtain ⟨hmin,hunique⟩ := ModularGraph.native_optimal hn (w.map (innerHom hx hsize))
  have hc := ModularGraph.canonical_native_cost (k := k) hx j.1 j.2
  change WeightedNativeForcing.realCost (ModularGraph.weight n k x)
    (ModularGraph.canonicalWalk j.1 j.2) = _ at hc
  have hm := inner_map_cost hx hsize (innerRoute (data (k := k) hx hsize) j)
  rw [inner_map_route] at hm
  have hm' := hm.symm.trans hc
  change _ ≤ WeightedNativeForcing.realCost (ModularGraph.weight n k x)
      (w.map (innerHom hx hsize)) at hmin
  rw [inner_map_cost,← hm'] at hmin
  refine ⟨by exact_mod_cast hmin,?_⟩
  intro he
  have heq : (natCost (innerWeight n k x) w : ℝ) =
      (k : ℝ) * ((QuadraticRepair.baseline k x : ℤ) + (j.2.val : ℝ)^2) := by
    rw [he,hm']
  have heqw : (w.map (innerHom hx hsize)).support = List.ofFn (ModularGraph.point j.1 j.2) :=
    hunique ((inner_map_cost hx hsize w).trans heq)
  apply Walk.ext_support
  simpa [Walk.support_map,innerHom,innerRoute_support,data] using heqw

def separation (k x : ℕ) : ℕ := k*(k*x^2+1+x^2)+1

abbrev ProductVertex (n k σ : ℕ) :=
  ObstacleProduct.Vertex (ZMod σ) (ZMod σ) (ZMod σ) (ModularGraph.Vertex n k)

noncomputable def weight (n k x σ : ℕ) [NeZero n] [NeZero σ]
    (u v : ProductVertex n k σ) : ℝ≥0 :=
  (separation k x * primary (leftWeight n x) (rightWeight n x) u v +
    secondary (innerWeight n k x) u v : ℕ)

theorem full_optimal (hx : x ≤ n) (hsize : n*x ≤ σ)
    (hn : (k+1)*x ≤ n) (houter : 3*(n*x) ≤ σ)
    (b : ZMod σ) (j : ZMod n × Fin x)
    (q : (graph (data (k := k) hx hsize)).Walk
      (.inl ((data hx hsize).left b j)) (.inr (.inr ((data hx hsize).right b j)))) :
    WeightedNativeForcing.realCost (weight n k x σ) (fullWalk (data hx hsize) b j) ≤
      WeightedNativeForcing.realCost (weight n k x σ) q ∧
    (WeightedNativeForcing.realCost (weight n k x σ) q =
      WeightedNativeForcing.realCost (weight n k x σ) (fullWalk (data hx hsize) b j) →
      q = fullWalk (data hx hsize) b j) := by
  have hM : ∀ j, natCost (innerWeight n k x) (innerRoute (data hx hsize) j) < separation k x := by
    intro j
    rw [inner_route_cost]
    have ha : j.2.val^2 ≤ x^2 := by nlinarith [j.2.isLt]
    have hh := Nat.mul_le_mul_left k (Nat.add_le_add_left ha (k*x^2+1))
    unfold separation
    omega
  obtain ⟨hmin,hu⟩ := separated_optimal (data hx hsize)
    (leftWeight n x) (rightWeight n x) (innerWeight n k x) (2*(n*x)^2+1) (separation k x)
    (by intro a b; unfold leftWeight; omega) (by intro b c; unfold rightWeight; omega)
    (outer_small hx hsize) (outer_optimal hx hsize houter) (inner_optimal hx hsize hn) hM b j q
  let wn : ProductVertex n k σ → ProductVertex n k σ → ℕ := fun u v => separation k x * primary (leftWeight n x) (rightWeight n x) u v +
    secondary (innerWeight n k x) u v
  have hp : WeightedNativeForcing.realCost (weight n k x σ) (fullWalk (data hx hsize) b j) =
      (natCost wn (fullWalk (data hx hsize) b j) : ℝ) := realCost_nat wn _
  have hq : WeightedNativeForcing.realCost (weight n k x σ) q = (natCost wn q : ℝ) :=
    realCost_nat wn q
  rw [hp,hq]
  exact ⟨by exact_mod_cast hmin,fun h => hu (by exact_mod_cast h)⟩

theorem weight_symm (hx : x ≤ n) (hsize : n*x ≤ σ) (u v : ProductVertex n k σ) :
    (graph (data (k := k) hx hsize)).Adj u v →
      weight n k x σ u v = weight n k x σ v u := by
  intro h
  rcases h with ⟨e,h | h⟩ <;>
    have hs := congrArg Prod.fst h <;> have ht := congrArg Prod.snd h <;> dsimp at hs ht
  · rw [← hs,← ht]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩)
    · rfl
    · simp only [weight,arc,primary,secondary,Nat.mul_zero,Nat.zero_add,innerWeight,data]
      rw [ModularGraph.columnSlope_symm _ _ (ModularGraph.canonical_adj j.1 j.2 i)]
    · rfl
  · rw [← ht,← hs]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩)
    · rfl
    · simp only [weight,arc,primary,secondary,Nat.mul_zero,Nat.zero_add,innerWeight,data]
      rw [ModularGraph.columnSlope_symm _ _ (ModularGraph.canonical_adj j.1 j.2 i)]
    · rfl

theorem weight_pos (hx : x ≤ n) (hsize : n*x ≤ σ) {u v : ProductVertex n k σ}
    (h : (graph (data (k := k) hx hsize)).Adj u v) : 0 < weight n k x σ u v := by
  rcases h with ⟨e,h | h⟩ <;>
    have hs := congrArg Prod.fst h <;> have ht := congrArg Prod.snd h <;> dsimp at hs ht
  · rw [← hs,← ht]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;>
      simp only [weight,arc,primary,secondary,leftWeight,rightWeight,innerWeight,separation] <;>
      positivity
  · rw [← ht,← hs]
    rcases e with ⟨b,j⟩ | (⟨b,i,j⟩ | ⟨b,j⟩) <;>
      simp only [weight,arc,primary,secondary,leftWeight,rightWeight,innerWeight,separation] <;>
      positivity

end LinearDistancePreservers.ModularObstacle
