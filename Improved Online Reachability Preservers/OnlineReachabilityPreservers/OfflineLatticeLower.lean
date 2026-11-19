import OnlineReachabilityPreservers.GraphRelabel
import OnlineReachabilityPreservers.OfflineDemandLower
import OnlineReachabilityPreservers.OverlayLowerAudit

/-! Fixed-graph offline lattice lower bounds at the prescribed vertex and demand counts. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

private theorem consecutiveScale (f : ℕ → ℕ) (v : ℕ)
    (initial : f 0 ≤ v) (existsLarger : ∃ t, v < f t) :
    ∃ q, f q ≤ v ∧ v < f (q+1) := by
  let cut := Nat.find existsLarger
  have beyond : v < f cut := Nat.find_spec existsLarger
  have positive : 0 < cut := by
    by_contra! notPositive
    have eq : cut = 0 := by omega
    exact (not_lt_of_ge initial) (eq ▸ beyond)
  let q := cut-1
  have qSmall : q < cut := by dsimp [q]; omega
  refine ⟨q, Nat.le_of_not_gt (Nat.find_min existsLarger qSmall), ?_⟩
  exact (show cut = q+1 by dsimp [q]; omega) ▸ beyond

private theorem le_pow_of_positive {a k : ℕ} (aPos : 0 < a) (kPos : 0 < k) : a ≤ a^k := by
  simpa only [pow_one] using Nat.pow_le_pow_right aPos kPos

private theorem cubicScale (n : ℕ) (large : 8 ≤ n) :
    ∃ q, 0 < q ∧ 8*q^3 ≤ n ∧ n < 64*q^3 := by
  obtain ⟨q, fit, beyond⟩ := consecutiveScale (fun q => 8*q^3) n (by simp)
    ⟨n+1, by
      calc n < n+1 := Nat.lt_succ_self n
        _ ≤ (n+1)^3 := le_pow_of_positive (by omega) (by decide)
        _ ≤ _ := Nat.le_mul_of_pos_left _ (by decide)⟩
  have qPos : 0 < q := by
    by_contra! zero
    have eq : q = 0 := by omega
    simp [eq] at beyond
    omega
  refine ⟨q, qPos, fit, beyond.trans_le ?_⟩
  calc
    8*(q+1)^3 ≤ 8*(2*q)^3 := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = 64*q^3 := by ring

private theorem squareScale (q p : ℕ) (qPos : 0 < q) (large : q^2 ≤ p) :
    ∃ r, 0 < r ∧ q^2*r^2 ≤ p ∧ p < 4*q^2*r^2 := by
  obtain ⟨r, fit, beyond⟩ := consecutiveScale (fun r => q^2*r^2) p (by simp)
    ⟨p+1, by
      calc p < p+1 := Nat.lt_succ_self p
        _ ≤ (p+1)^2 := le_pow_of_positive (by omega) (by decide)
        _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.pow_pos qPos)⟩
  have rPos : 0 < r := by
    by_contra! zero
    have eq : r = 0 := by omega
    simp [eq] at beyond
    exact (not_lt_of_ge large) beyond
  refine ⟨r, rPos, fit, beyond.trans_le ?_⟩
  calc
    q^2*(r+1)^2 ≤ q^2*(2*r)^2 := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = 4*q^2*r^2 := by ring

/-- In the two linear regimes a single linear construction is sufficient.
In the remaining range, fit a lattice with independent layer and slope
counts inside both prescribed budgets. -/
theorem offline_lattice_parameters {n p : ℕ} (pUpper : p ≤ n^2) :
    n^4*p^3 ≤ (4*n)^6 ∨ n^4*p^3 ≤ (16*p)^6 ∨
      ∃ steps slopes : ℕ, 0 < steps ∧ 0 < slopes ∧
        4*(steps+1)*steps^2*slopes^3 ≤ n ∧ steps^2*slopes^4 ≤ p ∧
          n^4*p^3 ≤ (256*(steps^3*slopes^4))^6 := by
  by_cases large : 8 ≤ n
  · obtain ⟨q, qPos, qFit, qOver⟩ := cubicScale n large
    by_cases enough : q^2 ≤ p
    · obtain ⟨r, rPos, rFit, rOver⟩ := squareScale q p qPos enough
      by_cases slopesFit : r ≤ q
      · right; right
        let steps := q/r
        let u := steps*r
        have stepPos : 0 < steps := Nat.div_pos slopesFit rPos
        have uSmall : u ≤ q := Nat.div_mul_le_self _ _
        have rLe : r ≤ u := Nat.le_mul_of_pos_left _ stepPos
        have qLe : q ≤ 2*u := by
          have divRem := Nat.mod_add_div q r
          rw [Nat.mul_comm r (q/r)] at divRem
          have remainder := Nat.mod_lt q rPos
          change q%r+u = q at divRem
          omega
        have vFit : 4*(steps+1)*steps^2*r^3 ≤ n := by
          calc
            _ ≤ 4*(2*steps)*steps^2*r^3 := by gcongr; omega
            _ = 8*u^3 := by dsimp [u]; ring
            _ ≤ 8*q^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left uSmall _)
            _ ≤ _ := qFit
        have pFit : steps^2*r^4 ≤ p := by
          calc
            _ = u^2*r^2 := by dsimp [u]; ring
            _ ≤ q^2*r^2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left uSmall _)
            _ ≤ _ := rFit
        have vert : n ≤ 512*u^3 := by
          calc
            _ ≤ 64*q^3 := qOver.le
            _ ≤ 64*(2*u)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left qLe _)
            _ = _ := by ring
        have pairs : p ≤ 16*u^2*r^2 := by
          calc
            _ ≤ 4*q^2*r^2 := rOver.le
            _ ≤ 4*(2*u)^2*r^2 := by gcongr
            _ = _ := by ring
        refine ⟨steps,r,stepPos,rPos,vFit,pFit,?_⟩
        calc
          _ ≤ (512*u^3)^4*(16*u^2*r^2)^3 :=
            Nat.mul_le_mul (Nat.pow_le_pow_left vert _) (Nat.pow_le_pow_left pairs _)
          _ = _ := by dsimp [u]; ring
      · right; left
        have dense : q^4 ≤ p := by
          calc
            _ = q^2*q^2 := by ring
            _ ≤ q^2*r^2 := by gcongr; omega
            _ ≤ _ := rFit
        calc
          _ ≤ (64*q^3)^4*p^3 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left qOver.le _)
          _ = 64^4*(q^4)^3*p^3 := by ring
          _ ≤ 64^4*p^3*p^3 := by gcongr
          _ = _ := by ring
    · left
      have sparse : p^3 ≤ n^2 := by
        calc
          _ ≤ (q^2)^3 := Nat.pow_le_pow_left (by omega) _
          _ = (q^3)^2 := by ring
          _ ≤ _ := Nat.pow_le_pow_left (by omega) _
      calc
        _ ≤ n^4*n^2 := Nat.mul_le_mul_left _ sparse
        _ = n^6 := by ring
        _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  · left
    calc
      _ ≤ n^4*(n^2)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pUpper _)
      _ = n^4*n^6 := by ring
      _ ≤ 8^4*n^6 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by ring

private theorem pad_offline_instance {A : Type*} [Fintype A] {n p required : ℕ}
    (G D : Arcs A) (dag : IsDAG G) (fits : Fintype.card A ≤ n) (enough : D.card ≤ p)
    (pCap : p ≤ n^2) (forced : ∀ H ⊆ G, Preserves G H D.toList → required ≤ H.card) :
    ∃ (g d : Arcs (Fin n)), IsDAG g ∧ d.card = p ∧
      ∀ H ⊆ g, Preserves g H d.toList → required ≤ H.card := by
  classical
  let f := (Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb fits)
  let arcs := f.prodMap f
  let g := G.map arcs
  have gDag : IsDAG g := by
    intro u v edge back
    obtain ⟨e, present, eq⟩ := mem_map.mp edge
    have backwards : Reach g (f e.2) (f e.1) := by
      have sameLeft := congrArg Prod.fst eq
      have sameRight := congrArg Prod.snd eq
      change f e.1 = u at sameLeft
      change f e.2 = v at sameRight
      rw [sameRight, sameLeft]
      exact back
    exact dag present ((reach_relabel f).mp backwards)
  let active := D.map arcs
  have slots : p ≤ (univ : Arcs (Fin n)).card := by simpa [pow_two] using pCap
  have activeFits : active.card ≤ p := (card_map arcs).trans_le enough
  obtain ⟨d, includeActive, _, dSize⟩ := exists_subsuperset_card_eq (subset_univ active) activeFits slots
  refine ⟨g,d,gDag,dSize,?_⟩
  intro H sub preserves
  let small := G.filter fun e => arcs e ∈ H
  have smallSub : small ⊆ G := filter_subset _ _
  have smallMap : small.map arcs = H := by
    ext e
    constructor
    · intro member
      obtain ⟨original, kept, rfl⟩ := mem_map.mp member
      exact (mem_filter.mp kept).2
    · intro member
      obtain ⟨original, kept, same⟩ := mem_map.mp (sub member)
      exact mem_map.mpr ⟨original, mem_filter.mpr ⟨kept, same ▸ member⟩, same⟩
  have smallPreserves : Preserves G small D.toList := by
    intro pair member
    have inMap : arcs pair ∈ d.toList := mem_toList.mpr (includeActive (mem_map_of_mem _ (mem_toList.mp member)))
    have actual := preserves (arcs pair) inMap
    rw [← smallMap] at actual
    exact (reach_relabel f (G := small)).symm.trans (actual.trans (reach_relabel f (G := G)))
  rw [← smallMap, card_map]
  exact forced small smallSub smallPreserves

/-- A finite lower bound of order `n^(2/3)*sqrt p` at the original
vertex and demand counts. Additive linear lower bounds are separate. -/
theorem offline_lattice_lower_all_sizes {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (pCap : p ≤ n^2) :
    ∃ (G D : Arcs (Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → n^4*p^3 ≤ (256*H.card)^6 := by
  rcases offline_lattice_parameters pCap with sparse | dense | ⟨steps, slopes, positive, _, fits, demandFits, bound⟩
  · obtain ⟨G,D,dag,card,lower⟩ := offline_linear_vertex_lower hn hp pCap
    refine ⟨G,D,dag,card,?_⟩
    intro H sub preserves
    have edges := lower H sub preserves
    exact sparse.trans (Nat.pow_le_pow_left (by omega) _)
  · obtain ⟨G,D,dag,card,lower⟩ := offline_linear_demand_lower hn pCap
    refine ⟨G,D,dag,card,?_⟩
    intro H sub preserves
    have edges := lower H sub preserves
    exact dense.trans (Nat.pow_le_pow_left (by omega) _)
  · obtain ⟨G,D,dag,card,_,forced⟩ := two_parameter_offline_lattice_lower (slopes := slopes) positive
    have fits' : Fintype.card (OrderedLatticeVertex steps slopes) ≤ n := (orderedLatticeVertex_card _ _).trans_le fits
    obtain ⟨big, requests, dagBig, size, lower⟩ :=
      pad_offline_instance G D dag fits' (card.trans_le demandFits) pCap
        (fun H sub preserves => (forced H sub preserves).ge)
    refine ⟨big,requests,dagBig,size,?_⟩
    intro H sub preserves
    exact bound.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (lower H sub preserves)) _)

/-- The exact-size lattice bound in terms of the usual real exponents. -/
theorem offline_lattice_lower_all_sizes_real {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (pCap : p ≤ n^2) :
    ∃ (G D : Arcs (Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList →
        (n : ℝ)^(2/3 : ℝ) * (p : ℝ)^(1/2 : ℝ) ≤ 256*(H.card : ℝ) := by
  obtain ⟨G,D,dag,size,bound⟩ := offline_lattice_lower_all_sizes hn hp pCap
  refine ⟨G,D,dag,size,?_⟩
  intro H sub preserves
  have powers : ((n : ℝ)^(2/3 : ℝ) * (p : ℝ)^(1/2 : ℝ))^6 = (n : ℝ)^4 * (p : ℝ)^3 := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_mul_natCast (by positivity),
      show (2/3 : ℝ)*(6 : ℕ) = (4 : ℕ) by norm_num,
      show (1/2 : ℝ)*(6 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (6 : ℕ) ≠ 0)).mp
  rw [powers]
  exact_mod_cast bound H sub preserves

/-- At the prescribed counts, one instance forces the sum of the two linear
terms and the lattice term, up to a universal constant. -/
theorem offline_lower_all_sizes_with_linear {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (pCap : p ≤ n^2) :
    ∃ (G D : Arcs (Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (n : ℝ) + p +
        (n : ℝ)^(2/3 : ℝ) * (p : ℝ)^(1/2 : ℝ) ≤ 768*(H.card : ℝ) := by
  let lattice : ℝ := (n : ℝ)^(2/3 : ℝ) * (p : ℝ)^(1/2 : ℝ)
  by_cases linear : lattice ≤ max (n : ℝ) p
  · by_cases vertices : (p : ℝ) ≤ n
    · obtain ⟨G,D,dag,size,force⟩ := offline_linear_vertex_lower hn hp pCap
      refine ⟨G,D,dag,size,?_⟩
      intro H sub preserves
      have lower := force H sub preserves
      have twice : (n : ℝ) ≤ 2*(H.card : ℝ) := by
        exact_mod_cast (show n ≤ 2*H.card by omega)
      have latticeLe : lattice ≤ n := (max_eq_left vertices) ▸ linear
      change (n : ℝ) + p + lattice ≤ _
      linarith only [vertices, twice, latticeLe, show (0 : ℝ) ≤ H.card by positivity]
    · obtain ⟨G,D,dag,size,force⟩ := offline_linear_demand_lower hn pCap
      refine ⟨G,D,dag,size,?_⟩
      intro H sub preserves
      have six : (p : ℝ) ≤ 6*(H.card : ℝ) := by exact_mod_cast force H sub preserves
      have demands : (n : ℝ) ≤ p := (lt_of_not_ge vertices).le
      have latticeLe : lattice ≤ p := (max_eq_right demands) ▸ linear
      change (n : ℝ) + p + lattice ≤ _
      linarith only [demands, six, latticeLe, show (0 : ℝ) ≤ H.card by positivity]
  · obtain ⟨G,D,dag,size,force⟩ := offline_lattice_lower_all_sizes_real hn hp pCap
    refine ⟨G,D,dag,size,?_⟩
    intro H sub preserves
    have both := max_le_iff.mp (lt_of_not_ge linear).le
    change (n : ℝ) + p + lattice ≤ _
    have forced : lattice ≤ 256*(H.card : ℝ) := force H sub preserves
    linarith only [both.1, both.2, forced]

end OnlineReachabilityPreservers.SourceAudit
