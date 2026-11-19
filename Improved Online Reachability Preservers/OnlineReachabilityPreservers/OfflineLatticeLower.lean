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

private theorem multiplicativePowerScale {n c power : ℕ} (large : c ≤ n)
    (cPos : 0 < c) (powerPos : 0 < power) :
    ∃ q, 0 < q ∧ c*q^power ≤ n ∧ n < c*(2*q)^power := by
  obtain ⟨q, fits, beyond⟩ := consecutiveScale (fun q => c*q^power) n (by simp [Nat.zero_pow powerPos])
    ⟨n+1, by
      calc n < n+1 := Nat.lt_succ_self n
        _ ≤ (n+1)^power := le_pow_of_positive (by omega) powerPos
        _ ≤ _ := Nat.le_mul_of_pos_left _ cPos⟩
  have qPos : 0 < q := by
    by_contra! no
    have eq : q = 0 := by omega
    simp [eq] at beyond
    omega
  refine ⟨q,qPos,fits,beyond.trans_le ?_⟩
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

private theorem cubicScale (n : ℕ) (large : 8 ≤ n) :
    ∃ q, 0 < q ∧ 8*q^3 ≤ n ∧ n < 64*q^3 := by
  obtain ⟨q,positive,fits,beyond⟩ := multiplicativePowerScale (power := 3) large (by decide) (by decide)
  exact ⟨q,positive,fits,(show 8*(2*q)^3 = 64*q^3 by ring) ▸ beyond⟩

private theorem squareScale (q p : ℕ) (qPos : 0 < q) (large : q^2 ≤ p) :
    ∃ r, 0 < r ∧ q^2*r^2 ≤ p ∧ p < 4*q^2*r^2 := by
  obtain ⟨r,positive,fits,beyond⟩ := multiplicativePowerScale (power := 2) large (Nat.pow_pos qPos) (by decide)
  exact ⟨r,positive,fits,(show q^2*(2*r)^2 = 4*q^2*r^2 by ring) ▸ beyond⟩

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

/-- Fit the two-coordinate slope family into the prescribed budgets when
neither of the linear lower constructions already gives the same rate. -/
theorem offline_grid_three_parameters {n p : ℕ} (pCap : p ≤ n^2) :
    n^3*p^4 ≤ (32*n)^6 ∨ n^3*p^4 ≤ (32*p)^6 ∨
      ∃ steps slopes : ℕ, 0 < steps ∧ 0 < slopes ∧
        16*(steps+1)*steps^3*slopes^4 ≤ n ∧ 2*steps^3*slopes^6 ≤ p ∧
        n^3*p^4 ≤ (2048*(2*steps^4*slopes^6))^6 := by
  by_cases large : 32 ≤ n
  · obtain ⟨q,qPos,qFit,qOver⟩ := multiplicativePowerScale (power := 4) large (by decide) (by decide)
    have nBound : n ≤ 512*q^4 := by
      calc
        n ≤ 32*(2*q)^4 := qOver.le
        _ = _ := by ring
    by_cases enough : 2*q^3 ≤ p
    · have cPos : 0 < 2*q^3 := by positivity
      obtain ⟨r,rPos,rFit,rOver⟩ := multiplicativePowerScale (power := 3) enough cPos (by decide)
      have pBound : p ≤ 16*q^3*r^3 := by
        calc
          p ≤ 2*q^3*(2*r)^3 := rOver.le
          _ = _ := by ring
      by_cases slopesFit : r ≤ q
      · right; right
        let steps := q/r
        let u := steps*r
        have stepPos : 0 < steps := Nat.div_pos slopesFit rPos
        have uSmall : u ≤ q := Nat.div_mul_le_self _ _
        have rLe : r ≤ u := Nat.le_mul_of_pos_left _ stepPos
        have qLe : q ≤ 2*u := by
          have split := Nat.mod_add_div q r
          rw [Nat.mul_comm r (q/r)] at split
          have remainder := Nat.mod_lt q rPos
          change q%r+u = q at split
          omega
        have vFit : 16*(steps+1)*steps^3*r^4 ≤ n := by
          calc
            _ ≤ 16*(2*steps)*steps^3*r^4 := by gcongr; omega
            _ = 32*u^4 := by dsimp [u]; ring
            _ ≤ 32*q^4 := by gcongr
            _ ≤ _ := qFit
        have pFit : 2*steps^3*r^6 ≤ p := by
          calc
            _ = 2*u^3*r^3 := by dsimp [u]; ring
            _ ≤ 2*q^3*r^3 := by gcongr
            _ ≤ _ := rFit
        have vCompare : n ≤ 8192*u^4 := by
          calc
            _ ≤ 512*q^4 := nBound
            _ ≤ 512*(2*u)^4 := by gcongr
            _ = _ := by ring
        have pCompare : p ≤ 128*u^3*r^3 := by
          calc
            _ ≤ 16*q^3*r^3 := pBound
            _ ≤ 16*(2*u)^3*r^3 := by gcongr
            _ = _ := by ring
        refine ⟨steps,r,stepPos,rPos,vFit,pFit,?_⟩
        calc
          _ ≤ (8192*u^4)^3*(128*u^3*r^3)^4 :=
            Nat.mul_le_mul (Nat.pow_le_pow_left vCompare _) (Nat.pow_le_pow_left pCompare _)
          _ = 2^67*(steps^24*r^36) := by dsimp [u]; ring
          _ ≤ 2^72*(steps^24*r^36) :=
            Nat.mul_le_mul_right _ (by decide)
          _ = _ := by ring
      · right; left
        have dense : q^6 ≤ p := by
          calc
            _ = q^3*q^3 := by ring
            _ ≤ q^3*r^3 :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
            _ ≤ 2*(q^3*r^3) := by omega
            _ = 2*q^3*r^3 := by ring
            _ ≤ _ := rFit
        calc
          _ ≤ (512*q^4)^3*p^4 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left nBound _)
          _ = 512^3*(q^6)^2*p^4 := by ring
          _ ≤ 512^3*p^2*p^4 := by gcongr
          _ ≤ 32^6*p^2*p^4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
          _ = _ := by ring
    · left
      have sparse : p^4 ≤ n^3 := by
        calc
          _ ≤ (2*q^3)^4 := Nat.pow_le_pow_left (by omega) _
          _ = 16*(q^4)^3 := by ring
          _ ≤ (32*q^4)^3 := by
            rw [mul_pow]
            exact Nat.mul_le_mul_right _ (by decide)
          _ ≤ _ := Nat.pow_le_pow_left qFit _
      calc
        _ ≤ n^3*n^3 := Nat.mul_le_mul_left _ sparse
        _ = n^6 := by ring
        _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  · left
    calc
      _ ≤ n^3*(n^2)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pCap _)
      _ = n^5*n^6 := by ring
      _ ≤ 32^5*n^6 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
      _ ≤ 32^6*n^6 := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by ring

/-- With two freely chosen slope coordinates, the lattice forces
on the order of `n^(1/2)*p^(2/3)` edges at the prescribed counts. -/
theorem offline_grid_three_lower_all_sizes {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (pCap : p ≤ n^2) :
    ∃ (G D : Arcs (Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → n^3*p^4 ≤ (2048*H.card)^6 := by
  rcases offline_grid_three_parameters pCap with sparse | dense | ⟨steps, slopes, positive, _, fits, demandFits, bound⟩
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
  · obtain ⟨G,D,dag,card,_,forced⟩ :=
      multidimensional_offline_lattice_lower (dimension := 2) (slopes := slopes) positive
    have vCount : Fintype.card (OrderedGridVertex 2 steps slopes) = 16*(steps+1)*steps^3*slopes^4 := by
      rw [orderedGridVertex_card]
      ring
    have dCount : D.card = 2*steps^3*slopes^6 := by
      rw [card]
      ring
    have forced' (H : Arcs (OrderedGridVertex 2 steps slopes)) (sub : H ⊆ G)
        (preserved : Preserves G H D.toList) : 2*steps^4*slopes^6 ≤ H.card := by
      rw [forced H sub preserved, dCount]
      exact le_of_eq (by ring)
    obtain ⟨big,requests,dagBig,size,lower⟩ := pad_offline_instance G D dag
      (vCount.trans_le fits) (dCount.trans_le demandFits) pCap forced'
    refine ⟨big,requests,dagBig,size,?_⟩
    intro H sub preserves
    exact bound.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (lower H sub preserves)) _)

/-- The same exact-size lower bound written with real exponents. -/
theorem offline_grid_three_lower_all_sizes_real {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (pCap : p ≤ n^2) :
    ∃ (G D : Arcs (Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList →
        (n : ℝ)^(1/2 : ℝ)*(p : ℝ)^(2/3 : ℝ) ≤ 2048*(H.card : ℝ) := by
  obtain ⟨G,D,dag,size,bound⟩ := offline_grid_three_lower_all_sizes hn hp pCap
  refine ⟨G,D,dag,size,?_⟩
  intro H sub preserves
  have powers : ((n : ℝ)^(1/2 : ℝ)*(p : ℝ)^(2/3 : ℝ))^6 = (n : ℝ)^3*(p : ℝ)^4 := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_mul_natCast (by positivity),
      show (1/2 : ℝ)*(6 : ℕ) = (3 : ℕ) by norm_num,
      show (2/3 : ℝ)*(6 : ℕ) = (4 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (6 : ℕ) ≠ 0)).mp
  rw [powers]
  exact_mod_cast bound H sub preserves

/-- One instance forces the sum of the linear terms and both lattice rates,
up to a universal constant. -/
theorem offline_lower_all_sizes_with_two_lattices {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (pCap : p ≤ n^2) :
    ∃ (G D : Arcs (Fin n)), IsDAG G ∧ D.card = p ∧
      ∀ H ⊆ G, Preserves G H D.toList → (n : ℝ) + p +
        (n : ℝ)^(2/3 : ℝ)*(p : ℝ)^(1/2 : ℝ) + (n : ℝ)^(1/2 : ℝ)*(p : ℝ)^(2/3 : ℝ) ≤
          4096*(H.card : ℝ) := by
  let base : ℝ := (n : ℝ) + p + (n : ℝ)^(2/3 : ℝ)*(p : ℝ)^(1/2 : ℝ)
  let more : ℝ := (n : ℝ)^(1/2 : ℝ)*(p : ℝ)^(2/3 : ℝ)
  by_cases dominates : more ≤ base
  · obtain ⟨G,D,dag,size,lower⟩ := offline_lower_all_sizes_with_linear hn hp pCap
    refine ⟨G,D,dag,size,?_⟩
    intro H sub preserves
    change base + more ≤ _
    have forcing : base ≤ 768*(H.card : ℝ) := lower H sub preserves
    linarith only [dominates, forcing, show (0 : ℝ) ≤ H.card by positivity]
  · obtain ⟨G,D,dag,size,lower⟩ := offline_grid_three_lower_all_sizes_real hn hp pCap
    refine ⟨G,D,dag,size,?_⟩
    intro H sub preserves
    change base + more ≤ _
    have forcing : more ≤ 2048*(H.card : ℝ) := lower H sub preserves
    exact (add_le_add (le_of_not_ge dominates) le_rfl).trans (by linarith only [forcing])

end OnlineReachabilityPreservers.SourceAudit
