import OnlineReachabilityPreservers.IntersectionOrder
import OnlineReachabilityPreservers.DagReduction

/-! Initial pairwise incidence bound for acyclic half-four-bridge-free systems. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]
variable {K : Type*} [LinearOrder K]

private def highDegree (paths : I → Finset V) (d : ℕ) (i : I) : Finset V :=
  (paths i).filter (fun v => d ≤ (occurrences paths v).card)

private def earlierVertices (s : Finset V) (position : V → K) (y : V) : Finset V :=
  s.filter fun x => position x < position y

private def goodVertices (paths : I → Finset V) (position : I → V → K) (d ℓ : ℕ) (i : I) : Finset V :=
  (highDegree paths d i).filter fun y => ℓ ≤ (earlierVertices (highDegree paths d i) (position i) y).card

omit [LinearOrder I] in
private theorem highDegree_sum (paths : I → Finset V) (d : ℕ) :
    (∑ i, (paths i).card) ≤ (∑ i, (highDegree paths d i).card) + Fintype.card V * d := by
  let low (i : I) := (paths i).filter fun v => ¬ d ≤ (occurrences paths v).card
  have light : (∑ i, (low i).card) ≤ Fintype.card V * d := by
    rw [← sum_occurrences low]
    calc
      _ ≤ ∑ v : V, d := by
        apply sum_le_sum
        intro v _
        by_cases hv : d ≤ (occurrences paths v).card
        · have hempty : occurrences low v = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro i hi
            have hl : v ∈ low i := (mem_filter.mp hi).2
            exact (mem_filter.mp hl).2 hv
          simp [hempty]
        · refine (card_le_card ?_ : (occurrences low v).card ≤ (occurrences paths v).card).trans
            (Nat.le_of_lt (lt_of_not_ge hv))
          intro i hi
          exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (mem_filter.mp hi).2).1⟩
      _ = _ := by simp
  calc
    _ = ∑ i, ((highDegree paths d i).card + (low i).card) :=
      sum_congr rfl fun i _ => (card_filter_add_card_filter_not _).symm
    _ ≤ _ := by rw [sum_add_distrib]; gcongr

omit [Fintype V] [LinearOrder V] in
private theorem early_count (s : Finset V) (position : V → K) (unique : Set.InjOn position s) (ℓ : ℕ) :
    (s.filter fun y => ¬ ℓ ≤ (earlierVertices s position y).card).card ≤ ℓ := by
  have increase {x y : V} (hx : x ∈ s) (advance : position x < position y) :
      (earlierVertices s position x).card < (earlierVertices s position y).card := by
    apply card_lt_card
    rw [ssubset_iff_subset_ne]
    refine ⟨fun w hw => mem_filter.mpr ⟨(mem_filter.mp hw).1, (mem_filter.mp hw).2.trans advance⟩, ?_⟩
    intro equal
    have hx' : x ∈ earlierVertices s position y := mem_filter.mpr ⟨hx, advance⟩
    rw [← equal] at hx'
    exact (lt_irrefl _) (mem_filter.mp hx').2
  calc
    _ ≤ (range ℓ).card := by
      apply card_le_card_of_injOn (fun y => (earlierVertices s position y).card)
      · intro y hy
        exact mem_range.mpr (lt_of_not_ge (mem_filter.mp hy).2)
      · intro x hx y hy eq
        obtain ⟨hx, _⟩ := mem_filter.mp hx
        obtain ⟨hy, _⟩ := mem_filter.mp hy
        rcases lt_trichotomy (position x) (position y) with earlier | same | later
        · exact ((increase hx earlier).ne eq).elim
        · exact unique hx hy same
        · exact ((increase hy later).ne' eq).elim
    _ = _ := card_range ℓ

omit [Fintype V] [LinearOrder I] in
private theorem goodVertices_sum (paths : I → Finset V) (position : I → V → K)
    (unique : ∀ i, Set.InjOn (position i) (paths i)) (d ℓ : ℕ) :
    (∑ i, (highDegree paths d i).card) ≤
      (∑ i, (goodVertices paths position d ℓ i).card) + Fintype.card I * ℓ := by
  rw [← show (∑ _ : I, ℓ) = Fintype.card I * ℓ by simp, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  let s := highDegree paths d i
  have eq := card_filter_add_card_filter_not (s := s) (fun y => ℓ ≤ (earlierVertices s (position i) y).card)
  change s.card ≤ (goodVertices paths position d ℓ i).card + ℓ
  rw [← eq]
  exact Nat.add_le_add_left (early_count s (position i) ((unique i).mono (filter_subset _ _)) ℓ) _

omit [Fintype I] in
private theorem card_erase_lower {s : Finset I} (i : I) : s.card ≤ (s.erase i).card + 1 := by
  by_cases hi : i ∈ s
  · rw [card_erase_add_one hi]
  · simp [erase_eq_of_notMem hi]

/-- Every good collision extends at each high-degree predecessor to a distinct counted chain. -/
private theorem extend_collisions (paths : I → Finset V) (position : I → V → K)
    (chains : Finset ((I × I) × (I × V × V)))
    (accept : ∀ {l m r x y}, l ≠ m → l ≠ r → r < m → x ∈ paths l → y ∈ paths r →
      x ∈ paths m → y ∈ paths m → position m x < position m y → ((l, r), m, x, y) ∈ chains)
    (d ℓ : ℕ) :
    (collisions (goodVertices paths position d ℓ)).card * (ℓ * (d - 2)) ≤ chains.card := by
  classical
  let g := collisions (goodVertices paths position d ℓ)
  let prior (w : V × I × I) := earlierVertices (highDegree paths d w.2.2) (position w.2.2) w.1
  let choices (w : V × I × I) (x : V) := ((occurrences paths x).erase w.2.2).erase w.2.1
  let pairs := g.sigma fun w => (prior w).sigma (choices w)
  let witness (w : Σ _ : V × I × I, Σ _ : V, I) : (I × I) × (I × V × V) :=
    ((w.2.2, w.1.2.1), (w.1.2.2, w.2.1, w.1.1))
  have into : pairs.card ≤ chains.card := by
    apply card_le_card_of_injOn witness
    · rintro ⟨⟨y, r, m⟩, x, l⟩ hp
      obtain ⟨hw, hxl⟩ := mem_sigma.mp hp
      have hc : (y, r, m) ∈ collisions (goodVertices paths position d ℓ) := hw
      obtain ⟨_, hrm, hyr, hym⟩ := mem_filter.mp hc
      obtain ⟨hx, hl⟩ := mem_sigma.mp hxl
      have hx' : x ∈ earlierVertices (highDegree paths d m) (position m) y := hx
      have hl' : l ∈ ((occurrences paths x).erase m).erase r := hl
      obtain ⟨hlr, hlm, hli⟩ := by
        simpa only [mem_erase] using hl'
      exact accept hlm hlr hrm (mem_filter.mp hli).2
        (mem_filter.mp (mem_filter.mp hyr).1).1
        (mem_filter.mp (mem_filter.mp hx').1).1
        (mem_filter.mp (mem_filter.mp hym).1).1 (mem_filter.mp hx').2
    · rintro ⟨⟨y, r, m⟩, x, l⟩ _ ⟨⟨y', r', m'⟩, x', l'⟩ _ he
      change ((l, r), m, x, y) = ((l', r'), m', x', y') at he
      cases he
      rfl
  refine le_trans ?_ into
  rw [card_sigma]
  calc
    _ = ∑ w ∈ g, ℓ * (d - 2) := by simp [g]
    _ ≤ _ := by
      apply sum_le_sum
      intro w hw
      have hg : w ∈ collisions (goodVertices paths position d ℓ) := hw
      have hℓ : ℓ ≤ (prior w).card := (mem_filter.mp (mem_filter.mp hg).2.2.2).2
      rw [card_sigma]
      calc
        _ ≤ (prior w).card * (d - 2) := Nat.mul_le_mul_right _ hℓ
        _ = ∑ x ∈ prior w, (d - 2) := by simp
        _ ≤ _ := by
          apply sum_le_sum
          intro x hx
          have hprior : x ∈ earlierVertices (highDegree paths d w.2.2) (position w.2.2) w.1 := hx
          have hd := (mem_filter.mp (mem_filter.mp hprior).1).2
          have hm := card_erase_lower (s := occurrences paths x) w.2.2
          have hr := card_erase_lower (s := (occurrences paths x).erase w.2.2) w.2.1
          change d - 2 ≤ (((occurrences paths x).erase w.2.2).erase w.2.1).card
          omega

private theorem cut_budget {m n : ℕ} (hn : 0 < n) (hm : 4 * n ≤ m) :
    0 < m / (4 * n) ∧ m ≤ 8 * n * (m / (4 * n)) := by
  have h4 : 0 < 4 * n := by omega
  have hd := Nat.div_pos hm h4
  have h := Nat.lt_mul_div_succ m h4
  refine ⟨hd, ?_⟩
  have hnext : m / (4 * n) + 1 ≤ 2 * (m / (4 * n)) := by omega
  exact h.le.trans ((Nat.mul_le_mul_left (4 * n) hnext).trans (by ring_nf; rfl))

/-- A finite version of the Appendix A lower count, obtained by thresholding incidences.
This avoids assuming a split or cleaning operation preserves the bridge condition. -/
theorem lemma26_ranked_chain_lower (paths : I → Finset V) (position : I → V → K)
    (unique : ∀ i, Set.InjOn (position i) (paths i))
    (chains : Finset ((I × I) × (I × V × V)))
    (accept : ∀ {l m r x y}, l ≠ m → l ≠ r → r < m → x ∈ paths l → y ∈ paths r →
      x ∈ paths m → y ∈ paths m → position m x < position m y → ((l, r), m, x, y) ∈ chains)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (hdense : 16 * Fintype.card V ≤ ∑ i, (paths i).card)
    (hlong : 8 * Fintype.card I ≤ ∑ i, (paths i).card) :
    (∑ i, (paths i).card)^4 ≤ 2048 * (Fintype.card V)^2 * Fintype.card I *
      chains.card := by
  let n := Fintype.card V
  let p := Fintype.card I
  let m := ∑ i, (paths i).card
  let d := m / (4 * n)
  let ℓ := m / (4 * p)
  let G := ∑ i, (goodVertices paths position d ℓ i).card
  let Q := (collisions (goodVertices paths position d ℓ)).card
  have hclean := highDegree_sum paths d
  have hgood := goodVertices_sum paths position unique d ℓ
  change m ≤ (∑ i, (highDegree paths d i).card) + n*d at hclean
  change (∑ i, (highDegree paths d i).card) ≤ G + p*ℓ at hgood
  have hdn : 4 * (n * d) ≤ m := by
    have h := Nat.div_mul_le_self m (4*n)
    convert h using 1
    ring
  have hlp : 4 * (p * ℓ) ≤ m := by
    have h := Nat.div_mul_le_self m (4*p)
    convert h using 1
    ring
  have hmG : m ≤ 2 * G := by omega
  have hlong' : 8*p ≤ m := hlong
  have hdense' : 16*n ≤ m := hdense
  have hGn : 2*n ≤ G := by omega
  have hCS : G^2 ≤ n * (G + 2*Q) := incidence_square (goodVertices paths position d ℓ) Q le_rfl
  have hGQ : G^2 ≤ 4*n*Q := by
    have h := Nat.mul_le_mul_right G hGn
    nlinarith only [h, hCS]
  have hMQ : m^2 ≤ 16*n*Q := by
    have h := Nat.pow_le_pow_left hmG 2
    nlinarith only [h, hGQ]
  have hmd := (cut_budget hn (show 4*n ≤ m by omega)).2
  have hmℓ := (cut_budget hp (show 4*p ≤ m by omega)).2
  have hd4 : 4 ≤ d := (Nat.le_div_iff_mul_le (by omega : 0 < 4*n)).mpr (by omega)
  have hdd : d ≤ 2 * (d - 2) := by omega
  have hmD : m ≤ 16*n*(d - 2) := hmd.trans
    ((Nat.mul_le_mul_left (8*n) hdd).trans (by ring_nf; rfl))
  have hcount : Q * (ℓ * (d - 2)) ≤ chains.card := extend_collisions paths position chains (fun a b c d e f g h => accept a b c d e f g h) d ℓ
  change m^4 ≤ 2048 * n^2 * p * chains.card
  calc
    m^4 = m^2 * m * m := by ring
    _ ≤ (16*n*Q) * (8*p*ℓ) * (16*n*(d - 2)) := by gcongr
    _ = (2048*n^2*p) * (Q * (ℓ * (d - 2))) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hcount

/-- The Appendix A lower count when all paths use a common vertex order. -/
theorem lemma26_chain_lower (paths : I → Finset V)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (hdense : 16 * Fintype.card V ≤ ∑ i, (paths i).card)
    (hlong : 8 * Fintype.card I ≤ ∑ i, (paths i).card) :
    (∑ i, (paths i).card)^4 ≤ 2048 * (Fintype.card V)^2 * Fintype.card I * (rChains paths).card :=
  lemma26_ranked_chain_lower paths (fun _ v => v) (fun _ _ _ _ _ eq => eq) (rChains paths)
    (fun lm lr earlier left right mx my order => mem_rChains.mpr ⟨lm, lr, earlier, left, right, mx, my, order⟩)
    hn hp hdense hlong

/-- The initial bound (Lemma 27) on the acyclic systems used by the growth algorithms. -/
theorem lemma27_acyclic (paths : I → Finset V) (free : HalfBridgeFree (PathBefore paths) 4) :
    let n := Fintype.card V
    let p := Fintype.card I
    let m := ∑ i, (paths i).card
    m ≤ 16*n ∨ m ≤ 8*p ∨ m^3 ≤ 2048 * (n*p)^2 := by
  dsimp only
  let n := Fintype.card V
  let p := Fintype.card I
  let m := ∑ i, (paths i).card
  by_cases hmn : m ≤ 16*n
  · exact Or.inl hmn
  by_cases hmp : m ≤ 8*p
  · exact Or.inr (Or.inl hmp)
  have hcap : m ≤ p*n := calc
    _ ≤ ∑ _ : I, n := sum_le_sum (fun _ _ => card_le_univ _)
    _ = _ := by simp [p]
  have hn : 0 < n := Nat.pos_of_ne_zero (by intro e; rw [e, mul_zero] at hcap; omega)
  have hp : 0 < p := Nat.pos_of_ne_zero (by intro e; rw [e, zero_mul] at hcap; omega)
  have hm : 0 < m := by omega
  have hlower := lemma26_chain_lower paths hn hp (show 16*n ≤ m by omega)
    (show 8*p ≤ m by omega)
  have hupper : (rChains paths).card ≤ p*m := rChains_upper free
  have h : m^4 ≤ (2048*n^2*p) * (p*m) :=
    hlower.trans (Nat.mul_le_mul_left _ hupper)
  refine Or.inr (Or.inr (Nat.le_of_mul_le_mul_right ?_ hm))
  convert h using 1 <;> ring

/-- Forward growth gives a common-order half-4-bridge-free family. -/
theorem orderedCompression_free {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    HalfBridgeFree (PathBefore (topologicalPaths G (compressed G D))) 4 := by
  intro k _ b
  let old : Bridge (CompressedBefore G D) k :=
    b.reverse.mapVertices (topologicalEquiv G).symm (topologicalEquiv G).symm.injective
      (fun _ _ _ h => topologicalPaths_step dag
        (fun i {_ _} hx hy ne => compressedBefore_total (G := G) (D := D) (i := i) hx hy ne) h)
  simpa [old, Bridge.mapVertices, Bridge.reverse, Function.comp_def, Fin.rev_zero] using
    no_earlier_first_arc dag old

theorem edge_bound_of_incidence {m n p : ℕ} (cap : m ≤ n^2)
    (h : m + p ≤ 16*n ∨ m + p ≤ 8*p ∨ (m + p)^3 ≤ 2048 * (n*p)^2) :
    m ≤ 16*n ∨ m^3 ≤ 2048 * (n*p)^2 := by
  rcases h with h | h | h
  · exact Or.inl (by omega)
  · right
    calc
      m^3 = m^2 * m := by ring
      _ ≤ (8*p)^2 * n^2 := Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) cap
      _ = 64 * (n*p)^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by decide)
  · exact Or.inr ((Nat.pow_le_pow_left (Nat.le_add_right m p) 3).trans h)

/-- The Appendix A initial exponent on the actual forward-growth output, without endpoints
specified in advance. The bound applies to each prefix of the request list. -/
theorem forwardRun_pairwise_initial {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    let m := (forwardRun G D).card
    let n := Fintype.card V
    let p := D.length
    m ≤ 16*n ∨ m^3 ≤ 2048 * (n*p)^2 := by
  let : Fintype (Set.range (reverseTopologicalKey G)) :=
    Fintype.ofEquiv V (topologicalEquiv G)
  have h := lemma27_acyclic (topologicalPaths G (compressed G D)) (orderedCompression_free dag D)
  simp only [← Fintype.card_congr (topologicalEquiv G), Fintype.card_fin, topologicalPaths, card_map,
    compressed_total dag D] at h
  have cap := card_le_univ (forwardRun G D)
  rw [Fintype.card_prod, ← pow_two] at cap
  exact edge_bound_of_incidence cap h

/-- The same initial pairwise bound on Algorithm 2, by reversing the digraph. -/
theorem backwardRun_pairwise_initial {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    let m := (backwardRun G D).card
    let n := Fintype.card V
    let p := D.length
    m ≤ 16*n ∨ m^3 ≤ 2048 * (n*p)^2 := by
  simpa only [backwardRun, reverseArcs_card, List.length_map] using
    forwardRun_pairwise_initial (reverseArcs_dag dag) (D.map Prod.swap)

/-- The initial pairwise bound on arbitrary digraphs with the SCC connector overhead. -/
theorem pairwise_initial (G : Arcs V) (D : List (V × V)) :
    let H := sinkPreserver G D
    let n := Fintype.card V
    H ⊆ G ∧ Preserves G H D ∧
      (H.card ≤ 18*n ∨ (H.card - 2*n)^3 ≤ 2048 * (n * D.length)^2) := by
  obtain ⟨sub, preserves, overhead⟩ := sinkPreserver_spec G D
  have h := forwardRun_pairwise_initial (condensation_dag G) (D.map (projectDemand G))
  simp only [List.length_map] at h
  refine ⟨sub, preserves, ?_⟩
  rcases h with h | h
  · exact Or.inl (by omega)
  · exact Or.inr ((Nat.pow_le_pow_left (show (sinkPreserver G D).card - 2 * Fintype.card V ≤
        (forwardRun (condensation G) (D.map (projectDemand G))).card by omega) 3).trans h)

end OnlineReachabilityPreservers
