import Mathlib.Data.Finset.Powerset
import OnlineReachabilityPreservers.CyclicIntersections
import OnlineReachabilityPreservers.OppositeIntersectionPruning
import Mathlib.Analysis.Real.Sqrt

/-! Upstream vertices of later branches give an incidence bound at half cutoff three. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private theorem same_later_branch_of_shared_upstream {n p k : ℕ} {paths : Fin p → List (Fin n)}
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    {i j j' : Fin p} (earlier : i < j) (earlier' : i < j') {x x' u : Fin n}
    (hit : x ∈ paths i) (hit' : x' ∈ paths i)
    (up : Before paths j u x) (up' : Before paths j' u x') : j = j' := by
  by_contra different
  by_cases equal : x = x'
  · subst x'
    exact no_parallel_list_steps free (by omega) different up up'
  rcases listBefore_total hit hit' equal with along | against
  · let bridge := threeListBridge earlier.ne' (fun equal => different equal.symm) earlier'.ne' up along up'
    exact free three bridge earlier'
  · let bridge := threeListBridge earlier'.ne' different earlier.ne' up' against up
    exact free three bridge earlier

private abbrev rowIncidences {n p : ℕ} (paths : Fin p → List (Fin n)) : Finset (Fin p × Fin n) :=
  univ.filter (fun v => v.2 ∈ paths v.1)

private theorem rowIncidences_card {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) : (rowIncidences paths).card = ∑ i, (paths i).length := by
  have count := card_eq_sum_card_fiberwise (s := rowIncidences paths) (t := (univ : Finset (Fin p)))
    (f := Prod.fst) (fun x _ => mem_univ x.1)
  rw [count]
  apply sum_congr rfl
  intro i _
  let withRow : Fin n ↪ Fin p × Fin n := ⟨Prod.mk i,fun _ _ equal => congrArg Prod.snd equal⟩
  have exactFiber : (rowIncidences paths).filter (fun x => x.1 = i) = (paths i).toFinset.map withRow := by
    ext x
    rcases x with ⟨j,v⟩
    simp only [rowIncidences,mem_filter,mem_univ,true_and,mem_map,List.mem_toFinset]
    constructor
    · rintro ⟨on,rfl⟩
      exact ⟨v,on,rfl⟩
    · rintro ⟨w,on,equal⟩
      change (i,w) = (j,v) at equal
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      exact ⟨on,rfl⟩
  rw [exactFiber,card_map,List.toFinset_card_of_nodup (simple i)]

private abbrev arrivalPredecessors {n p : ℕ} (paths : Fin p → List (Fin n)) (i : Fin p) (x : Fin n) :=
  predecessors (occurrences (fun i => (paths i).toFinset) x) i

private theorem mem_arrivalPredecessors {n p : ℕ} {paths : Fin p → List (Fin n)} {i j : Fin p} {x : Fin n} :
    j ∈ arrivalPredecessors paths i x ↔ x ∈ paths j ∧ j < i := by
  simp [arrivalPredecessors,predecessors,mem_occurrences]

private theorem small_row_position_count {n p : ℕ} (paths : Fin p → List (Fin n)) (L : ℕ) :
    ((rowIncidences paths).filter (fun v => (paths v.1).idxOf v.2 < L)).card ≤ p*L := by
  let S := (rowIncidences paths).filter (fun v => (paths v.1).idxOf v.2 < L)
  let rank (x : S) : Fin p × Fin L := (x.val.1,⟨(paths x.val.1).idxOf x.val.2,(mem_filter.mp x.property).2⟩)
  have injective : Function.Injective rank := by
    rintro ⟨⟨i,x⟩,hx⟩ ⟨⟨j,y⟩,hy⟩ equal
    obtain rfl : i = j := congrArg Prod.fst equal
    have on : x ∈ paths i := (mem_filter.mp (mem_filter.mp hx).1).2
    have idx : (paths i).idxOf x = (paths i).idxOf y := congrArg (fun a => a.2.val) equal
    obtain rfl := (List.idxOf_inj on).mp idx
    rfl
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective rank injective

private theorem small_arrival_rank_count {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ) :
    ((rowIncidences paths).filter (fun v => (arrivalPredecessors paths v.1 v.2).card < D)).card ≤ n*D := by
  let S := (rowIncidences paths).filter (fun v => (arrivalPredecessors paths v.1 v.2).card < D)
  let rank (x : S) : Fin n × Fin D := (x.val.2,⟨(arrivalPredecessors paths x.val.1 x.val.2).card,(mem_filter.mp x.property).2⟩)
  have injective : Function.Injective rank := by
    rintro ⟨⟨i,x⟩,hx⟩ ⟨⟨j,y⟩,hy⟩ equal
    obtain rfl : x = y := congrArg Prod.fst equal
    have hx' : i ∈ occurrences (fun a => (paths a).toFinset) x := by
      exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_filter.mp (mem_filter.mp hx).1).2)
    have hy' : j ∈ occurrences (fun a => (paths a).toFinset) x := by
      exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_filter.mp (mem_filter.mp hy).1).2)
    have idx : (arrivalPredecessors paths i x).card = (arrivalPredecessors paths j x).card :=
      congrArg (fun a => a.2.val) equal
    obtain rfl := predecessor_count_injective _ hx' hy' idx
    rfl
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective rank injective

private abbrev lateIncidences {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ) :=
  (rowIncidences paths).filter (fun v => D ≤ (arrivalPredecessors paths v.1 v.2).card ∧ L ≤ (paths v.1).idxOf v.2)

private theorem lateIncidences_card_lower {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (D L : ℕ) :
    (∑ i, (paths i).length) ≤ (lateIncidences paths D L).card+n*D+p*L := by
  let early := (rowIncidences paths).filter (fun v => (arrivalPredecessors paths v.1 v.2).card < D)
  let front := (rowIncidences paths).filter (fun v => (paths v.1).idxOf v.2 < L)
  let good := lateIncidences paths D L
  have cover : rowIncidences paths ⊆ (good ∪ early) ∪ front := by
    intro v on
    by_cases a : (arrivalPredecessors paths v.1 v.2).card < D
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨on,a⟩ : v ∈ early))
    by_cases b : (paths v.1).idxOf v.2 < L
    · exact mem_union_right _ (mem_filter.mpr ⟨on,b⟩ : v ∈ front)
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨on,le_of_not_gt a,le_of_not_gt b⟩ : v ∈ good))
  rw [← rowIncidences_card paths simple]
  calc
    _ ≤ ((good ∪ early) ∪ front).card := card_le_card cover
    _ ≤ (good ∪ early).card+front.card := card_union_le _ _
    _ ≤ (good.card+early.card)+front.card := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add_left (small_arrival_rank_count paths D) _) (small_row_position_count paths L)

private abbrev priorChoiceIncidences {n p : ℕ} (paths : Fin p → List (Fin n))
    (prior : Fin p × Fin n → Finset (Fin p)) (D L : ℕ) :=
  (rowIncidences paths).filter (fun v => D ≤ (prior v).card ∧ L ≤ (paths v.1).idxOf v.2)

private abbrev UpstreamBooking {n p : ℕ} (paths : Fin p → List (Fin n))
    (prior : Fin p × Fin n → Finset (Fin p)) :=
  Σ a : (rowIncidences paths), Fin (prior a.val).card × Fin ((paths a.val.1).idxOf a.val.2)

private noncomputable def bookingEarlier {n p : ℕ} (paths : Fin p → List (Fin n))
    (prior : Fin p × Fin n → Finset (Fin p)) (g : UpstreamBooking paths prior) : prior g.1.val :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm g.2.1

private def bookingVertex {n p : ℕ} (paths : Fin p → List (Fin n))
    (prior : Fin p × Fin n → Finset (Fin p)) (g : UpstreamBooking paths prior) : Fin n :=
  (paths g.1.val.1)[g.2.2.val]'(g.2.2.isLt.trans (List.idxOf_lt_length_of_mem (mem_filter.mp g.1.property).2))

private noncomputable def upstreamBookingImage {n p : ℕ} (paths : Fin p → List (Fin n))
    (prior : Fin p × Fin n → Finset (Fin p)) (g : UpstreamBooking paths prior) : Fin p × Fin n :=
  ((bookingEarlier paths prior g).val,bookingVertex paths prior g)

private theorem upstreamBookingImage_injective {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    (prior : Fin p × Fin n → Finset (Fin p))
    (earlierSpec : ∀ {i j x}, i ∈ prior (j,x) → x ∈ paths i ∧ i < j)
    (onlyHit : ∀ {i j x y}, x ∈ paths j → y ∈ paths j → i ∈ prior (j,x) → i ∈ prior (j,y) → x = y) :
    Function.Injective (upstreamBookingImage paths prior) := by
  have step (g : UpstreamBooking paths prior) : Before paths g.1.val.1 (bookingVertex paths prior g) g.1.val.2 := by
    refine ⟨List.getElem_mem _,(mem_filter.mp g.1.property).2,?_⟩
    dsimp only [bookingVertex]
    rw [(simple g.1.val.1).idxOf_getElem]
    exact g.2.2.isLt
  intro g h equal
  let earlier := (bookingEarlier paths prior g).val
  have sameBase : earlier = (bookingEarlier paths prior h).val := congrArg Prod.fst equal
  have sameUp : bookingVertex paths prior g = bookingVertex paths prior h := congrArg Prod.snd equal
  have onG : earlier ∈ prior (g.1.val.1,g.1.val.2) := (bookingEarlier paths prior g).property
  have onH : earlier ∈ prior (h.1.val.1,h.1.val.2) := sameBase.symm ▸ (bookingEarlier paths prior h).property
  obtain ⟨hitG,oldG⟩ := earlierSpec onG
  obtain ⟨hitH,oldH⟩ := earlierSpec onH
  have branch : g.1.val.1 = h.1.val.1 := same_later_branch_of_shared_upstream free three oldG oldH
    hitG hitH (step g) (sameUp.symm ▸ step h)
  have corner : g.1.val.2 = h.1.val.2 := onlyHit (step g).2.1 (branch.symm ▸ (step h).2.1) onG (branch.symm ▸ onH)
  have source : g.1 = h.1 := Subtype.ext (Prod.ext branch corner)
  rcases g with ⟨g,d,l⟩
  rcases h with ⟨h,e,m⟩
  change g = h at source
  subst h
  have ranks : d = e := (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm.injective (Subtype.ext sameBase)
  have samePosition := congrArg (paths g.val.1).idxOf sameUp
  dsimp only [bookingVertex] at samePosition
  rw [(simple g.val.1).idxOf_getElem,(simple g.val.1).idxOf_getElem] at samePosition
  have offsets : l = m := Fin.ext samePosition
  exact congrArg (Sigma.mk g) (Prod.ext ranks offsets)

private abbrev tripleSelections (S : ℕ) := (univ : Finset (Fin (S+2))).powersetCard 3

private noncomputable def sortedTripleSelection {S : ℕ} (selection : tripleSelections S) : Fin 3 ≃o (↥selection.val) :=
  Fintype.orderIsoFinOfCardEq _ ((Fintype.card_coe _).trans (mem_powersetCard.mp selection.property).2)

private noncomputable def triplePositions {S : ℕ} (selection : tripleSelections S) (j : Fin 3) : ℕ :=
  ((sortedTripleSelection selection j).val).val

private theorem triplePositions_strictMono {S : ℕ} (selection : tripleSelections S) :
    StrictMono (triplePositions selection) := fun _ _ h => (sortedTripleSelection selection).strictMono h

private noncomputable def tripleGaps {S : ℕ} (selection : tripleSelections S) : ℕ × ℕ × ℕ :=
  let x := triplePositions selection 0
  let y := triplePositions selection 1
  let z := triplePositions selection 2
  (x,y-x-1,z-y-1)

private theorem tripleGaps_sum_lt {S : ℕ} (selection : tripleSelections S) :
    (tripleGaps selection).1+(tripleGaps selection).2.1+(tripleGaps selection).2.2 < S := by
  have xy := triplePositions_strictMono selection (by decide : (0:Fin 3) < 1)
  have yz := triplePositions_strictMono selection (by decide : (1:Fin 3) < 2)
  have zBound : triplePositions selection 2 < S+2 := (sortedTripleSelection selection 2).val.isLt
  dsimp only [tripleGaps]
  omega

private theorem tripleGaps_injective (S : ℕ) : Function.Injective (tripleGaps (S := S)) := by
  intro a b equal
  have first : triplePositions a 0 = triplePositions b 0 := congrArg Prod.fst equal
  have second : triplePositions a 1-triplePositions a 0-1 = triplePositions b 1-triplePositions b 0-1 :=
    congrArg (fun u => u.2.1) equal
  have third : triplePositions a 2-triplePositions a 1-1 = triplePositions b 2-triplePositions b 1-1 :=
    congrArg (fun u => u.2.2) equal
  have a01 := triplePositions_strictMono a (by decide : (0:Fin 3) < 1)
  have a12 := triplePositions_strictMono a (by decide : (1:Fin 3) < 2)
  have b01 := triplePositions_strictMono b (by decide : (0:Fin 3) < 1)
  have b12 := triplePositions_strictMono b (by decide : (1:Fin 3) < 2)
  have aligned (i : Fin 3) : (sortedTripleSelection a i).val = (sortedTripleSelection b i).val := by
    apply Fin.ext
    fin_cases i
    · exact first
    · change triplePositions a 1 = triplePositions b 1
      omega
    · change triplePositions a 2 = triplePositions b 2
      omega
  apply Subtype.ext
  apply Finset.ext
  intro v
  constructor
  · intro on
    let i := (sortedTripleSelection a).symm ⟨v,on⟩
    have aAt : (sortedTripleSelection a i).val = v := congrArg Subtype.val ((sortedTripleSelection a).apply_symm_apply ⟨v,on⟩)
    rw [← aAt,aligned]
    exact (sortedTripleSelection b i).property
  · intro on
    let i := (sortedTripleSelection b).symm ⟨v,on⟩
    have bAt : (sortedTripleSelection b i).val = v := congrArg Subtype.val ((sortedTripleSelection b).apply_symm_apply ⟨v,on⟩)
    rw [← bAt,← aligned]
    exact (sortedTripleSelection a i).property

private theorem mass_cube_le_six_times_choose (S : ℕ) : S^3 ≤ 6*(S+2).choose 3 := by
  calc
    _ ≤ (S+2)*(S+1)*S := by
      rw [pow_succ,pow_two]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    _ = S.ascFactorial 3 := by simp [Nat.ascFactorial_succ,Nat.mul_assoc]
    _ = _ := by rw [Nat.ascFactorial_eq_factorial_mul_choose',show S+3-1 = S+2 by omega]; norm_num [Nat.factorial]

private theorem upstream_mass_shift_cube_of_prior_counts {n p k : ℕ}
    (hn : 0 < n) (hp : 0 < p) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    (prior : Fin p × Fin n → Finset (Fin p))
    (earlierSpec : ∀ {i j x}, i ∈ prior (j,x) → x ∈ paths i ∧ i < j)
    (onlyHit : ∀ {i j x y}, x ∈ paths j → y ∈ paths j → i ∈ prior (j,x) → i ∈ prior (j,y) → x = y)
    (M : ℕ) (coverage : ∀ D L, M ≤ (priorChoiceIncidences paths prior D L).card+n*D+p*L) :
    (M-(n+p))^3 ≤ 6*(n*p)^2 := by
  classical
  let S := M-(n+p)
  by_cases empty : S = 0
  · change S^3 ≤ _
    simp [empty]
  have total : S+n+p = M := by dsimp only [S] at empty ⊢; omega
  let A (z : tripleSelections S) := (tripleGaps z).1
  let B (z : tripleSelections S) := (tripleGaps z).2.1
  let C (z : tripleSelections S) := (tripleGaps z).2.2
  let D (z : tripleSelections S) := A z/n+1
  let L (z : tripleSelections S) := B z/p+1
  have validIndex (z : tripleSelections S) : C z < (priorChoiceIncidences paths prior (D z) (L z)).card := by
    have small : A z+B z+C z < S := tripleGaps_sum_lt z
    have priceD : n*D z ≤ A z+n := by
      dsimp only [D]
      rw [Nat.mul_add,Nat.mul_one]
      exact Nat.add_le_add_right (Nat.mul_div_le _ _) _
    have priceL : p*L z ≤ B z+p := by
      dsimp only [L]
      rw [Nat.mul_add,Nat.mul_one]
      exact Nat.add_le_add_right (Nat.mul_div_le _ _) _
    have cover : M ≤ (priorChoiceIncidences paths prior (D z) (L z)).card+n*D z+p*L z :=
      coverage (D z) (L z)
    omega
  let pick (d l : ℕ) : (Fin (priorChoiceIncidences paths prior d l).card) ≃ (↥(priorChoiceIncidences paths prior d l)) :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm
  let chosen (z : tripleSelections S) := pick (D z) (L z) ⟨C z,validIndex z⟩
  let source (z : tripleSelections S) : rowIncidences paths := ⟨(chosen z).val,(mem_filter.mp (chosen z).property).1⟩
  let book (z : tripleSelections S) : UpstreamBooking paths prior :=
    ⟨source z,⟨A z/n,(mem_filter.mp (chosen z).property).2.1⟩,
      ⟨B z/p,(mem_filter.mp (chosen z).property).2.2⟩⟩
  let Image (z : tripleSelections S) : (Fin p × Fin n) × Fin n × Fin p :=
    (upstreamBookingImage paths prior (book z),⟨A z%n,Nat.mod_lt _ hn⟩,⟨B z%p,Nat.mod_lt _ hp⟩)
  have pickInjective {d₁ l₁ d₂ l₂ : ℕ} {c₁ : Fin (priorChoiceIncidences paths prior d₁ l₁).card}
      {c₂ : Fin (priorChoiceIncidences paths prior d₂ l₂).card} (hs : d₁ = d₂) (ht : l₁ = l₂)
      (same : (pick d₁ l₁ c₁).val = (pick d₂ l₂ c₂).val) : c₁.val = c₂.val := by
    subst d₂
    subst l₂
    exact congrArg Fin.val ((pick d₁ l₁).injective (Subtype.ext same))
  have injective : Function.Injective Image := by
    intro z w equal
    have distinctBookings := upstreamBookingImage_injective paths simple free three prior (fun {_ _ _} => earlierSpec)
      (fun {_ _ _ _} => onlyHit)
    have same : book z = book w := distinctBookings (congrArg Prod.fst equal)
    have sources : (chosen z).val = (chosen w).val := congrArg (fun g : UpstreamBooking paths prior => g.fst.val) same
    have quotientA : A z/n = A w/n := congrArg (fun g : UpstreamBooking paths prior => g.snd.1.val) same
    have quotientB : B z/p = B w/p := congrArg (fun g : UpstreamBooking paths prior => g.snd.2.val) same
    have remainderA : A z%n = A w%n := congrArg (fun v => v.2.1.val) equal
    have remainderB : B z%p = B w%p := congrArg (fun v => v.2.2.val) equal
    have eqA : A z = A w := calc
      _ = A z%n+n*(A z/n) := (Nat.mod_add_div _ _).symm
      _ = A w%n+n*(A w/n) := by rw [quotientA,remainderA]
      _ = _ := Nat.mod_add_div _ _
    have eqB : B z = B w := calc
      _ = B z%p+p*(B z/p) := (Nat.mod_add_div _ _).symm
      _ = B w%p+p*(B w/p) := by rw [quotientB,remainderB]
      _ = _ := Nat.mod_add_div _ _
    have eqC : C z = C w := pickInjective (congrArg (·+1) quotientA) (congrArg (·+1) quotientB) sources
    exact tripleGaps_injective S (Prod.ext eqA (Prod.ext eqB eqC))
  have triangleCount : (S+2).choose 3 ≤ (p*n)*(n*p) := by
    simpa only [Fintype.card_coe,card_powersetCard,card_univ,Fintype.card_fin,Fintype.card_prod] using
      Fintype.card_le_of_injective Image injective
  change S^3 ≤ _
  calc
    _ ≤ 6*(S+2).choose 3 := mass_cube_le_six_times_choose S
    _ ≤ 6*((p*n)*(n*p)) := Nat.mul_le_mul_left _ triangleCount
    _ = _ := by ring

private theorem unique_intersection_half_three_shifted_mass_cube_le {n p k : ℕ}
    (hn : 0 < n) (hp : 0 < p) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y) :
    ((∑ i, (paths i).length)-(n+p))^3 ≤ 6*(n*p)^2 := by
  let prior (g : Fin p × Fin n) := arrivalPredecessors paths g.1 g.2
  refine upstream_mass_shift_cube_of_prior_counts hn hp paths simple free three prior
    (fun {_ _ _} on => mem_arrivalPredecessors.mp on) ?_ _ (lateIncidences_card_lower paths simple)
  intro i j x y xj yj xi yi
  obtain ⟨onX,earlier⟩ := mem_arrivalPredecessors.mp xi
  exact unique earlier.ne onX xj (mem_arrivalPredecessors.mp yi).1 yj

/-- A simultaneous count of all earlier-row and upstream-vertex choices
sharpens the half-three cube bound, with an explicit shift for the two
budgets. This holds with the same constants for every larger cutoff. -/
theorem half_three_shifted_mass_cube_le {n p k : ℕ} (hn : 0 < n) (hp : 0 < p)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) :
    ((∑ i, (paths i).length)-2*(n+p))^3 ≤ 48*(n*p)^2 := by
  let clean := removeOppositeIntersections paths
  let W := ∑ i, (clean i).length
  have retention : (∑ i, (paths i).length) ≤ 2*W := removeOppositeIntersections_mass simple free three
  have square := unique_intersection_half_three_shifted_mass_cube_le hn hp clean
    (fun i => (removeOppositeIntersections_sublist paths i).nodup (simple i))
    (removeOppositeIntersections_halfFree simple free) three
    (fun {_ _ _ _} apart xa xb ya yb => removeOppositeIntersections_unique simple free (by omega) apart xa xb ya yb)
  change (W-(n+p))^3 ≤ 6*(n*p)^2 at square
  have lower : (∑ i, (paths i).length)-2*(n+p) ≤ 2*(W-(n+p)) := by omega
  calc
    _ ≤ (2*(W-(n+p)))^3 := Nat.pow_le_pow_left lower 3
    _ = 8*(W-(n+p))^3 := by ring
    _ ≤ 8*(6*(n*p)^2) := Nat.mul_le_mul_left _ square
    _ = _ := by ring


/-- A simple half-three-free family has either at most `8(n+p)` mass
or mass with cube at most `1024 (np)^2`. Every larger half cutoff inherits
the bound. No regularity hypothesis on the input is needed. -/
theorem half_three_mass_cubic_or_linear {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) :
    let M := ∑ i, (paths i).length
    M ≤ 8*(n+p) ∨ M^3 ≤ 1024*(n*p)^2 := by
  let M := ∑ i, (paths i).length
  by_cases small : M ≤ 8*(n+p)
  · exact Or.inl small
  apply Or.inr
  have hn : 0 < n := by
    by_contra! zero
    have nil (i : Fin p) : paths i = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun v _ => (Nat.not_lt_of_ge zero) ((Nat.zero_le v.val).trans_lt v.isLt))
    simp [M,nil] at small
  have hp : 0 < p := by
    by_contra! zero
    have pZero : p = 0 := by omega
    have none : IsEmpty (Fin p) := pZero ▸ (inferInstance : IsEmpty (Fin 0))
    simp [M,Finset.univ_eq_empty] at small
  have upper := half_three_shifted_mass_cube_le hn hp paths simple free three
  change (M-2*(n+p))^3 ≤ 48*(n*p)^2 at upper
  have compare : M ≤ 2*(M-2*(n+p)) := by omega
  change M^3 ≤ _
  calc
    _ ≤ (2*(M-2*(n+p)))^3 := Nat.pow_le_pow_left compare 3
    _ = 8*(M-2*(n+p))^3 := by ring
    _ ≤ 8*(48*(n*p)^2) := Nat.mul_le_mul_left _ upper
    _ ≤ _ := by omega

/-- At unbounded path budgets, half-three mass of order `n √p` requires
a positive quadratic path density. The constants depend only on the
mass fraction, so the statement also applies at every larger cutoff. -/
theorem half_three_n_sqrt_p_mass_requires_quadratic_path_density (η : ℝ) (positive : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 0 < P ∧ ∀ {n p k : ℕ}, 0 < n → P ≤ p → 3 ≤ k →
      ∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) k →
      η*(n:ℝ)*Real.sqrt p ≤ ((∑ i, (paths i).length : ℕ):ℝ) → δ*(n:ℝ)^2 ≤ p := by
  let t := min (η/16) (η^3/1024)
  have tPos : 0 < t := lt_min (by positivity) (by positivity)
  refine ⟨t^2,by positivity,⌈(16/η)^2⌉₊+1,by positivity,?_⟩
  intro n p k hn large three paths simple free dense
  let y := Real.sqrt (p:ℝ)
  have pPos : 0 < p := by omega
  have yPos : 0 < y := Real.sqrt_pos.mpr (Nat.cast_pos.mpr pPos)
  have nPos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have square : y^2 = (p:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have rootBound : t*(n:ℝ) ≤ y := by
    rcases half_three_mass_cubic_or_linear paths simple free three with linear | cube
    · have threshold : (16/η)^2 ≤ (p:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
      have base : 16/η ≤ y := (sq_le_sq₀ (by positivity) yPos.le).mp (square ▸ threshold)
      have scaleN : (16:ℝ) ≤ η*y := by simpa only [mul_comm] using (div_le_iff₀ positive).mp base
      have costN : (8:ℝ)*n ≤ (η/2)*(n:ℝ)*y := by
        have price := mul_le_mul_of_nonneg_right scaleN nPos.le
        linarith only [price]
      by_contra! sparse
      have smallP : y < (η/16)*(n:ℝ) := sparse.trans_le
        (mul_le_mul_of_nonneg_right (min_le_left _ _) nPos.le)
      have costP : (8:ℝ)*p < (η/2)*(n:ℝ)*y := by
        have price := mul_lt_mul_of_pos_right smallP yPos
        rw [← square]
        linarith only [price]
      have mass : ((∑ i, (paths i).length : ℕ):ℝ) ≤ 8*((n:ℝ)+p) := by exact_mod_cast linear
      linarith only [mass,dense,costN,costP]
    · have cap : ((∑ i, (paths i).length : ℕ):ℝ)^3 ≤ 1024*((n:ℝ)*p)^2 := by exact_mod_cast cube
      have product : (η^3*(n:ℝ))*((n:ℝ)^2*y^3) ≤ (1024*y)*((n:ℝ)^2*y^3) := calc
        _ = (η*(n:ℝ)*y)^3 := by ring
        _ ≤ ((∑ i, (paths i).length : ℕ):ℝ)^3 := pow_le_pow_left₀ (by positivity) dense 3
        _ ≤ 1024*((n:ℝ)*p)^2 := cap
        _ = 1024*((n:ℝ)*y^2)^2 := by rw [square]
        _ = _ := by ring
      have scale : η^3*(n:ℝ) ≤ 1024*y := le_of_mul_le_mul_right product (by positivity)
      calc
        _ ≤ (η^3/1024)*(n:ℝ) := mul_le_mul_of_nonneg_right (min_le_right _ _) nPos.le
        _ ≤ y := by linarith only [scale]
  calc
    _ = (t*(n:ℝ))^2 := by ring
    _ ≤ y^2 := pow_le_pow_left₀ (by positivity) rootBound 2
    _ = _ := square

private noncomputable def latestPriorRows {n p : ℕ} (paths : Fin p → List (Fin n))
    (g : Fin p × Fin n) : Finset (Fin p) := by
  classical
  exact (arrivalPredecessors paths g.1 g.2).filter (fun i => ∀ y, Before paths g.1 g.2 y → y ∉ paths i)

private theorem mem_latestPriorRows {n p : ℕ} {paths : Fin p → List (Fin n)} {i j : Fin p} {x : Fin n} :
    i ∈ latestPriorRows paths (j,x) ↔ i ∈ arrivalPredecessors paths j x ∧
      ∀ y, Before paths j x y → y ∉ paths i := by
  classical
  simp [latestPriorRows]

private noncomputable def skippedPriorRows {n p : ℕ} (paths : Fin p → List (Fin n))
    (g : Fin p × Fin n) : Finset (Fin p) :=
  arrivalPredecessors paths g.1 g.2 \ latestPriorRows paths g

private theorem skippedPriorRows_witness {n p : ℕ} {paths : Fin p → List (Fin n)} {i j : Fin p} {x : Fin n}
    (skip : i ∈ skippedPriorRows paths (j,x)) : x ∈ paths i ∧ i < j ∧ ∃ y ∈ paths i, Before paths j x y := by
  classical
  obtain ⟨earlier,notLatest⟩ := mem_sdiff.mp skip
  obtain ⟨shared,position⟩ := mem_arrivalPredecessors.mp earlier
  refine ⟨shared,position,?_⟩
  by_contra absent
  exact notLatest (mem_latestPriorRows.mpr ⟨earlier,fun y later on => absent ⟨y,on,later⟩⟩)

private theorem latestPriorRows_unique_hit {n p : ℕ} {paths : Fin p → List (Fin n)} {i j : Fin p} {x y : Fin n}
    (xj : x ∈ paths j) (yj : y ∈ paths j) (xLast : i ∈ latestPriorRows paths (j,x))
    (yLast : i ∈ latestPriorRows paths (j,y)) : x = y := by
  by_contra different
  obtain ⟨xEarlier,xLatest⟩ := mem_latestPriorRows.mp xLast
  obtain ⟨yEarlier,yLatest⟩ := mem_latestPriorRows.mp yLast
  rcases listBefore_total xj yj different with forward | backward
  · exact xLatest y forward (mem_arrivalPredecessors.mp yEarlier).1
  · exact yLatest x backward (mem_arrivalPredecessors.mp xEarlier).1

private theorem skippedPriorRows_total_le_mass {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) :
    (∑ g ∈ rowIncidences paths, (skippedPriorRows paths g).card) ≤ ∑ i, (paths i).length := by
  classical
  let R := rowIncidences paths
  let Lost := Σ g : ↥R, ↥(skippedPriorRows paths g.val)
  let charge (a : Lost) : R :=
    ⟨(a.snd.val,a.fst.val.2),mem_filter.mpr ⟨mem_univ _,(skippedPriorRows_witness a.snd.property).1⟩⟩
  have injective : Function.Injective charge := by
    rintro ⟨g,a⟩ ⟨h,b⟩ equal
    have projected := congrArg (@Subtype.val (Fin p × Fin n) (· ∈ R)) equal
    change (a.val,g.val.2) = (b.val,h.val.2) at projected
    obtain ⟨sameBase,sameVertex⟩ := Prod.mk.inj projected
    obtain ⟨_,ag,x,hitA,upA⟩ := skippedPriorRows_witness a.property
    obtain ⟨_,bh,y,hitB,upB⟩ := skippedPriorRows_witness b.property
    have sameBranch : g.val.1 = h.val.1 := same_later_branch_of_shared_upstream free three ag
      (sameBase.symm ▸ bh) hitA (sameBase.symm ▸ hitB) upA (sameVertex.symm ▸ upB)
    have same : g = h := Subtype.ext (Prod.ext sameBranch sameVertex)
    subst h
    exact congrArg (Sigma.mk g) (Subtype.ext sameBase)
  have count : Fintype.card Lost = ∑ g ∈ R, (skippedPriorRows paths g).card := by
    change Fintype.card (Σ g : ↥R, ↥(skippedPriorRows paths g.val)) = _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    exact R.sum_coe_sort (fun g : Fin p × Fin n => (skippedPriorRows paths g).card)
  have slots := Fintype.card_le_of_injective charge injective
  rwa [count,Fintype.card_coe,rowIncidences_card paths simple] at slots

private theorem latestPriorRows_count_add_skipped {n p : ℕ} (paths : Fin p → List (Fin n)) (g : Fin p × Fin n) :
    (arrivalPredecessors paths g.1 g.2).card = (latestPriorRows paths g).card+(skippedPriorRows paths g).card := by
  classical
  have subset : latestPriorRows paths g ⊆ arrivalPredecessors paths g.1 g.2 := by
    rcases g with ⟨j,x⟩
    exact fun _ on => (mem_latestPriorRows.mp on).1
  have size := card_le_card subset
  rw [skippedPriorRows,card_sdiff_of_subset subset]
  omega

private theorem latest_prior_choice_counts {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) (T D L : ℕ) :
    let M := ∑ i, (paths i).length
    M-(M/(T+1)+n*T) ≤ (priorChoiceIncidences paths (latestPriorRows paths) D L).card+n*D+p*L := by
  classical
  let M := ∑ i, (paths i).length
  let R := rowIncidences paths
  let largeLoss := R.filter (fun g => T < (skippedPriorRows paths g).card)
  let early := R.filter (fun g => (arrivalPredecessors paths g.1 g.2).card < D+T)
  let front := R.filter (fun g => (paths g.1).idxOf g.2 < L)
  let good := priorChoiceIncidences paths (latestPriorRows paths) D L
  have lossBudget : largeLoss.card*(T+1) ≤ M := calc
    _ = ∑ _ ∈ largeLoss, (T+1) := by simp
    _ ≤ ∑ g ∈ largeLoss, (skippedPriorRows paths g).card := sum_le_sum fun _ hit => (mem_filter.mp hit).2
    _ ≤ ∑ g ∈ R, (skippedPriorRows paths g).card := sum_le_sum_of_subset (filter_subset _ _)
    _ ≤ _ := skippedPriorRows_total_le_mass paths simple free three
  have lossCount : largeLoss.card ≤ M/(T+1) := (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr lossBudget
  have cover : R ⊆ ((good ∪ early) ∪ front) ∪ largeLoss := by
    intro g on
    by_cases worst : T < (skippedPriorRows paths g).card
    · exact mem_union_right _ (mem_filter.mpr ⟨on,worst⟩ : g ∈ largeLoss)
    by_cases lowIndex : (paths g.1).idxOf g.2 < L
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨on,lowIndex⟩ : g ∈ front))
    by_cases late : (arrivalPredecessors paths g.1 g.2).card < D+T
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨on,late⟩ : g ∈ early)))
    have enough : D ≤ (latestPriorRows paths g).card := by
      have derived := latestPriorRows_count_add_skipped paths g
      omega
    exact mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_filter.mpr ⟨on,enough,le_of_not_gt lowIndex⟩ : g ∈ good)))
  have price₁ : (good ∪ early).card ≤ good.card+n*(D+T) := (card_union_le _ _).trans
    (Nat.add_le_add_left (small_arrival_rank_count paths (D+T)) _)
  have price₂ : ((good ∪ early) ∪ front).card ≤ good.card+n*(D+T)+p*L := (card_union_le _ _).trans
    (Nat.add_le_add price₁ (small_row_position_count paths L))
  have charge : M ≤ good.card+n*(D+T)+p*L+M/(T+1) := calc
    M = R.card := (rowIncidences_card paths simple).symm
    _ ≤ (((good ∪ early) ∪ front) ∪ largeLoss).card := card_le_card cover
    _ ≤ _ := (card_union_le _ _).trans (Nat.add_le_add price₂ lossCount)
  rw [Nat.mul_add] at charge
  change M-(M/(T+1)+n*T) ≤ good.card+n*D+p*L
  omega

/-- Choosing the latest shared vertex for each earlier row removes the
need to discard whole incidences. At most one skipped earlier-row choice
is charged to any earlier incidence. `T` sets the allowable local loss. -/
theorem half_three_latest_intersection_shifted_mass_cube_le {n p k : ℕ} (hn : 0 < n) (hp : 0 < p)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) (T : ℕ) :
    let M := ∑ i, (paths i).length
    (M-M/(T+1)-((T+1)*n+p))^3 ≤ 6*(n*p)^2 := by
  let M := ∑ i, (paths i).length
  let K := M-(M/(T+1)+n*T)
  have bound := upstream_mass_shift_cube_of_prior_counts hn hp paths simple free three
    (latestPriorRows paths) (fun {_ _ _} on => mem_arrivalPredecessors.mp (mem_latestPriorRows.mp on).1)
    (fun {_ _ _ _} => latestPriorRows_unique_hit) K (latest_prior_choice_counts paths simple free three T)
  have shifted : K-(n+p) = M-M/(T+1)-((T+1)*n+p) := by
    dsimp only [K]
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm T n]
    omega
  rw [shifted] at bound
  exact bound

end OnlineReachabilityPreservers
