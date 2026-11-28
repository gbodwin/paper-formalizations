import OnlineReachabilityPreservers.SaturatedLiteralFullFourLower
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-! Sharp mass comparison at full cutoff four and the saturated literal half budget. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- The simple graph joining vertices if either orientation is present. -/
def arcShadow {V : Type*} [DecidableEq V] (arcs : Finset (V × V))
    (loopless : ∀ x, (x,x) ∉ arcs) : SimpleGraph V where
  Adj x y := (x,y) ∈ arcs ∨ (y,x) ∈ arcs
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun x h => loopless x (h.elim id id)⟩

/-- The simple graph joining vertices if both orientations are present. -/
def reciprocalGraph {V : Type*} [DecidableEq V] (arcs : Finset (V × V))
    (loopless : ∀ x, (x,x) ∉ arcs) : SimpleGraph V where
  Adj x y := (x,y) ∈ arcs ∧ (y,x) ∈ arcs
  symm := ⟨fun _ _ => And.symm⟩
  loopless := ⟨fun x h => loopless x h.1⟩

instance {V : Type*} [DecidableEq V] {arcs : Finset (V × V)}
    {loopless : ∀ x, (x,x) ∉ arcs} : DecidableRel (arcShadow arcs loopless).Adj :=
  fun x y => inferInstanceAs (Decidable ((x,y) ∈ arcs ∨ (y,x) ∈ arcs))

instance {V : Type*} [DecidableEq V] {arcs : Finset (V × V)}
    {loopless : ∀ x, (x,x) ∉ arcs} : DecidableRel (reciprocalGraph arcs loopless).Adj :=
  fun x y => inferInstanceAs (Decidable ((x,y) ∈ arcs ∧ (y,x) ∈ arcs))

private theorem arcShadow_cliqueFree_four {V : Type*} [DecidableEq V]
    (arcs : Finset (V × V)) (loopless : ∀ x, (x,x) ∉ arcs)
    (noTriangle : ∀ {x y z}, (x,y) ∈ arcs → (y,z) ∈ arcs → (x,z) ∉ arcs) :
    (arcShadow arcs loopless).CliqueFree 4 := by
  intro s clique
  let label (i : Fin 4) : V := ((s.equivFinOfCardEq clique.card_eq).symm i).val
  have distinct : Function.Injective label := Subtype.val_injective.comp
    (s.equivFinOfCardEq clique.card_eq).symm.injective
  have adj {i j : Fin 4} (ne : i ≠ j) :
      (label i,label j) ∈ arcs ∨ (label j,label i) ∈ arcs :=
    clique.isClique
      ((s.equivFinOfCardEq clique.card_eq).symm i).property
      ((s.equivFinOfCardEq clique.card_eq).symm j).property (distinct.ne ne)
  have twoOut {i j : Fin 4} (ne : i ≠ j) (first : (label 0,label i) ∈ arcs)
      (second : (label 0,label j) ∈ arcs) : False := by
    rcases adj ne with forward | backward
    · exact noTriangle first forward second
    · exact noTriangle second backward first
  have twoIn {i j : Fin 4} (ne : i ≠ j) (first : (label i,label 0) ∈ arcs)
      (second : (label j,label 0) ∈ arcs) : False := by
    rcases adj ne with forward | backward
    · exact noTriangle forward second first
    · exact noTriangle backward first second
  rcases adj (by decide : (0 : Fin 4) ≠ 1) with one | one <;>
    rcases adj (by decide : (0 : Fin 4) ≠ 2) with two | two
  · exact twoOut (by decide : (1 : Fin 4) ≠ 2) one two
  · rcases adj (by decide : (0 : Fin 4) ≠ 3) with three | three
    · exact twoOut (by decide : (1 : Fin 4) ≠ 3) one three
    · exact twoIn (by decide : (2 : Fin 4) ≠ 3) two three
  · rcases adj (by decide : (0 : Fin 4) ≠ 3) with three | three
    · exact twoOut (by decide : (2 : Fin 4) ≠ 3) two three
    · exact twoIn (by decide : (1 : Fin 4) ≠ 3) one three
  · exact twoIn (by decide : (1 : Fin 4) ≠ 2) one two

/-- In addition to one arc per shadow edge, an edge with both orientations contributes one more arc. -/
theorem arcs_card_le_shadow_add_reciprocal {V : Type*} [Fintype V] [LinearOrder V]
    (arcs : Finset (V × V)) (loopless : ∀ x, (x,x) ∉ arcs) :
    arcs.card ≤ (arcShadow arcs loopless).edgeFinset.card+(reciprocalGraph arcs loopless).edgeFinset.card := by
  classical
  let keep (e : V × V) := e.swap ∉ arcs ∨ e.1 < e.2
  let first := arcs.filter keep
  let second := arcs.filter fun e => ¬ keep e
  let unlabeled (e : V × V) : Sym2 V := s(e.1,e.2)
  have firstCard : first.card ≤ (arcShadow arcs loopless).edgeFinset.card := by
    apply card_le_card_of_injOn unlabeled
    · intro e member
      have on := (mem_filter.mp member).1
      exact SimpleGraph.mem_edgeFinset.mpr (Or.inl on)
    · intro e eIn f fIn equal
      rcases Sym2.mk_eq_mk_iff.mp equal with same | swap
      · exact same
      · have fIn' := mem_filter.mp fIn
        subst e
        have eIn' := mem_filter.mp eIn
        rcases eIn'.2 with no | reverse
        · exact (no (by simpa using fIn'.1)).elim
        · rcases fIn'.2 with no | forward
          · exact (no eIn'.1).elim
          · exact (lt_asymm reverse forward).elim
  have secondCard : second.card ≤ (reciprocalGraph arcs loopless).edgeFinset.card := by
    apply card_le_card_of_injOn unlabeled
    · intro e member
      obtain ⟨on,drop⟩ := mem_filter.mp member
      exact SimpleGraph.mem_edgeFinset.mpr
        ⟨on,by by_contra no; exact drop (Or.inl no)⟩
    · intro e eIn f fIn equal
      rcases Sym2.mk_eq_mk_iff.mp equal with same | swap
      · exact same
      · have fIn' := mem_filter.mp fIn
        subst e
        have eIn' := mem_filter.mp eIn
        have order₁ : ¬ f.2 < f.1 := fun h => eIn'.2 (Or.inr h)
        have order₂ : ¬ f.1 < f.2 := fun h => fIn'.2 (Or.inr h)
        have same := le_antisymm (le_of_not_gt order₁) (le_of_not_gt order₂)
        have on : (f.1,f.2) ∈ arcs := fIn'.1
        rw [← same] at on
        exact (loopless f.1 on).elim
  have split : first.card+second.card = arcs.card := card_filter_add_card_filter_not keep
  omega

private theorem graph_edge_square_le_of_unique_common_neighbor {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (one : ∀ {x z a b : V}, x ≠ z → G.Adj a x → G.Adj a z → G.Adj b x → G.Adj b z → a = b) :
    (2*G.edgeFinset.card)^2 ≤ 2*(Fintype.card V)^3 := by
  let n := Fintype.card V
  let pairs (v : V) := (G.neighborFinset v).offDiag
  have disjoint : (↑(univ : Finset V) : Set V).PairwiseDisjoint pairs := by
    intro v _ w _ apart
    apply disjoint_left.mpr
    intro e first second
    obtain ⟨vx,vz,xz⟩ := mem_offDiag.mp first
    obtain ⟨wx,wz,_⟩ := mem_offDiag.mp second
    exact apart (one xz ((G.mem_neighborFinset _ _).mp vx) ((G.mem_neighborFinset _ _).mp vz)
      ((G.mem_neighborFinset _ _).mp wx) ((G.mem_neighborFinset _ _).mp wz))
  have covers : (univ : Finset V).biUnion pairs ⊆ (univ : Finset V).offDiag := by
    intro e member
    obtain ⟨_,_,on⟩ := mem_biUnion.mp member
    exact mem_offDiag.mpr ⟨mem_univ _,mem_univ _,(mem_offDiag.mp on).2.2⟩
  have pairBound : (∑ v, (pairs v).card) ≤ n*n := by
    have size := card_le_card covers
    rw [card_biUnion disjoint,offDiag_card,card_univ] at size
    exact size.trans (Nat.sub_le _ _)
  have total : (∑ v, G.degree v) ≤ n*n := calc
    _ ≤ ∑ _ : V, n := sum_le_sum fun v _ => card_le_univ (G.neighborFinset v)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,n]
  have split : (∑ v, (G.degree v)^2) = (∑ v, (pairs v).card)+(∑ v, G.degree v) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    change (G.degree v)^2 = (G.neighborFinset v).offDiag.card+G.degree v
    rw [offDiag_card,G.card_neighborFinset_eq_degree,pow_two,
      Nat.sub_add_cancel (Nat.le_mul_self _)]
  have sumSquares : (∑ v, (G.degree v)^2) ≤ 2*(n*n) := by omega
  have cauchy : (2*G.edgeFinset.card)^2 ≤ n*(∑ v, (G.degree v)^2) := by
    simpa only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,
      G.sum_degrees_eq_twice_card_edges,n] using
      (sum_mul_sq_le_sq_mul_sq (R := ℕ) (univ : Finset V) (fun _ => 1) (fun v => G.degree v))
  calc
    _ ≤ n*(∑ v, (G.degree v)^2) := cauchy
    _ ≤ n*(2*(n*n)) := Nat.mul_le_mul_left n sumSquares
    _ = _ := by change n*(2*(n*n)) = 2*n^3; ring

/-- A detour and shortcut with distinct vertices and injective arc owners give a full bridge. -/
theorem no_detour_of_distinct_arc_owners {V I : Type*} [DecidableEq V]
    {rows : I → List V} {cutoff s : ℕ} (full : BridgeFree (Before rows) cutoff)
    (fits : s+2 ≤ cutoff) (multiple : 0 < s) {arcs : Finset (V × V)}
    (owner : arcs → I) (unique : Function.Injective owner)
    (compares : ∀ edge : arcs, Before rows (owner edge) edge.val.1 edge.val.2)
    (vertices : Fin (s+2) → V) (distinct : Function.Injective vertices)
    (chain : ∀ i : Fin (s+1), (vertices i.castSucc,vertices i.succ) ∈ arcs)
    (shortcut : (vertices 0,vertices (Fin.last (s+1))) ∈ arcs) : False := by
  let arc (i : Fin (s+1)) : arcs := ⟨_,chain i⟩
  let river : arcs := ⟨_,shortcut⟩
  have arcInjective : Function.Injective arc := by
    intro i j equal
    have first := congrArg (fun e : arcs => e.val.1) equal
    change vertices i.castSucc = vertices j.castSucc at first
    exact Fin.ext (congrArg (fun j : Fin (s+2) => j.val) (distinct first))
  refine (full fits).false
    { vertex := vertices
      arc := owner ∘ arc
      river := owner river
      distinctVertices := distinct
      distinctArcs := unique.comp arcInjective
      river_ne_arc := ?_
      riverStep := compares river
      arcStep := fun i => compares (arc i) }
  intro i equal
  have same := unique equal
  have first := congrArg (fun e : arcs => e.val.1) same
  have second := congrArg (fun e : arcs => e.val.2) same
  change vertices 0 = vertices i.castSucc at first
  change vertices (Fin.last (s+1)) = vertices i.succ at second
  have zero := congrArg Fin.val (distinct first)
  have last := congrArg Fin.val (distinct second)
  change 0 = i.val at zero
  change s+1 = i.val+1 at last
  omega

/-- A strict comparison on each arc excludes loops. -/
theorem arc_owners_loopless {V I : Type*} [DecidableEq V] {rows : I → List V}
    {arcs : Finset (V × V)} {owner : arcs → I}
    (compares : ∀ e : arcs, Before rows (owner e) e.val.1 e.val.2) (x : V) :
    (x,x) ∉ arcs :=
  fun loop => listBefore_ne (compares ⟨(x,x),loop⟩) rfl

/-- In a full-three-free system, injectively owned arcs exclude transitive triangles. -/
theorem arc_owners_no_transitive_triangle {V I : Type*} [DecidableEq V] {rows : I → List V}
    {arcs : Finset (V × V)} {owner : arcs → I} (unique : Function.Injective owner)
    (compares : ∀ e : arcs, Before rows (owner e) e.val.1 e.val.2)
    {k : ℕ} (full : BridgeFree (Before rows) k) (three : 3 ≤ k) {x y z : V}
    (xy : (x,y) ∈ arcs) (yz : (y,z) ∈ arcs) (xz : (x,z) ∈ arcs) : False := by
  have xyApart := listBefore_ne (compares ⟨(x,y),xy⟩)
  have yzApart := listBefore_ne (compares ⟨(y,z),yz⟩)
  have xzApart := listBefore_ne (compares ⟨(x,z),xz⟩)
  have vertices : Function.Injective (![x,y,z] : Fin 3 → V) := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp_all
  exact no_detour_of_distinct_arc_owners full three (by decide : 0 < 1)
    owner unique compares ![x,y,z] vertices (by intro i; fin_cases i; exacts [xy,yz]) xz

/-- Two common neighbors in the reciprocal graph give a full four-bridge.
The sum of squared degrees bounds the square of its edge count. -/
theorem reciprocal_edge_square_le_of_distinct_arc_owners {V I : Type*} [Fintype V] [DecidableEq V]
    {rows : I → List V} {arcs : Finset (V × V)} {owner : arcs → I}
    (loopless : ∀ x, (x,x) ∉ arcs) (unique : Function.Injective owner)
    (compares : ∀ e : arcs, Before rows (owner e) e.val.1 e.val.2)
    {k : ℕ} (full : BridgeFree (Before rows) k) (four : 4 ≤ k) :
    (2*(reciprocalGraph arcs loopless).edgeFinset.card)^2 ≤ 2*(Fintype.card V)^3 := by
  let reciprocal := reciprocalGraph arcs loopless
  have oneCommon {x z a b : V} (xz : x ≠ z) (ax : reciprocal.Adj a x)
      (az : reciprocal.Adj a z) (bx : reciprocal.Adj b x) (bz : reciprocal.Adj b z) : a = b := by
    by_contra ab
    have axApart := reciprocal.ne_of_adj ax
    have azApart := reciprocal.ne_of_adj az
    have bxApart := reciprocal.ne_of_adj bx
    have bzApart := reciprocal.ne_of_adj bz
    have vertices : Function.Injective (![x,a,z,b] : Fin 4 → V) := by
      intro i j eq
      fin_cases i <;> fin_cases j <;> simp_all
    exact no_detour_of_distinct_arc_owners full four (by decide : 0 < 2) owner unique compares
      ![x,a,z,b] vertices (by intro i; fin_cases i; exacts [ax.2,az.1,bz.2]) bx.2
  exact graph_edge_square_le_of_unique_common_neighbor reciprocal (fun {_ _ _ _} => oneCommon)

/-- First darts of a literal full-four-free system decompose into a
(K_4)-free undirected shadow and a subquadratic reciprocal part. The
singletons use at most one additional row per vertex. -/
theorem literal_full_four_path_count_bound {v q k : ℕ} (paths : Fin q → List (Fin v))
    (distinct : Function.Injective paths) (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (full : BridgeFree (Before paths) k) (four : 4 ≤ k) :
    ∃ edges reciprocal : ℕ, q ≤ v+edges+reciprocal ∧ 3*edges ≤ v^2 ∧ (2*reciprocal)^2 ≤ 2*v^3 := by
  obtain ⟨arcs,count,owner,unique,compares⟩ := literal_first_darts paths distinct valid full.halfFree (by omega)
  let loopless := arc_owners_loopless compares
  let shadow := arcShadow arcs loopless
  let reciprocal := reciprocalGraph arcs loopless
  have freeShadow : shadow.CliqueFree (3+1) :=
    arcShadow_cliqueFree_four arcs loopless
      (fun {_ _ _} => arc_owners_no_transitive_triangle unique compares full (by omega))
  have edgeCount := freeShadow.card_edgeFinset_le
  rw [Fintype.card_fin,SimpleGraph.turanNumber_three] at edgeCount
  have limit : 3*shadow.edgeFinset.card ≤ v^2 := by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_right 3 edgeCount).trans (Nat.div_mul_le_self _ _)
  have reciprocalBound := reciprocal_edge_square_le_of_distinct_arc_owners loopless unique compares full four
  rw [Fintype.card_fin] at reciprocalBound
  have firstCount := arcs_card_le_shadow_add_reciprocal arcs loopless
  exact ⟨shadow.edgeFinset.card,reciprocal.edgeFinset.card,by
    dsimp [shadow,reciprocal]
    omega,limit,reciprocalBound⟩

/-- Every row contributes at most two visits apart from the long-row mass. -/
theorem list_mass_le_twice_rows_add_long {v q : ℕ} (rows : Fin q → List (Fin v)) :
    (∑ i, (rows i).length) ≤ 2*q+listMassAboveWidth rows 2 := calc
  _ ≤ ∑ i, (2+(if 2 < (rows i).length then (rows i).length else 0)) := by
    apply sum_le_sum
    intro i _
    by_cases longRow : 2 < (rows i).length
    · simp [longRow]
    · simpa [longRow] using (le_of_not_gt longRow)
  _ = _ := by
    rw [sum_add_distrib, show (∑ _ : Fin q, (2:ℕ)) = 2*q by simp [Nat.mul_comm]]
    simp [listMassAboveWidth,sum_filter]

/-- At any full cutoff of at least four, the literal mass is at most
two thirds of the vertex square plus an arbitrarily small quadratic error,
uniformly under smaller vertex budgets. -/
theorem literal_full_mass_le_two_thirds_square_of_cutoff_four (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n v q k : ℕ}, N ≤ n → v ≤ n → 4 ≤ k → ∀ rows : Fin q → List (Fin v),
      Function.Injective rows → (∀ i, rows i ≠ [] ∧ (rows i).Nodup) → BridgeFree (Before rows) k →
      ((∑ i, (rows i).length : ℕ):ℝ) ≤ (2/3+ε)*(n:ℝ)^2 := by
  obtain ⟨N,small⟩ := full_three_long_mass_subquadratic_within_vertex_budget (ε/2) (by positivity)
  let linear := ⌈8/ε⌉₊
  let reciprocal := ⌈32/ε^2⌉₊
  refine ⟨max N (max linear reciprocal),?_⟩
  intro n v q k large fits four rows distinct valid full
  obtain ⟨edges,extra,count,shadow,reciprocalBound⟩ := literal_full_four_path_count_bound rows distinct valid full four
  have count' : (q:ℝ) ≤ (n:ℝ)+edges+extra := by
    exact_mod_cast count.trans (Nat.add_le_add_right (Nat.add_le_add_right fits _) _)
  have shadow' : 3*(edges:ℝ) ≤ (n:ℝ)^2 := by
    exact_mod_cast shadow.trans (Nat.pow_le_pow_left fits 2)
  have reciprocal' : (2*(extra:ℝ))^2 ≤ 2*(n:ℝ)^3 := by
    exact_mod_cast reciprocalBound.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left fits 3))
  have evanescent := (le_max_right N _).trans large
  have sufficientLinear : (8:ℝ)/ε ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_left _ _).trans evanescent))
  have sufficientReciprocal : (32:ℝ)/ε^2 ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans evanescent))
  have linearError : 2*(n:ℝ) ≤ (ε/4)*(n:ℝ)^2 := by
    have gate := (div_le_iff₀ positive).mp sufficientLinear
    have scaled := mul_le_mul_of_nonneg_right gate (show 0 ≤ (n:ℝ) by positivity)
    nlinarith only [scaled]
  have reciprocalError : 2*(extra:ℝ) ≤ (ε/4)*(n:ℝ)^2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have gate := (div_le_iff₀ (by positivity : 0 < ε^2)).mp sufficientReciprocal
    have scaled := mul_le_mul_of_nonneg_right gate (show 0 ≤ (n:ℝ)^3 by positivity)
    exact reciprocal'.trans (by nlinarith only [scaled])
  have long := small ((le_max_left N _).trans large) fits (by omega : 3 ≤ k) rows
    (fun i => (valid i).2) full
  have mass := list_mass_le_twice_rows_add_long rows
  have mass' : ((∑ i, (rows i).length : ℕ):ℝ) ≤ 2*(q:ℝ)+(listMassAboveWidth rows 2:ℝ) := by
    exact_mod_cast mass
  nlinarith only [count',shadow',linearError,reciprocalError,long,mass']

/-- At the saturated literal half budget the half mass is exactly
(M=n^2+2). The optimal full-four-free mass lies between
(2/3 − ε)M and (2/3 + ε)M for all large n.
The lower witness satisfies both budgets and all four original-average caps. -/
theorem literal_saturated_half_full_four_mass_comparison (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n →
      let p := n+n.choose 2+1
      let M := n^2+2
      (∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
        (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ (∀ k, HalfBridgeFree (Before paths) k) ∧
        (∑ i, (paths i).length) = M) ∧
      (∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 4 ∧
        (2/3-ε)*(M:ℝ) ≤ ((∑ i, (rows i).length : ℕ):ℝ) ∧
        (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows) ∧
      ∀ {v q : ℕ}, v ≤ n → q ≤ p → ∀ rows : Fin q → List (Fin v), Function.Injective rows →
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) → BridgeFree (Before rows) 4 →
        ((∑ i, (rows i).length : ℕ):ℝ) ≤ (2/3+ε)*(M:ℝ) := by
  obtain ⟨U,upper⟩ := literal_full_mass_le_two_thirds_square_of_cutoff_four ε positive
  obtain ⟨L,lower⟩ := frozen_full_four_cyclic_pairs_at_saturated_half_budget (ε/2) (by positivity)
  let margin := max 2 ⌈4/ε⌉₊
  refine ⟨max (max U L) margin,?_⟩
  intro n large
  let p := n+n.choose 2+1
  have enough := (le_max_left (max U L) margin).trans large
  have nMargin := (le_max_right (max U L) margin).trans large
  have nTwo : 2 ≤ n := (le_max_left _ _).trans nMargin
  obtain ⟨paths,distinct,valid,all⟩ := literal_half_all_of_choose_budget (n := n) (p := p)
    (by simp [p,nTwo])
  have mass := literal_half_mass_at_saturated_four_budget distinct valid (all 4) le_rfl
  have identity := twice_choose_two_add_self n
  obtain ⟨v,vFits,q,qFits,rows,unique,well,free,lowerMass,massFits,caps⟩ := lower ((le_max_right U L).trans enough)
  refine ⟨⟨paths,distinct,valid,all,by omega⟩,⟨v,vFits,q,qFits,rows,unique,well,free,?_,massFits,caps⟩,?_⟩
  · have grows : (4:ℝ)/ε ≤ n :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans nMargin))
    have epsN := (div_le_iff₀ positive).mp grows
    have one : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have nSq : (n:ℝ) ≤ (n:ℝ)^2 := by
      rw [pow_two]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right one (show 0 ≤ (n:ℝ) by positivity)
    have epsSquare := mul_le_mul_of_nonneg_right nSq positive.le
    change (2/3-ε)*((n^2+2 : ℕ):ℝ) ≤ _
    refine le_trans ?_ lowerMass
    push_cast
    nlinarith only [epsN,epsSquare,positive]
  · intro v q fits _ rows distinct valid full
    have bound := upper ((le_max_left U L).trans enough) fits (le_rfl : 4 ≤ 4) rows distinct valid full
    refine bound.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact_mod_cast (Nat.le_add_right (n^2) 2)

end OnlineReachabilityPreservers
