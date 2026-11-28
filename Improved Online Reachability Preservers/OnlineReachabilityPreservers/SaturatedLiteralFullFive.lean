import OnlineReachabilityPreservers.SaturatedLiteralFullFour
import Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Nat.Choose.Bounds

/-! Sharp mass comparison from full cutoff five at the saturated literal half budget. -/

namespace OnlineReachabilityPreservers

open Finset Filter SimpleGraph
local notation "Before" => SourceAudit.BeforeIn

private theorem triangle_completes_cyclic {V : Type*} [DecidableEq V] {arcs : Finset (V × V)}
    (noTriangle : ∀ {x y z}, (x,y) ∈ arcs → (y,z) ∈ arcs → (x,z) ∉ arcs)
    {x y z : V} (first : (x,y) ∈ arcs)
    (next : (y,z) ∈ arcs ∨ (z,y) ∈ arcs) (last : (z,x) ∈ arcs ∨ (x,z) ∈ arcs) :
    (y,z) ∈ arcs ∧ (z,x) ∈ arcs := by
  rcases next with next | reverse
  · exact ⟨next,last.resolve_right (noTriangle first next)⟩
  · rcases last with last | forward
    · exact (noTriangle last first reverse).elim
    · exact (noTriangle forward reverse first).elim

private theorem arcShadow_triplePair_free {V I : Type*} [DecidableEq V]
    {rows : I → List V} {arcs : Finset (V × V)}
    (loopless : ∀ x, (x,x) ∉ arcs) (owner : arcs → I) (unique : Function.Injective owner)
    (compares : ∀ edge : arcs, Before rows (owner edge) edge.val.1 edge.val.2)
    (noTriangle : ∀ {x y z}, (x,y) ∈ arcs → (y,z) ∈ arcs → (x,z) ∉ arcs)
    {cutoff : ℕ} (full : BridgeFree (Before rows) cutoff) (five : 5 ≤ cutoff) :
    (SimpleGraph.completeEquipartiteGraph 3 2).Free (arcShadow arcs loopless) := by
  rintro ⟨copy⟩
  let label (layer : Fin 3) (index : Fin 2) := copy (layer,index)
  have cross {a b : Fin 3} (different : a ≠ b) (i j : Fin 2) :
      (label a i,label b j) ∈ arcs ∨ (label b j,label a i) ∈ arcs :=
    copy.toHom.map_adj (SimpleGraph.completeEquipartiteGraph_adj.mpr different)
  have detour {a b c : Fin 3} (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a)
      (first : (label a 0,label b 0) ∈ arcs) : False := by
    obtain ⟨second,_⟩ := triangle_completes_cyclic (fun {_ _ _} => noTriangle) first (cross bc 0 0) (cross ca 0 0)
    obtain ⟨third,_⟩ := triangle_completes_cyclic (fun {_ _ _} => noTriangle) second (cross ca 0 1) (cross ab 1 0)
    obtain ⟨fourth,back⟩ := triangle_completes_cyclic (fun {_ _ _} => noTriangle) third (cross ab 1 1) (cross bc 1 0)
    obtain ⟨_,direct⟩ := triangle_completes_cyclic (fun {_ _ _} => noTriangle) back (cross ca 0 0) (cross ab 0 1)
    let point : Fin 5 → Fin 3 × Fin 2 := ![(a,0),(b,0),(c,0),(a,1),(b,1)]
    have pointsDistinct : Function.Injective point := by
      intro i j same
      fin_cases i <;> fin_cases j <;>
        first | rfl | simp [point,ab,bc,ca,ab.symm,bc.symm,ca.symm] at same
    let vertices : Fin 5 → V := copy ∘ point
    have distinct : Function.Injective vertices := copy.injective.comp pointsDistinct
    apply no_detour_of_distinct_arc_owners full five (by decide : 0 < 3) owner unique compares vertices distinct _ direct
    intro i
    fin_cases i
    exacts [first,second,third,fourth]
  rcases cross (by decide : (0 : Fin 3) ≠ 1) 0 0 with forward | reverse
  · exact detour (by decide : (0 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 2)
      (by decide : (2 : Fin 3) ≠ 0) forward
  · exact detour (by decide : (1 : Fin 3) ≠ 0) (by decide : (0 : Fin 3) ≠ 2)
      (by decide : (2 : Fin 3) ≠ 1) reverse

private abbrev triplePairGraph := completeEquipartiteGraph 3 2

private theorem triplePairGraph_ne_bot : triplePairGraph ≠ ⊥ := by
  intro empty
  have cross : triplePairGraph.Adj (0,0) (1,0) :=
    (completeEquipartiteGraph_adj).mpr (by decide)
  rw [empty] at cross
  exact cross

private theorem triplePair_extremal_quadratic_linear (ε : ℝ) (positive : 0 < ε) :
    ∃ C : ℕ, ∀ n : ℕ,
      (extremalNumber n triplePairGraph : ℝ) ≤ (1/4+ε/2)*((n:ℝ)^2+n)+(C:ℝ)^2 := by
  obtain ⟨N,eventual⟩ := eventually_atTop.mp
    (eventually_completeEquipartiteGraph_isContained_of_minDegree positive 2 2)
  refine ⟨N,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    classical
    obtain ⟨G,dec,best⟩ := exists_isExtremal_free (V := Fin n) triplePairGraph_ne_bot
    let _ := dec
    have maximum : G.edgeFinset.card = extremalNumber n triplePairGraph := by
      simpa only [Fintype.card_fin] using G.card_edgeFinset_of_isExtremal_free best
    rw [← maximum]
    by_cases large : N ≤ n ∧ 0 < n
    · let _ : Nonempty (Fin n) := ⟨⟨0,large.2⟩⟩
      have low : (G.minDegree : ℝ) < (1-1/(2:ℝ)+ε)*(n:ℝ) := by
        by_contra! high
        exact best.prop (eventual n large.1 high)
      obtain ⟨v,degree⟩ := G.exists_minimal_degree_vertex
      have neighborhood : (G.degree v : ℝ) < 2*(1/4+ε/2)*(n:ℝ) := by
        rw [← degree]
        linarith only [low]
      have residual := G.card_edgeFinset_deleteIncidenceSet_le_extremalNumber best.prop v
      rw [Fintype.card_fin] at residual
      have rest : ((G.deleteIncidenceSet v).edgeFinset.card:ℝ) ≤
          (1/4+ε/2)*(((n-1:ℕ):ℝ)^2+(n-1:ℕ))+(N:ℝ)^2 :=
        (Nat.cast_le.mpr residual).trans (ih (n-1) (by omega))
      rw [Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one] at rest
      have split : G.edgeFinset.card = (G.deleteIncidenceSet v).edgeFinset.card+G.degree v := by
        rw [G.card_edgeFinset_deleteIncidenceSet]
        exact (Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)).symm
      rw [split,Nat.cast_add]
      nlinarith only [rest,neighborhood]
    · have small : n ≤ N := by omega
      have edges : G.edgeFinset.card ≤ n^2 := by
        have pairs := G.card_edgeFinset_le_card_choose_two
        rw [Fintype.card_fin] at pairs
        exact pairs.trans (Nat.choose_le_pow _ _)
      have residual : (G.edgeFinset.card : ℝ) ≤ (N:ℝ)^2 := by
        exact_mod_cast edges.trans (Nat.pow_le_pow_left small 2)
      exact residual.trans (le_add_of_nonneg_left (by positivity))

private theorem triplePair_free_graph_edges_le_quarter (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n v : ℕ}, N ≤ n → v ≤ n →
      ∀ (G : SimpleGraph (Fin v)) [DecidableRel G.Adj], triplePairGraph.Free G →
        (G.edgeFinset.card:ℝ) ≤ (1/4+ε)*(n:ℝ)^2 := by
  obtain ⟨C,control⟩ := triplePair_extremal_quadratic_linear ε positive
  let a : ℝ := 1/4+ε/2
  let linear := ⌈4*a/ε⌉₊
  let residual := ⌈4*(C:ℝ)^2/ε⌉₊
  refine ⟨max 1 (max linear residual),?_⟩
  intro n v large fits G _ free
  have upper := G.card_edgeFinset_le_extremalNumber free
  rw [Fintype.card_fin] at upper
  have finite : (G.edgeFinset.card:ℝ) ≤ a*((v:ℝ)^2+v)+(C:ℝ)^2 :=
    (Nat.cast_le.mpr upper).trans (control v)
  have fitsReal : (v:ℝ) ≤ n := by exact_mod_cast fits
  have compare : (v:ℝ)^2+(v:ℝ) ≤ (n:ℝ)^2+(n:ℝ) :=
    add_le_add ((sq_le_sq₀ (by positivity) (by positivity)).mpr fitsReal) fitsReal
  have nonnegative : 0 ≤ a := by
    change 0 ≤ (1:ℝ)/4+ε/2
    positivity
  have bound : (G.edgeFinset.card:ℝ) ≤ a*((n:ℝ)^2+n)+(C:ℝ)^2 :=
    finite.trans (add_le_add (mul_le_mul_of_nonneg_left compare nonnegative) le_rfl)
  have tail := (le_max_right 1 _).trans large
  have enoughLin : 4*a/ε ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_left _ _).trans tail))
  have enoughConst : 4*(C:ℝ)^2/ε ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans tail))
  have paidLin := mul_le_mul_of_nonneg_right ((div_le_iff₀ positive).mp enoughLin)
    (show 0 ≤ (n:ℝ) by positivity)
  have paidConst := (div_le_iff₀ positive).mp enoughConst
  have one : (1:ℝ) ≤ n := by exact_mod_cast (le_max_left 1 _).trans large
  have square : (n:ℝ) ≤ (n:ℝ)^2 := by
    rw [pow_two]
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right one (show 0 ≤ (n:ℝ) by positivity))
  have larger := mul_le_mul_of_nonneg_right square positive.le
  dsimp [a] at bound paidLin
  nlinarith only [bound,paidLin,paidConst,larger]


/-- At a full cutoff of at least five, the first-pair shadow omits
the complete three-partite graph with two vertices per part. The
literal row count is asymptotically at most one quarter of the vertex
square, uniformly within any smaller vertex budget. -/
theorem literal_full_five_path_count_le_quarter_square (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n v q k : ℕ}, N ≤ n → v ≤ n → 5 ≤ k → ∀ paths : Fin q → List (Fin v),
      Function.Injective paths → (∀ i, paths i ≠ [] ∧ (paths i).Nodup) → BridgeFree (Before paths) k →
      (q:ℝ) ≤ (1/4+ε)*(n:ℝ)^2 := by
  obtain ⟨S,shadowBound⟩ := triplePair_free_graph_edges_le_quarter (ε/2) (by positivity)
  let linear := ⌈4/ε⌉₊
  let reciprocalThreshold := ⌈8/ε^2⌉₊
  refine ⟨max S (max linear reciprocalThreshold),?_⟩
  intro n v q k large fits five paths distinct valid full
  obtain ⟨arcs,count,owner,unique,compares⟩ := literal_first_darts paths distinct valid full.halfFree (by omega)
  let loopless := arc_owners_loopless compares
  let shadow := arcShadow arcs loopless
  let reciprocal := reciprocalGraph arcs loopless
  have shadowFree := arcShadow_triplePair_free loopless owner unique compares
    (fun {_ _ _} => arc_owners_no_transitive_triangle unique compares full (by omega)) full five
  have shadowEdges := shadowBound ((le_max_left S _).trans large) fits shadow shadowFree
  have reciprocalBound := reciprocal_edge_square_le_of_distinct_arc_owners loopless unique compares full (by omega)
  rw [Fintype.card_fin] at reciprocalBound
  have countArcs := arcs_card_le_shadow_add_reciprocal arcs loopless
  have pathCap : (q:ℝ) ≤ (n:ℝ)+shadow.edgeFinset.card+reciprocal.edgeFinset.card := by
    have raw : q ≤ n+shadow.edgeFinset.card+reciprocal.edgeFinset.card := calc
      _ ≤ v+arcs.card := count
      _ ≤ v+(shadow.edgeFinset.card+reciprocal.edgeFinset.card) := Nat.add_le_add_left countArcs v
      _ ≤ _ := by rw [← Nat.add_assoc]; gcongr
    exact_mod_cast raw
  have reciprocal' : (2*(reciprocal.edgeFinset.card:ℝ))^2 ≤ 2*(n:ℝ)^3 := by
    exact_mod_cast reciprocalBound.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left fits 3))
  have tail := (le_max_right S _).trans large
  have sufficientLinear : (4:ℝ)/ε ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_left _ _).trans tail))
  have sufficientReciprocal : (8:ℝ)/ε^2 ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans tail))
  have linearError : 2*(n:ℝ) ≤ (ε/2)*(n:ℝ)^2 := by
    have gate := (div_le_iff₀ positive).mp sufficientLinear
    have scaled := mul_le_mul_of_nonneg_right gate (show 0 ≤ (n:ℝ) by positivity)
    nlinarith only [scaled]
  have reciprocalError : 2*(reciprocal.edgeFinset.card:ℝ) ≤ (ε/2)*(n:ℝ)^2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have gate := (div_le_iff₀ (by positivity : 0 < ε^2)).mp sufficientReciprocal
    have scaled := mul_le_mul_of_nonneg_right gate (show 0 ≤ (n:ℝ)^3 by positivity)
    exact reciprocal'.trans (by nlinarith only [scaled])
  nlinarith only [pathCap,shadowEdges,linearError,reciprocalError]

/-- At full cutoff five and above, literal full mass is at most
one half of the vertex square plus an arbitrarily small quadratic error. -/
theorem literal_full_mass_le_half_square_of_cutoff_five (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n v q k : ℕ}, N ≤ n → v ≤ n → 5 ≤ k → ∀ rows : Fin q → List (Fin v),
      Function.Injective rows → (∀ i, rows i ≠ [] ∧ (rows i).Nodup) → BridgeFree (Before rows) k →
      ((∑ i, (rows i).length : ℕ):ℝ) ≤ (1/2+ε)*(n:ℝ)^2 := by
  obtain ⟨Q,few⟩ := literal_full_five_path_count_le_quarter_square (ε/4) (by positivity)
  obtain ⟨L,small⟩ := full_three_long_mass_subquadratic_within_vertex_budget (ε/2) (by positivity)
  refine ⟨max Q L,?_⟩
  intro n v q k large fits five rows distinct valid full
  have pathCount := few ((le_max_left Q L).trans large) fits five rows distinct valid full
  have long := small ((le_max_right Q L).trans large) fits (by omega : 3 ≤ k) rows (fun i => (valid i).2) full
  have mass := list_mass_le_twice_rows_add_long rows
  have mass' : ((∑ i, (rows i).length : ℕ):ℝ) ≤ 2*(q:ℝ)+(listMassAboveWidth rows 2:ℝ) := by
    exact_mod_cast mass
  nlinarith only [mass',long,pathCount]

/-- At all full cutoffs of at least five, the sharp asymptotic mass ratio at the
saturated literal half budget is one half. The all-cutoff pair witness
fits both input budgets and all four original-average caps. -/
theorem literal_saturated_half_full_five_mass_comparison (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n →
      let p := n+n.choose 2+1
      let M := n^2+2
      (∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
        (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ (∀ k, HalfBridgeFree (Before paths) k) ∧
        (∑ i, (paths i).length) = M) ∧
      (∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ (∀ k, BridgeFree (Before rows) k) ∧
        (1/2-ε)*(M:ℝ) ≤ ((∑ i, (rows i).length : ℕ):ℝ) ∧
        (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows) ∧
      ∀ {v q k : ℕ}, v ≤ n → q ≤ p → 5 ≤ k → ∀ rows : Fin q → List (Fin v), Function.Injective rows →
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) → BridgeFree (Before rows) k →
        ((∑ i, (rows i).length : ℕ):ℝ) ≤ (1/2+ε)*(M:ℝ) := by
  obtain ⟨U,upper⟩ := literal_full_mass_le_half_square_of_cutoff_five ε positive
  obtain ⟨L,lower⟩ := frozen_full_all_pairs_at_saturated_half_budget (ε/2) (by positivity)
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
    change (1/2-ε)*((n^2+2 : ℕ):ℝ) ≤ _
    refine le_trans ?_ lowerMass
    push_cast
    nlinarith only [epsN,epsSquare,positive]
  · intro v q k fits _ five rows distinct valid full
    have bound := upper ((le_max_left U L).trans enough) fits five rows distinct valid full
    refine bound.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact_mod_cast (Nat.le_add_right (n^2) 2)

end OnlineReachabilityPreservers
