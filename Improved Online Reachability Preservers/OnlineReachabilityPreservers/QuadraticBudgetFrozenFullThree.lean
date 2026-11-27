import OnlineReachabilityPreservers.QuadraticThreeRows
import OnlineReachabilityPreservers.ExtremalCopyBounds
import OnlineReachabilityPreservers.FullDisjointUnion
import OnlineReachabilityPreservers.FullThreeLiteralFeasibility

/-! Frozen full-three witnesses in ranges above the quadratic field budgets. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- In a box of multiplicative width nine eighths above either quadratic
budget, half-three mass is at most four times the one-layer-short witness. -/
theorem half_three_mass_le_four_near_quadratic_budgets {n p N P q cutoff : ℕ} (large : 16 ≤ q)
    (shape : (N = q^4 ∧ P = q^5) ∨ (N = q^5 ∧ P = q^4))
    (nBounds : N ≤ n ∧ 8*n ≤ 9*N) (pBounds : P ≤ p ∧ 8*p ≤ 9*P)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) cutoff) (three : 3 ≤ cutoff) :
    (∑ i, (paths i).length) ≤ 4*(q^5*(q-1)) := by
  have qPos : 0 < q := by omega
  have hn : 0 < n := (show 0 < N by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity).trans_le nBounds.1
  have hp : 0 < p := (show 0 < P by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity).trans_le pBounds.1
  have smaller : q^4 ≤ q^5 := Nat.pow_le_pow_right qPos (by decide)
  have envelope : N ≤ q^5 ∧ P ≤ q^5 := by
    rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨smaller,le_rfl⟩
    · exact ⟨le_rfl,smaller⟩
  have volume : N*P = q^9 := by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> ring
  have nCap := nBounds.2.trans (Nat.mul_le_mul_left 9 envelope.1)
  have pCap := pBounds.2.trans (Nat.mul_le_mul_left 9 envelope.2)
  have charge : 8*(4*n+p) ≤ 45*q^5 := by omega
  have product : 64*(n*p) ≤ 81*q^9 := calc
    _ = (8*n)*(8*p) := by ring
    _ ≤ (9*N)*(9*P) := Nat.mul_le_mul nBounds.2 pBounds.2
    _ = 81*(N*P) := by ring
    _ = _ := by rw [volume]
  have square : 64^2*(n*p)^2 ≤ 81^2*q^18 := calc
    _ = (64*(n*p))^2 := by ring
    _ ≤ (81*q^9)^2 := Nat.pow_le_pow_left product 2
    _ = _ := by ring
  let M := ∑ i, (paths i).length
  let W := q^5*(q-1)
  let S := M-M/4-(4*n+p)
  have balance : W+q^5 = q^6 := calc
    _ = q^5*((q-1)+1) := by dsimp only [W]; ring
    _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]; ring
  have cube : S^3 ≤ 6*(n*p)^2 :=
    half_three_latest_intersection_shifted_mass_cube_le hn hp paths simple half three 3
  by_contra! excess
  have scale : 69*q^5 ≤ 6*q^6 := calc
    _ ≤ (6*q)*q^5 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  have floor : 4*(M/4) ≤ M := Nat.mul_div_le _ _
  have gap : 9*q^6 < 4*S := by dsimp only [S]; omega
  have cap : 64^2*(4*S)^3 ≤ 64^2*(9*q^6)^3 := calc
    _ = 4^3*(64^2*S^3) := by ring
    _ ≤ (4^3*6)*(64^2*(n*p)^2) := by
      convert Nat.mul_le_mul_left (4^3) (Nat.mul_le_mul_left (64^2) cube) using 1
      ring
    _ ≤ (4^3*6)*(81^2*q^18) := Nat.mul_le_mul_left _ square
    _ = (4^3*6*81^2)*q^18 := by ring
    _ ≤ (64^2*9^3)*q^18 := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring
  exact (not_lt_of_ge cap) (Nat.mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ gap (Nat.zero_le _) (by decide : 3 ≠ 0)) (by decide))

private theorem quadraticForwardReserve {q n p : ℕ} (large : 16 ≤ q) (vertexFit : q^4 ≤ n)
    (rowFit : q^5 ≤ p) (rowCap : 8*p ≤ 9*q^5) :
    p-q^5 ≤ ((n-(q-1)*q^3)/2)*((n-(q-1)*q^3)-(n-(q-1)*q^3)/2) := by
  let r := n-(q-1)*q^3
  let extra := p-q^5
  have mask : (q-1)*q^3+q^3 = q^4 := calc
    _ = ((q-1)+1)*q^3 := by ring
    _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]; ring
  have room : q^3 ≤ r := by dsimp only [r]; omega
  have scale : 2*q^2 ≤ q^3 := calc
    _ ≤ q*q^2 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  have cubeLarge : 8 ≤ q^3 := by
    exact (show 8 = 2^3 by decide).trans_le (Nat.pow_le_pow_left (by omega : 2 ≤ q) 3)
  have count : 8*extra ≤ q^5 := by dsimp only [extra]; omega
  have product : q^5 ≤ 8*(q^2*(q^3/4)) := calc
    _ = q^2*q^3 := by ring
    _ ≤ q^2*(8*(q^3/4)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring
  have cap : q^2*(q^3/4) ≤ (r/2)*(r-r/2) := Nat.mul_le_mul (by omega) (by omega)
  exact Nat.le_of_mul_le_mul_left (count.trans (product.trans (Nat.mul_le_mul_left _ cap))) (by decide)

private theorem quadraticForwardExact {q n p : ℕ} (large : 16 ≤ q) (vertexFit : q^4 ≤ n)
    (rowFit : q^5 ≤ p) (rowCap : 8*p ≤ 9*q^5)
    (rows : Fin (q^5) → List (Fin ((q-1)*q^3))) (injective : Function.Injective rows)
    (well : ∀ i, rows i ≠ [] ∧ (rows i).Nodup) (free : BridgeFree (Before rows) 3) :
    ∃ candidate : Fin p → List (Fin n), Function.Injective candidate ∧
      (∀ i, candidate i ≠ [] ∧ (candidate i).Nodup) ∧ BridgeFree (Before candidate) 3 ∧
      (∑ i, (rows i).length) ≤ ∑ i, (candidate i).length := by
  let available := n-(q-1)*q^3
  let extra := p-q^5
  have enough : extra ≤ available+2*((available/2)*(available-available/2)) := by
    have cap := quadraticForwardReserve large vertexFit rowFit rowCap
    change extra ≤ (available/2)*(available-available/2) at cap
    omega
  have vertexSum : (q-1)*q^3+available = n := Nat.add_sub_of_le
    ((Nat.mul_le_mul_right (q^3) (Nat.sub_le q 1)).trans (by convert vertexFit using 1; ring))
  have pathSum : q^5+extra = p := Nat.add_sub_of_le rowFit
  obtain ⟨padding,padDistinct,padRows,padFree⟩ := literal_full_three_feasible_iff.mpr enough
  obtain ⟨joined,joinedDistinct,joinedRows,joinedFree,joinedMass⟩ :=
    exists_literal_full_disjoint_union rows padding injective padDistinct well padRows free padFree
  let Output (v r : ℕ) : Prop := ∃ candidate : Fin r → List (Fin v), Function.Injective candidate ∧
    (∀ i, candidate i ≠ [] ∧ (candidate i).Nodup) ∧ BridgeFree (Before candidate) 3 ∧
    (∑ i, (rows i).length) ≤ ∑ i, (candidate i).length
  have combined : Output ((q-1)*q^3+available) (q^5+extra) :=
    ⟨joined,joinedDistinct,joinedRows,joinedFree,by rw [joinedMass]; omega⟩
  rwa [vertexSum,pathSum] at combined

/-- At either quadratic budget and all larger counts up to nine eighths
of both coordinates, the literal half-three maximum is achieved. An
output using one fewer layer fits both budgets, meets the four original
average caps, and retains a quarter of the maximum. -/
theorem localOrderDistinctExtremal_frozen_full_three_near_quadratic_budgets (F : Type*)
    [Field F] [Fintype F] (large : 16 ≤ Fintype.card F) {n p N P : ℕ}
    (shape : let q := Fintype.card F; (N = q^4 ∧ P = q^5) ∨ (N = q^5 ∧ P = q^4))
    (nBounds : N ≤ n ∧ 8*n ≤ 9*N) (pBounds : P ≤ p ∧ 8*p ≤ 9*P) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ v ≤ n, ∃ r ≤ p, ∃ rows : Fin r → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (∑ i, (rows i).length) = (Fintype.card F)^5*(Fintype.card F-1) ∧
        (∑ i, (rows i).length) ≤ M ∧ M ≤ 4*(∑ i, (rows i).length) ∧
        frozenListCaps n p M rows := by
  let q := Fintype.card F
  let m := q-1
  let W := q^5*m
  have qPos : 0 < q := Fintype.card_pos
  have two : 2 ≤ m := by dsimp only [m]; omega
  have fits : m ≤ q := Nat.sub_le _ _
  have hp : 0 < p := (show 0 < P by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity).trans_le pBounds.1
  have hn : 0 < n := (show 0 < N by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> positivity).trans_le nBounds.1
  obtain ⟨v,r,len,deg,sized⟩ : ∃ v r len deg,
      (N = q^4 ∧ P = q^5 ∧ v = m*q^3 ∧ r = q^5 ∧ len = m ∧ deg = q^2) ∨
      (N = q^5 ∧ P = q^4 ∧ v = q^5 ∧ r = m*q^3 ∧ len = q^2 ∧ deg = m) := by
    rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨_,_,_,_,Or.inl ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
    · exact ⟨_,_,_,_,Or.inr ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  have mCube : m*q^3 ≤ q^4 := calc
    _ ≤ q*q^3 := Nat.mul_le_mul_right _ fits
    _ = _ := by ring
  have dims : v ≤ N ∧ r ≤ P := by
    rcases sized with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    · exact ⟨mCube,le_rfl⟩
    · exact ⟨le_rfl,mCube⟩
  have partBalance : v*deg = W ∧ r*len = W := by
    rcases sized with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ <;>
      constructor <;> dsimp only [W] <;> ring
  have Wcap : W ≤ q^6 := calc
    _ ≤ q^5*q := Nat.mul_le_mul_left _ fits
    _ = _ := by ring
  have measure : N*deg ≤ q^6 ∧ P*len ≤ q^6 := by
    rcases sized with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    · exact ⟨le_of_eq (by ring),Wcap⟩
    · exact ⟨Wcap,le_of_eq (by ring)⟩
  have lLarge : 2 ≤ len := by
    rcases sized with ⟨_,_,_,_,rfl,_⟩ | ⟨_,_,_,_,rfl,_⟩
    · exact two
    · nlinarith
  have layerShape : (v = m*q^3 ∧ r = q^5 ∧ len = m ∧ deg = q^2) ∨
      (v = q^5 ∧ r = m*q^3 ∧ len = q^2 ∧ deg = m) :=
    sized.elim (fun h => Or.inl h.2.2) (fun h => Or.inr h.2.2)
  obtain ⟨rows,injective,lengths,free,mass,degree,_⟩ := quadratic_full_three_rows_on_layers F two fits layerShape
  have long (i) : 2 ≤ (rows i).length := (lengths i).2.symm ▸ lLarge
  have present (i) : rows i ≠ [] ∧ (rows i).Nodup :=
    ⟨List.length_pos_iff.mp (lt_of_lt_of_le (by decide) (long i)),(lengths i).1⟩
  obtain ⟨candidate,candidateDistinct,candidateRows,candidateFree,candidateMass⟩ :
      ∃ candidate : Fin p → List (Fin n), Function.Injective candidate ∧
        (∀ i, candidate i ≠ [] ∧ (candidate i).Nodup) ∧ BridgeFree (Before candidate) 3 ∧
        (∑ i, (rows i).length) ≤ ∑ i, (candidate i).length := by
    rcases sized with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    · exact quadraticForwardExact large nBounds.1 pBounds.1 pBounds.2 rows injective present free
    · have pLe : p ≤ n := by
        have scale : 9*q^4 ≤ 8*q^5 := calc
          _ ≤ (8*q)*q^4 := Nat.mul_le_mul_right _ (by omega)
          _ = _ := by ring
        omega
      simpa only [one_mul] using exists_literal_full_disjoint_copies_with_singletons (t := 1)
        rows (fun i => (lengths i).1) long (by decide) free
        (by simpa only [one_mul] using nBounds.1)
        (by simpa only [one_mul] using dims.2.trans pBounds.1)
        (by simpa only [one_mul] using (Nat.sub_le p (m*q^3)).trans pLe)
  obtain ⟨paths,distinct,valid,half,maximal,_,_⟩ := localOrderDistinctExtremal_isDense (k := 3) true hp
    ⟨candidate,candidateDistinct,candidateRows,candidateFree.halfFree⟩
  let M := ∑ i, (paths i).length
  have exactMass : (∑ i, (rows i).length) = W := mass.trans partBalance.2
  have witnessLe : (∑ i, (rows i).length) ≤ M := candidateMass.trans
    (maximal candidate candidateDistinct candidateRows candidateFree.halfFree)
  have lower : W ≤ M := exactMass.symm.trans_le witnessLe
  have upper : M ≤ 4*W := half_three_mass_le_four_near_quadratic_budgets large shape nBounds pBounds paths
    (fun i => (valid i).2) half le_rfl
  have double : q^6 ≤ 2*W := calc
    _ = q^5*q := by ring
    _ ≤ q^5*(2*m) := Nat.mul_le_mul_left _ (by dsimp only [m]; omega)
    _ = _ := by dsimp only [W]; ring
  have capsAt {B b w C : ℕ} (bPos : 0 < b) (fit : B ≤ b) (near : 8*b ≤ 9*C)
      (exactVolume : B*w = W) (scale : C*w ≤ q^6) :
      (M:ℝ)/(4*(b:ℝ)) ≤ w ∧ (w:ℝ) ≤ 4*(M:ℝ)/b := by
    have low : W ≤ b*w := exactVolume.symm.trans_le (Nat.mul_le_mul_right _ fit)
    have high : 8*(b*w) ≤ 9*q^6 := calc
      _ = (8*b)*w := by ring
      _ ≤ (9*C)*w := Nat.mul_le_mul_right _ near
      _ = 9*(C*w) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ scale
    have enough : b*w ≤ 4*M := by omega
    have pos : (0:ℝ) < b := Nat.cast_pos.mpr bPos
    have lowerR : (M:ℝ) ≤ 4*((b:ℝ)*w) := by exact_mod_cast upper.trans (Nat.mul_le_mul_left 4 low)
    have upperR : (b:ℝ)*w ≤ 4*(M:ℝ) := by exact_mod_cast enough
    refine ⟨(div_le_iff₀ (by positivity)).mpr ?_,(le_div_iff₀ pos).mpr ?_⟩
    · convert lowerR using 1
      ring
    · simpa only [mul_comm (w:ℝ)] using upperR
  have caps : frozenListCaps n p M rows := by
    simp only [frozenListCaps,degree,fun i => (lengths i).2]
    exact ⟨fun _ => capsAt hn (dims.1.trans nBounds.1) nBounds.2 partBalance.1 measure.1,
      fun _ => capsAt hp (dims.2.trans pBounds.1) pBounds.2 partBalance.2 measure.2⟩
  exact ⟨paths,distinct,valid,half,maximal,v,dims.1.trans nBounds.1,r,dims.2.trans pBounds.1,
    rows,injective,present,free,exactMass,witnessLe,by rw [exactMass]; exact upper,caps⟩

end OnlineReachabilityPreservers
