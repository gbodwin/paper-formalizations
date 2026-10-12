import MinorFreeSpanners.WeightedPathArms

/-! Four internally selected path arms fund their full diameter, all low-degree
incident edges and a baseline reserve. Seven eighths of each old credit fund
diameter; the other eighth pays incident edges. Unit connectors are counted
once through their actual original forest edge identities. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem four_arm_credit {I : Type*} [Fintype I] (H : SimpleGraph I)
    (d credit : I → ℝ) (L D M c b a : ℝ) {x y : I}
    (A : WeightedPathArms H (fun i => d i+1) L (D+1) x)
    (B : WeightedPathArms H (fun i => d i+1) L (D+1) y)
    (hAB : Disjoint A.carrier B.carrier) (hc : 0≤c)
    (hd : ∀ i∈A.carrier∪B.carrier,d i≤D)
    (hcredit : ∀ i∈A.carrier∪B.carrier,c*d i≤credit i)
    (hbase : ∀ i∈A.carrier∪B.carrier,c*b≤credit i)
    (hpay : 8*a≤c*b) (hroom : 15*D+4*M+15+2*b≤6*L) :
    c*(2*(L+D)+M)+a*(A.carrier∪B.carrier).card+c*b/2≤
      (∑ i∈A.carrier∪B.carrier,credit i)+
      c*(internalEdges H A.carrier∪internalEdges H B.carrier).card := by
  classical
  let U := A.carrier∪B.carrier
  let E := internalEdges H A.carrier∪internalEdges H B.carrier
  have hmass : 4*L-2*(D+1)≤∑ i∈U,(d i+1) := by
    have ha := A.mass
    have hb := B.mass
    have hx := hd x (Finset.mem_union_left _ A.center_mem)
    have hy := hd y (Finset.mem_union_right _ B.center_mem)
    dsimp [U]
    rw [Finset.sum_union hAB]
    linarith
  have hea := internalEdges_card_lower H A.carrier A.connected ⟨x,A.center_mem⟩
  have heb := internalEdges_card_lower H B.carrier B.connected ⟨y,B.center_mem⟩
  have hecard : U.card≤E.card+2 := by
    dsimp [U,E]
    rw [Finset.card_union_of_disjoint hAB,
      Finset.card_union_of_disjoint (internalEdges_disjoint H hAB)]
    omega
  have he : (U.card:ℝ)-2≤E.card := by
    have hh : (U.card:ℝ)≤E.card+2 := by exact_mod_cast hecard
    linarith
  have hsum : 7*c*(∑ i∈U,d i)+8*a*U.card≤8*(∑ i∈U,credit i) := by
    have hp : ∀ i∈U,7*c*d i+8*a≤8*credit i := by
      intro i hi
      have hci := hcredit i hi
      have hbi := hbase i hi
      linarith
    calc
      _ = ∑ i∈U,(7*c*d i+8*a) := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ ∑ i∈U,8*credit i := Finset.sum_le_sum hp
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hm : (∑ i∈U,(d i+1))=(∑ i∈U,d i)+U.card := by
    simp [Finset.sum_add_distrib]
  have hmassc := mul_le_mul_of_nonneg_left hmass hc
  have hec := mul_le_mul_of_nonneg_left he hc
  have hroomc := mul_le_mul_of_nonneg_left hroom hc
  have hn : 0≤c*(U.card:ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
  change c*(2*(L+D)+M)+a*U.card+c*b/2≤(∑ i∈U,credit i)+c*E.card
  rw [hm] at hmassc
  nlinarith

end MinorFreeSpanners
