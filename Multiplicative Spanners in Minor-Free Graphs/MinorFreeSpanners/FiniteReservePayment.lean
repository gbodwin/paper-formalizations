import MinorFreeSpanners.BranchingReserveSelection

/-! Conserved low-degree payment from a bounded reserve set and one actual
surplus vertex. Half of that surplus baseline is retained for later absorption. -/
namespace MinorFreeSpanners
open Finset

 theorem finite_reserve_payment {I : Type*} (S R : Finset I) (z : I)
    (credit : I → ℝ) (c b a bridge radius : ℝ) (s : ℕ)
    (hRS : R⊆S) (hRcard : R.card≤s) (hzS : z∈S) (hzR : z∉R)
    (ha : 0≤a) (hbase : ∀ i∈S,c*b≤credit i)
    (hcost : (s+1:ℕ)*a≤c*b/2)
    (hreserve : c*radius≤(∑ i∈R,credit i)+bridge) :
    c*radius+a*S.card+c*b/2≤(∑ i∈S,credit i)+bridge := by
  classical
  let U := S\R
  let W := U.erase z
  have hzU : z∈U := Finset.mem_sdiff.mpr ⟨hzS,hzR⟩
  have hWS : W⊆S := (Finset.erase_subset z U).trans Finset.sdiff_subset
  have hcount := Finset.card_sdiff_of_subset hRS
  have herase := Finset.card_erase_of_mem hzU
  have hRSc := Finset.card_le_card hRS
  have hUpos := Finset.card_pos.mpr ⟨z,hzU⟩
  have hcard : S.card=R.card+W.card+1 := by dsimp [W,U] at *;omega
  have hcardR : (S.card:ℝ)=R.card+W.card+1 := by exact_mod_cast hcard
  have hsplus : (1:ℝ)≤(s+1:ℕ) := by exact_mod_cast Nat.succ_pos s
  have haBase : a≤c*b := by
    have hh := mul_le_mul_of_nonneg_right hsplus ha
    nlinarith
  have hWsum : (W.card:ℝ)*a≤∑ i∈W,credit i := by
    calc
      _ = ∑ _i∈W,a := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => haBase.trans (hbase i (hWS hi))
  have hzcredit := hbase z hzS
  have hRs : (R.card:ℝ)≤s := by exact_mod_cast hRcard
  have hRcharge : ((R.card:ℝ)+1)*a≤c*b/2 := by
    have hm := mul_le_mul_of_nonneg_right (add_le_add_right hRs 1) ha
    push_cast at hcost
    nlinarith only [hm,hcost]
  have hsumS := Finset.sum_sdiff (f:=credit) hRS
  have hsumU := Finset.sum_erase_add U credit hzU
  change (∑ i∈U,credit i)+(∑ i∈R,credit i)=∑ i∈S,credit i at hsumS
  change (∑ i∈W,credit i)+credit z=∑ i∈U,credit i at hsumU
  nlinarith

 theorem branching_core_credit {I : Type*} [Fintype I]
    (H : SimpleGraph I) (hH : H.IsAcyclic) (d credit : I → ℝ)
    (S : Finset I) (L D c b a : ℝ) (s : ℕ)
    (hcore : BranchingCore H (fun i => d i+1) L (D+1) S)
    (hc : 0≤c) (ha : 0≤a) (hd1 : ∀ i∈S,1≤d i)
    (hcred : ∀ i∈S,c*d i≤credit i) (hbase : ∀ i∈S,c*b≤credit i)
    (hsize : L+D≤s*b) (hcost : (s+1:ℕ)*a≤c*b/2) :
    ∃ radius : ℝ,0≤radius ∧ L-1≤radius ∧ radius≤L+D ∧
      (∀ i j,∀ p : H.Walk i j,p.IsPath →
        (∀ v∈p.support,v∈S) → pathMass d p+p.length≤radius) ∧
      c*radius+a*S.card+c*b/2≤(∑ i∈S,credit i)+c*(internalEdges H S).card := by
  obtain ⟨R,z,hz,radius,hr,hrD,hRS,hRcard,hzR,hbound,hreserve⟩ :=
    branching_reserve_selection H hH d credit S L D c b s hcore hc hd1 hcred hbase hsize
  have hrL : L-1≤radius := by
    obtain ⟨i,j,p,hp,hps,hL⟩ := hcore.2.2.1
    have hb := hbound i j p hp hps
    rw [pathMass_add_one d p hp] at hL
    linarith
  exact ⟨radius,hr,hrL,hrD,hbound,finite_reserve_payment S R z credit c b a _ radius s
    hRS hRcard hz hzR ha hbase hcost hreserve⟩

end MinorFreeSpanners
