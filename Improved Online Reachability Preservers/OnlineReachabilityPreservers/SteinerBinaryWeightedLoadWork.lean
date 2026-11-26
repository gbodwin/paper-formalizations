import OnlineReachabilityPreservers.SteinerBinaryArithmetic
import OnlineReachabilityPreservers.SteinerWeightedCover

/-! Update the weighted charge and its load numerator with binary operations. -/

namespace OnlineReachabilityPreservers

/-- The charge since the last doubling, its current doubling factor, and
the unnormalized weighted load. The edge cost is fixed separately. -/
structure BinaryWeightedLoad where
  remainder : List Bool
  power : List Bool
  amount : List Bool

def BinaryWeightedLoad.Encodes (row : BinaryWeightedLoad) (cost charge : ℕ) : Prop :=
  binaryWordValue row.remainder = charge%cost ∧ binaryWordValue row.power = 2^(charge/cost) ∧
    binaryWordValue row.amount = weightedLoad cost charge

/-- Start with no charges and the edge cost as the numerator. -/
def binaryWeightedLoadZeroWithWork (cost : List Bool) : BinaryWeightedLoad × ℕ :=
  (⟨[],[true],cost⟩,4)

theorem binaryWeightedLoadZeroWithWork_spec (cost : List Bool) :
    (binaryWeightedLoadZeroWithWork cost).1.Encodes (binaryWordValue cost) 0 ∧
    (binaryWeightedLoadZeroWithWork cost).2 = 4 := by
  change (0 = 0%binaryWordValue cost ∧ 1 = 2^(0/binaryWordValue cost) ∧
    binaryWordValue cost = weightedLoad (binaryWordValue cost) 0) ∧ 4 = 4
  simp [weightedLoad]

/-- A charge adds the current power to the numerator. At the cost boundary,
reset the remainder and double the power for subsequent charges. -/
def chargeBinaryWeightedLoadWithWork (cost : List Bool) (row : BinaryWeightedLoad) : BinaryWeightedLoad × ℕ :=
  let increment := addBinaryWordsWithWork row.remainder [] true
  let load := addBinaryWordsWithWork row.amount row.power false
  let boundary := binaryLessWithWork increment.1 cost false
  let next := if boundary.1 then ⟨increment.1,row.power,load.1⟩ else ⟨[],false::row.power,load.1⟩
  (next,increment.2+load.2+boundary.2+8)

def chargeBinaryWeightedLoadWorkBudget (cost remainder power amount : ℕ) : ℕ :=
  (20*remainder+5)+(20*(amount+power)+5)+(14*(remainder+1+cost)+4)+8

/-- The binary update implements a single charge on the exact weighted
load, including the rollover. The allowance tracks the supplied widths. -/
theorem chargeBinaryWeightedLoadWithWork_spec (costWord : List Bool) (charge : ℕ) (row : BinaryWeightedLoad)
    (positive : 0 < binaryWordValue costWord) (encoded : row.Encodes (binaryWordValue costWord) charge) :
    let out := chargeBinaryWeightedLoadWithWork costWord row
    out.1.Encodes (binaryWordValue costWord) (charge+1) ∧
      out.1.remainder.length ≤ row.remainder.length+1 ∧ out.1.power.length ≤ row.power.length+1 ∧
      out.1.amount.length ≤ row.amount.length+row.power.length+1 ∧
      out.2 ≤ chargeBinaryWeightedLoadWorkBudget costWord.length row.remainder.length row.power.length row.amount.length := by
  generalize costEq : binaryWordValue costWord = cost at positive encoded ⊢
  let increment := addBinaryWordsWithWork row.remainder [] true
  let load := addBinaryWordsWithWork row.amount row.power false
  let boundary := binaryLessWithWork increment.1 costWord false
  obtain ⟨remValue,powerValue,amountValue⟩ := encoded
  obtain ⟨nextRem,remWidth,remWork⟩ := addBinaryWordsWithWork_spec row.remainder [] true
  obtain ⟨nextAmount,amountWidth,amountWork⟩ := addBinaryWordsWithWork_spec row.amount row.power false
  obtain ⟨tested,testWork⟩ := binaryLessWithWork_noBorrow_spec increment.1 costWord
  change binaryWordValue increment.1 = binaryWordValue row.remainder+0+1 at nextRem
  change binaryWordValue load.1 = binaryWordValue row.amount+binaryWordValue row.power+0 at nextAmount
  change increment.1.length ≤ row.remainder.length+0+1 at remWidth
  change increment.2 ≤ 20*(row.remainder.length+0)+5 at remWork
  change load.1.length ≤ row.amount.length+row.power.length+1 at amountWidth
  change load.2 ≤ 20*(row.amount.length+row.power.length)+5 at amountWork
  change boundary.1 = decide (binaryWordValue increment.1 < binaryWordValue costWord) at tested
  change boundary.2 ≤ 14*(increment.1.length+costWord.length)+4 at testWork
  rw [remValue,Nat.add_zero] at nextRem
  rw [amountValue,powerValue,Nat.add_zero,← weightedLoad_succ positive charge] at nextAmount
  rw [nextRem,costEq] at tested
  have enough : increment.2+load.2+boundary.2+8 ≤
      chargeBinaryWeightedLoadWorkBudget costWord.length row.remainder.length row.power.length row.amount.length := by
    unfold chargeBinaryWeightedLoadWorkBudget
    omega
  have splitCharge := Nat.mod_add_div charge cost
  have remSmall := Nat.mod_lt charge positive
  let next := if boundary.1 then (⟨increment.1,row.power,load.1⟩ : BinaryWeightedLoad) else ⟨[],false::row.power,load.1⟩
  change next.Encodes cost (charge+1) ∧ next.remainder.length ≤ row.remainder.length+1 ∧
    next.power.length ≤ row.power.length+1 ∧ next.amount.length ≤ row.amount.length+row.power.length+1 ∧
    increment.2+load.2+boundary.2+8 ≤ _
  dsimp only [next]
  by_cases before : charge%cost+1 < cost
  · have on : boundary.1 = true := tested.trans (decide_eq_true before)
    have qr : (charge+1)/cost = charge/cost ∧ (charge+1)%cost = charge%cost+1 :=
      (Nat.div_mod_unique positive).mpr ⟨by omega,before⟩
    simp only [on,ite_true]
    refine ⟨⟨?_,?_,nextAmount⟩,by omega,Nat.le_succ _,amountWidth,enough⟩
    · exact nextRem.trans qr.2.symm
    · rwa [qr.1]
  · have off : boundary.1 = false := tested.trans (decide_eq_false before)
    have last : charge%cost+1 = cost := by omega
    have qr : (charge+1)/cost = charge/cost+1 ∧ (charge+1)%cost = 0 :=
      (Nat.div_mod_unique positive).mpr ⟨by rw [Nat.mul_add,Nat.mul_one]; omega,positive⟩
    simp only [off,Bool.false_eq_true,ite_false]
    refine ⟨⟨qr.2.symm,?_,nextAmount⟩,Nat.zero_le _,le_rfl,amountWidth,enough⟩
    change 0+2*binaryWordValue row.power = 2^((charge+1)/cost)
    rw [powerValue,qr.1,pow_succ',Nat.zero_add]

end OnlineReachabilityPreservers
