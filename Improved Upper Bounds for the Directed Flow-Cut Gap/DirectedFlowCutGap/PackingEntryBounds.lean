import DirectedFlowCutGap.PackingEntryExecution

namespace DirectedFlowCutGap.PackingEntry
open BinaryArithmetic BinaryRational BinaryFractionalRows

def instructionBound (B : ℕ) : ℕ := 22000*(4*(2*B+7)+2)^2+35

theorem widths (ci amount y : Fraction) (B : ℕ)
    (hc : StoredBounded ci B) (ha : StoredBounded amount B) (hy : StoredBounded y B) :
    StoredBounded (doubled ci) (B+3) ∧ StoredBounded (quotient ci amount) (2*B+4) ∧
      StoredBounded (factor ci amount) (2*B+7) ∧ StoredBounded (result ci amount y) (3*B+8) := by
  have htwo : StoredBounded two 2 := by simp [StoredBounded,two]
  have hone : StoredBounded one 1 := by simp [StoredBounded,one]
  have hd := mul_stored_bounded (stored_raw_bound htwo) (stored_raw_bound hc)
  have hd' : StoredBounded (doubled ci) (B+3) := by
    simpa only [doubled,show 2+B+1=B+3 by omega] using hd
  have hq := div_stored_bounded (stored_raw_bound ha) (stored_raw_bound hd')
  have hq' : StoredBounded (quotient ci amount) (2*B+4) := by
    simpa only [quotient,show B+(B+3)+1=2*B+4 by omega] using hq
  have hf := add_stored_bounded (stored_raw_bound hone) (stored_raw_bound hq')
  have hf' : StoredBounded (factor ci amount) (2*B+7) := by
    simpa only [factor,show 1+(2*B+4)+2=2*B+7 by omega] using hf
  have hr := mul_stored_bounded (stored_raw_bound hy) (stored_raw_bound hf')
  refine ⟨hd',hq',hf',?_⟩
  simpa only [result,show B+(2*B+7)+1=3*B+8 by omega] using hr

theorem steps_bound (ci amount y : Fraction) (B : ℕ)
    (hc : StoredBounded ci B) (ha : StoredBounded amount B) (hy : StoredBounded y B) :
    steps ci amount y ≤ instructionBound B := by
  obtain ⟨hd,hq,hf,_⟩ := widths ci amount y B hc ha hy
  let K := 2*B+7
  have lift (x : Fraction) (N : ℕ) (hx : StoredBounded x N) (hn : N≤K) :
      StoredBounded x K := ⟨hx.1.trans hn,hx.2.trans hn⟩
  have twoK : StoredBounded two K := lift two 2 (by simp [StoredBounded,two]) (by dsimp [K];omega)
  have oneK : StoredBounded one K := lift one 1 (by simp [StoredBounded,one]) (by dsimp [K];omega)
  have ciK := lift ci B hc (by dsimp [K];omega)
  have amountK := lift amount B ha (by dsimp [K];omega)
  have yK := lift y B hy (by dsimp [K];omega)
  have doubledK := lift (doubled ci) (B+3) hd (by dsimp [K];omega)
  have quotientK := lift (quotient ci amount) (2*B+4) hq (by dsimp [K];omega)
  have size (x z : Fraction) (hx : StoredBounded x K) (hz : StoredBounded z K) :
      CanonicalRationalProduct.inputSize x z≤4*K+2 := by
    have a:=hx.1;have b:=hx.2;have c:=hz.1;have d:=hz.2
    unfold CanonicalRationalProduct.inputSize
    omega
  have p := CanonicalRationalProduct.instructions_bound two ci
  have q := CanonicalRationalQuotient.steps_bound amount (doubled ci)
  have a := CanonicalRationalAddition.instructions_bound one (quotient ci amount)
  have m := CanonicalRationalProduct.instructions_bound y (factor ci amount)
  have ps := size two ci twoK ciK
  have qs := size amount (doubled ci) amountK doubledK
  have has := size one (quotient ci amount) oneK quotientK
  have ms := size y (factor ci amount) yK hf
  have pp : 500*CanonicalRationalProduct.inputSize two ci^2≤500*(4*K+2)^2 := by gcongr
  have qq : 600*CanonicalRationalQuotient.inputSize amount (doubled ci)^2≤600*(4*K+2)^2 := by
    change 600*CanonicalRationalProduct.inputSize amount (doubled ci)^2≤_
    gcongr
  have aa : 20000*CanonicalRationalAddition.inputSize one (quotient ci amount)^2≤20000*(4*K+2)^2 := by
    change 20000*CanonicalRationalProduct.inputSize one (quotient ci amount)^2≤_
    gcongr
  have mm : 500*CanonicalRationalProduct.inputSize y (factor ci amount)^2≤500*(4*K+2)^2 := by gcongr
  unfold steps instructionBound
  change _≤22000*(4*K+2)^2+35
  omega
end DirectedFlowCutGap.PackingEntry
