import DirectedFlowCutGap.BinaryRational
open DirectedFlowCutGap BinaryArithmetic BinaryRational
namespace BinaryRationalSmoke

def a : Fraction := ⟨[true,true,true,false,true,false,false],
  [false,false,true,true,false],by decide⟩
def b : Fraction := ⟨[true,false,true,false],[true,true,false,false],by decide⟩
def z : Fraction := ⟨[false,false,false],[true,false,true],by decide⟩

#eval do
  match (fromBits a.num a.den).1 with
  | none => throw (IO.userError "positive binary denominator was rejected")
  | some q => if q.num != a.num || q.den != a.den then
      throw (IO.userError "binary input guard changed stored fields")
  match (fromBits a.num [false,false]).1 with
  | none => pure ()
  | some _ => throw (IO.userError "zero binary denominator was accepted")
  let s := BinaryRational.add a b
  let p := BinaryRational.mul a b
  let d := BinaryRational.div a b
  let dz := BinaryRational.div a z
  let cmp := BinaryRational.le a b
  let cmp2 := BinaryRational.le b a
  if value s.1.num != 129 || value s.1.den != 36 then
    throw (IO.userError "binary rational sum lost its unreduced fields")
  if value p.1.num != 115 || value p.1.den != 36 then
    throw (IO.userError "binary rational product failed")
  if value d.1.num != 69 || value d.1.den != 60 then
    throw (IO.userError "binary reciprocal cross-products failed")
  if value dz.1.num != 0 || value dz.1.den != 1 then
    throw (IO.userError "binary zero-divisor fallback failed")
  if cmp.1 || !cmp2.1 || !(BinaryRational.le a a).1 then
    throw (IO.userError "binary rational comparison failed")
  if !(BinaryRational.isZero z).1 || (BinaryRational.isZero a).1 then
    throw (IO.userError "binary numerator zero test failed")
  for r in ([s,p,d,dz] : List (Fraction × ℕ)) do
    let r : Fraction × ℕ := r
    if r.1.num.length != (value r.1.num).size || r.1.den.length != (value r.1.den).size then
      throw (IO.userError "binary arithmetic output was not canonical")
    if r.2 > 2048*8^2 then throw (IO.userError "binary primitive charge envelope exceeded")
  IO.println s!"PASS binary rational padded inputs: sum=129/36 ({s.2} steps), product=115/36 ({p.2}), division=69/60 ({d.2}); zero divisor, exact comparison, canonical lengths and charge envelopes"
end BinaryRationalSmoke
