import DirectedFlowCutGap.EncodedEdgeLineInput
import DirectedFlowCutGap.BinaryDivision
import DirectedFlowCutGap.BinaryNaturalView
import DirectedFlowCutGap.BinaryVertexReductionArithmetic

/-! Precompute the line graph's typed labels once, using charged binary
comparisons, offsets and quotient/remainder. -/
namespace DirectedFlowCutGap.BinaryLineLabels

open BinaryArithmetic EncodedEdgeLineInput
open EdgeLineReduction (Node)
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)

private def coordinates (word radix : Bits) : (ℕ × ℕ) × ℕ :=
  let result := BinaryDivision.divide word radix
  let first := BinaryNaturalView.decode result.quotient
  let last := BinaryNaturalView.decode result.remainder
  ((first.1,last.1),result.steps+first.2+last.2+4)

private theorem coordinates_value (word radix : Bits) :
    (coordinates word radix).1=(value word/value radix,value word%value radix) := by
  have h := BinaryDivision.divide_spec word radix
  simp only [coordinates,BinaryNaturalView.decode_value,h.1,h.2.1]

private theorem port_index {n : ℕ} (i : Fin (lineSize n)) (port : i.val<n*2) :
    index n i=.inl (⟨i.val/2,(Nat.div_lt_iff_lt_mul (by decide)).mpr port⟩,i.val%2==1) := by
  apply (index n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  change i.val = ((finTwoEquiv.symm (i.val%2==1)).val+2*(i.val/2))
  have q := Nat.mod_add_div i.val 2
  have rem := Nat.mod_lt i.val (show 0 < 2 by decide)
  by_cases h : i.val%2=1 <;> simp [finTwoEquiv,h] <;> omega

private theorem arc_index {n : ℕ} (i : Fin (lineSize n)) (arc : n*2 ≤ i.val) (hn : 0<n) :
    let shift := i.val-n*2
    let inRange : shift<n*n := by have h := i.isLt; unfold lineSize at h; omega
    index n i=.inr (⟨shift/n,(Nat.div_lt_iff_lt_mul hn).mpr inRange⟩,⟨shift%n,Nat.mod_lt _ hn⟩) := by
  dsimp only
  apply (index n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  change i.val = n*2 + ((i.val-n*2)%n+n*((i.val-n*2)/n))
  rw [Nat.mod_add_div]
  omega

private def locate {n : ℕ} (divisor ports : Bits) (hn : value divisor=n) (hp : value ports=n*2)
    (i : Fin (lineSize n)) : Node (Fin n) × ℕ :=
  let input := BinaryNaturalView.encode i.val
  let zone := lessEqual ports input.1
  have input_value : value input.1=i.val := BinaryNaturalView.encode_value _
  if arc : zone.1=true then
    let position := BinaryDivision.sub input.1 ports
    let c := coordinates position.1 divisor
    have loc := coordinates_value position.1 divisor
    have offset : value position.1=i.val-n*2 := by rw [(BinaryDivision.sub_spec ..).1,input_value,hp]
    have hn0 : 0<n := by
      by_contra h
      have zero : n=0 := by omega
      have o := i.isLt
      simp [zero,lineSize] at o
    have ge : n*2 ≤ i.val := by
      have once := (lessEqual_spec ports input.1).1.mp arc
      rwa [hp,input_value] at once
    have good : i.val-n*2 < n*n := by have h := i.isLt; unfold lineSize at h; omega
    have hFirst : c.1.1<n := by
      change (coordinates position.1 divisor).1.1<n
      rw [loc,offset,hn]
      exact (Nat.div_lt_iff_lt_mul hn0).mpr good
    have hLast : c.1.2<n := by
      change (coordinates position.1 divisor).1.2<n
      rw [loc,hn]
      exact Nat.mod_lt _ hn0
    (.inr (⟨c.1.1,hFirst⟩,⟨c.1.2,hLast⟩),input.2+zone.2+position.2+c.2+8)
  else
    let c := coordinates input.1 [false,true]
    have less : i.val<n*2 := by
      have h := (lessEqual_spec ports input.1).1
      rw [hp,input_value] at h
      exact Nat.lt_of_not_ge (fun ge => arc (h.mpr ge))
    have within : c.1.1<n := by
      have h := coordinates_value input.1 [false,true]
      change (coordinates input.1 [false,true]).1.1<n
      rw [h,input_value]
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr less
    (.inl (⟨c.1.1,within⟩,c.1.2==1),input.2+zone.2+c.2+8)

theorem locate_value {n : ℕ} (divisor ports : Bits) (hn : value divisor=n) (hp : value ports=n*2)
    (i : Fin (lineSize n)) : (locate divisor ports hn hp i).1=index n i := by
  let x := (BinaryNaturalView.encode i.val).1
  have vx : value x=i.val := BinaryNaturalView.encode_value _
  have zone : (lessEqual ports x).1=true ↔ n*2 ≤ i.val := by rw [(lessEqual_spec ..).1,hp,vx]
  unfold locate
  dsimp only
  split
  · rename_i arc
    have yes : n*2 ≤ i.val := zone.mp arc
    have npos : 0<n := by
      by_contra h
      have zero : n=0 := by omega
      have hi := i.isLt
      simp [zero,lineSize] at hi
    rw [arc_index i yes npos]
    have h := coordinates_value (BinaryDivision.sub x ports).1 divisor
    rw [(BinaryDivision.sub_spec x ports).1,vx,hp,hn] at h
    exact congrArg Sum.inr (Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h)))
  · rename_i port
    have yes : i.val < n*2 := Nat.lt_of_not_ge (fun ge => port (zone.mpr ge))
    rw [port_index i yes]
    have h := coordinates_value x [false,true]
    rw [vx] at h
    exact congrArg Sum.inl (Prod.ext (Fin.ext (congrArg Prod.fst h)) (congrArg (fun pair : ℕ×ℕ => pair.2==1) h))

private theorem coordinates_paid {word radix : Bits} {W : ℕ}
    (wide : word.length ≤ W) (rad : radix.length ≤ W) (num : value word ≤ W) :
    (coordinates word radix).2 ≤ 1100*(W+1)^2 := by
  let x := BinaryDivision.divide word radix
  have d := BinaryDivision.divide_charge_bound wide rad
  have h := BinaryDivision.divide_spec word radix
  have q : x.quotient.length ≤ W := h.2.2.1.trans_le
    ((BinaryNaturalOperations.size_le_self _).trans ((Nat.div_le_self ..).trans num))
  have r : x.remainder.length ≤ W := h.2.2.2.trans_le
    ((BinaryNaturalOperations.size_le_self _).trans ((Nat.mod_le ..).trans num))
  have a := (BinaryNaturalView.decode_paid x.quotient).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right q 1) 2))
  have b := (BinaryNaturalView.decode_paid x.remainder).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right r 1) 2))
  change x.steps+(BinaryNaturalView.decode x.quotient).2+(BinaryNaturalView.decode x.remainder).2+4 ≤ _
  change x.steps ≤ _ at d
  nlinarith

private theorem locate_paid {n : ℕ} (divisor ports : Bits) (hn : value divisor=n) (hp : value ports=n*2)
    (i : Fin (lineSize n)) {W : ℕ} (divisorFit : divisor.length ≤ W) (portsFit : ports.length ≤ W)
    (size : lineSize n ≤ W) (pad : 2 ≤ W) : (locate divisor ports hn hp i).2 ≤ 2048*(W+1)^2 := by
  let x := BinaryNaturalView.encode i.val
  let z := lessEqual ports x.1
  have xv : value x.1=i.val := BinaryNaturalView.encode_value _
  have inRange : i.val ≤ W := i.isLt.le.trans size
  have len : x.1.length ≤ W := by
    rw [show x.1=i.val.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]
    exact (BinaryNaturalOperations.size_le_self _).trans inRange
  have p := (BinaryNaturalView.encode_paid i.val).trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (Nat.add_le_add_right ((BinaryNaturalOperations.size_le_self _).trans inRange) 1) 2))
  have c := (lessEqual_spec ports x.1).2.trans (Nat.mul_le_mul_left 17 (Nat.add_le_add_right (max_le portsFit len) 1))
  change x.2 ≤ _ at p
  change z.2 ≤ _ at c
  unfold locate
  dsimp only
  split
  · let d := BinaryDivision.sub x.1 ports
    have prop := BinaryDivision.sub_spec x.1 ports
    have dv : value d.1 ≤ W := prop.1.trans_le ((Nat.sub_le ..).trans (xv.trans_le inRange))
    have dl : d.1.length ≤ W := prop.2.1.trans_le
      ((BinaryNaturalOperations.size_le_self _).trans ((Nat.sub_le ..).trans (xv.trans_le inRange)))
    have dp : d.2 ≤ 64*(W+W+1) := prop.2.2.trans (Nat.mul_le_mul_left 64 (by gcongr))
    have div := coordinates_paid dl divisorFit dv
    change x.2+z.2+d.2+(coordinates d.1 divisor).2+8 ≤ _
    change (coordinates d.1 divisor).2 ≤ 1100*(W+1)^2 at div
    nlinarith only [p,c,dp,div]
  · have div := coordinates_paid len (show ([false,true] : Bits).length ≤ W from pad) (xv.trans_le inRange)
    change x.2+z.2+(coordinates x.1 [false,true]).2+8 ≤ _
    change (coordinates x.1 [false,true]).2 ≤ 1100*(W+1)^2 at div
    nlinarith only [p,c,div]

def labels (n : ℕ) : Vector (Node (Fin n)) (lineSize n) × ℕ :=
  let word := BinaryNaturalView.encode n
  let ports := false::word.1
  have nword : value word.1=n := BinaryNaturalView.encode_value n
  have twice : value ports=n*2 := by simp only [ports,value,Bool.toNat_false,zero_add,nword,Nat.mul_comm]
  let out := batch (locate word.1 ports nword twice)
  (out.1,word.2+out.2+8)

theorem labels_value (n : ℕ) : (labels n).1=Vector.ofFn (index n) := by
  simp only [labels,batch_value,locate_value]

def budget {R : Type*} [Semiring R] (n m : R) : R :=
  16*(n+1)^2+m*(2048*(m+3)^2)+8*m+12

theorem labels_paid (n : ℕ) : (labels n).2 ≤ budget n (lineSize n) := by
  let word := BinaryNaturalView.encode n
  let ports := false::word.1
  have nword : value word.1=n := BinaryNaturalView.encode_value _
  have twice : value ports=n*2 := by simp only [ports,value,Bool.toNat_false,zero_add,nword,Nat.mul_comm]
  let m := lineSize n
  have hn : n ≤ m := by unfold m lineSize; omega
  have words : word.1.length ≤ n := by
    rw [show word.1=n.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]
    exact BinaryNaturalOperations.size_le_self _
  have divs : word.1.length ≤ m+2 := words.trans (hn.trans (by omega))
  have p : ports.length ≤ m+2 := by unfold ports; simp only [List.length_cons]; omega
  have paid := batch_paid (locate word.1 ports nword twice)
    (fun i => locate_paid word.1 ports nword twice i divs p (Nat.le_add_right ..) (by omega))
  have framing := (BinaryNaturalView.encode_paid n).trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (Nat.add_le_add_right (BinaryNaturalOperations.size_le_self _) 1) 2))
  change word.2+(batch (locate word.1 ports nword twice)).2+8 ≤ budget n m
  change word.2 ≤ _ at framing
  change (batch (locate word.1 ports nword twice)).2 ≤ m*(2048*(m+3)^2)+8*m+4 at paid
  unfold budget
  omega

open EdgeLineReduction (departs base)
open RawNonnegativeRational (Code)
open EncodedVertexSolver (GraphInput)

private def adjacent {n : ℕ} (D : Input n) (origin : Node (Fin n)) : Node (Fin n) → Bool
  | .inl (v,false) => departs origin && decide (base origin=v)
  | .inl (_,true) => false
  | .inr (u,v) => departs origin && decide (base origin=u) && D.adjacency[u.val][v.val]

private def price {n : ℕ} (D : Input n) : Node (Fin n) → Code
  | .inl _ => Code.zero
  | .inr (u,v) => if D.adjacency[u.val][v.val] then D.costs[u.val][v.val] else Code.zero

private def endpoint {n : ℕ} (tag : Bool) (i : Fin n) : Fin (lineSize n) × ℕ :=
  let word := BinaryNaturalView.encode i.val
  let label := BinaryNaturalView.decode (tag::word.1)
  have same : label.1=tag.toNat+2*i.val := by
    rw [BinaryNaturalView.decode_value,value,BinaryNaturalView.encode_value]
  have inside : label.1<lineSize n := by
    rw [same,lineSize]
    have hi := i.isLt
    cases tag <;> simp only [Bool.toNat_false,Bool.toNat_true,zero_add] <;> omega
  (⟨label.1,inside⟩,word.2+label.2+2)

private theorem endpoint_value {n : ℕ} (tag : Bool) (i : Fin n) :
    (endpoint tag i).1=(index n).symm (.inl (i,tag)) := by
  apply Fin.ext
  change (BinaryNaturalView.decode (tag::(BinaryNaturalView.encode i.val).1)).1 =
    (finTwoEquiv.symm tag).val+2*i.val
  rw [BinaryNaturalView.decode_value,value,BinaryNaturalView.encode_value]
  cases tag <;> rfl

private theorem endpoint_paid {n : ℕ} (tag : Bool) (i : Fin n) :
    (endpoint tag i).2 ≤ 48*(n+2)^2 := by
  let word := BinaryNaturalView.encode i.val
  have size : i.val.size ≤ n := (BinaryNaturalOperations.size_le_self _).trans i.isLt.le
  have len : word.1.length ≤ n := by
    rw [show word.1=i.val.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]
    exact size
  have a := (BinaryNaturalView.encode_paid i.val).trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (show i.val.size+1 ≤ n+2 by omega) 2))
  have b := (BinaryNaturalView.decode_paid (tag::word.1)).trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (show (tag::word.1).length+1 ≤ n+2 by rw [List.length_cons]; omega) 2))
  change word.2+(BinaryNaturalView.decode (tag::word.1)).2+2 ≤ _
  change word.2 ≤ 16*(n+2)^2 at a
  have pos : 1 ≤ (n+2)^2 := Nat.one_le_pow _ _ (by omega)
  omega

private def demandRows {n : ℕ} : List (Fin n × Fin n) → List (Fin (lineSize n) × Fin (lineSize n)) × ℕ
  | [] => ([],2)
  | (s,t)::rest =>
    let entry := endpoint true s
    let exit := endpoint false t
    let table := demandRows rest
    ((entry.1,exit.1)::table.1,entry.2+exit.2+table.2+8)

private theorem demandRows_value {n : ℕ} (D : List (Fin n × Fin n)) :
    (demandRows D).1=D.map (fun (s,t) => (source s,sink t)) := by
  induction D with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨s,t⟩
    simp only [demandRows,List.map_cons,endpoint_value,ih]
    rfl

def demandBudget {R : Type*} [Semiring R] (n d : R) : R :=
  d*(96*(n+2)^2+8)+2

private theorem demandRows_paid {n : ℕ} (D : List (Fin n × Fin n)) :
    (demandRows D).2 ≤ demandBudget n D.length := by
  induction D with
  | nil => simp [demandRows,demandBudget]
  | cons head rest ih =>
    rcases head with ⟨s,t⟩
    have a := endpoint_paid true s
    have b := endpoint_paid false t
    simp only [demandRows,List.length_cons,demandBudget,Nat.add_mul,Nat.one_mul] at *
    omega

def prepare {n : ℕ} (D : Input n) : GraphInput (lineSize n) × ℕ :=
  let data := labels n
  let node := fun i : Fin (lineSize n) => data.1[i.val]
  let demanded := demandRows D.demands
  (⟨Vector.ofFn (fun i => Vector.ofFn fun j => adjacent D (node i) (node j)),
    demanded.1,Vector.ofFn (fun i => price D (node i))⟩,data.2+demanded.2)

@[simp] theorem prepare_value {n : ℕ} (D : Input n) : (prepare D).1=lineInput D := by
  simp only [prepare,labels_value,Vector.getElem_ofFn,demandRows_value]
  rfl

theorem prepare_paid {n : ℕ} (D : Input n) :
    (prepare D).2 ≤ budget (lineSize n) (lineSize n)+demandBudget (lineSize n) D.demands.length := by
  apply (Nat.add_le_add (labels_paid n) (demandRows_paid D.demands)).trans
  have h : n ≤ lineSize n := by unfold lineSize; omega
  unfold budget demandBudget
  gcongr

open Polynomial in
theorem budget_eval (a b : Polynomial ℕ) (x : ℕ) : (budget a b).eval x=budget (a.eval x) (b.eval x) := by
  simp only [budget,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

open Polynomial in
theorem demandBudget_eval (a b : Polynomial ℕ) (x : ℕ) :
    (demandBudget a b).eval x=demandBudget (a.eval x) (b.eval x) := by
  simp only [demandBudget,eval_add,eval_mul,eval_pow,eval_ofNat]

end DirectedFlowCutGap.BinaryLineLabels
