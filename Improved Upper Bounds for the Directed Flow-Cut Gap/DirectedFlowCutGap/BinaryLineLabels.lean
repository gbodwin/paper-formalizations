import DirectedFlowCutGap.EncodedEdgeLineInput
import DirectedFlowCutGap.BinaryDivision
import DirectedFlowCutGap.BinaryNaturalView
import DirectedFlowCutGap.BinaryVertexReductionArithmetic
import DirectedFlowCutGap.BinaryEdgeGadget
import DirectedFlowCutGap.BinaryVectorAccess

/-! Build the indexed line graph with charged binary labels, adjacency
tests, demand coordinates and data movement. -/
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

def labelsWithControl (n : ℕ) : (Vector (Node (Fin n)) (lineSize n) × ℕ) × ℕ :=
  let word := BinaryNaturalView.encode n
  let ports := false::word.1
  have nword : value word.1=n := BinaryNaturalView.encode_value n
  have twice : value ports=n*2 := by simp only [ports,value,Bool.toNat_false,zero_add,nword,Nat.mul_comm]
  let out := BinaryArrayBatch.run (locate word.1 ports nword twice)
  ((out.1.1,word.2+out.1.2+8),out.2)

def labels (n : ℕ) : Vector (Node (Fin n)) (lineSize n) × ℕ := (labelsWithControl n).1

theorem labels_value (n : ℕ) : (labels n).1=Vector.ofFn (index n) := by
  simp only [labels,labelsWithControl,BinaryArrayBatch.run_value,locate_value]

def budget {R : Type*} [Semiring R] (n m : R) : R :=
  16*(n+1)^2+m*(2048*(m+3)^2)+8*m+12

private theorem labels_bounds (n : ℕ) : (labels n).2 ≤ budget n (lineSize n) ∧
    (labelsWithControl n).2 ≤ BinaryArrayBatch.childCeiling (lineSize n) (2048*(lineSize n+3)^2) 0 := by
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
  have callback (i : Fin m) : (locate word.1 ports nword twice i).2 ≤ 2048*(m+3)^2 :=
    locate_paid word.1 ports nword twice i divs p (Nat.le_add_right ..) (by omega)
  have paid := batch_paid (locate word.1 ports nword twice) callback
  have framing := (BinaryNaturalView.encode_paid n).trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (Nat.add_le_add_right (BinaryNaturalOperations.size_le_self _) 1) 2))
  constructor
  · change word.2+(batch (locate word.1 ports nword twice)).2+8 ≤ budget n m
    change word.2 ≤ _ at framing
    change (batch (locate word.1 ports nword twice)).2 ≤ m*(2048*(m+3)^2)+8*m+4 at paid
    unfold budget
    omega
  · exact (BinaryArrayBatch.run_paid _ callback).trans (BinaryArrayBatch.childBudget_le m _ 0)

theorem labels_paid (n : ℕ) : (labels n).2 ≤ budget n (lineSize n) := (labels_bounds n).1

def labelControlBudget {R : Type*} [Semiring R] (m : R) : R :=
  BinaryArrayBatch.childCeiling m (2048*(m+3)^2) 0

theorem labels_control_paid (n : ℕ) : (labelsWithControl n).2 ≤ labelControlBudget (lineSize n) :=
  (labels_bounds n).2

open EdgeLineReduction (departs base)
open RawNonnegativeRational (Code)
open EncodedVertexSolver (GraphInput)
open BinaryEdgeGadget (equalFin equalFin_value equalFin_paid)

private def departTo {n : ℕ} (origin : Node (Fin n)) (v : Fin n) : Bool × ℕ :=
  if departs origin then
    let same := equalFin (base origin) v
    (same.1,same.2+4)
  else (false,2)

private theorem departTo_iff {n : ℕ} (origin : Node (Fin n)) (v : Fin n) :
    (departTo origin v).1=true ↔ departs origin=true ∧ base origin=v := by
  unfold departTo
  split <;> simp_all [equalFin_value]

private theorem departTo_paid {n : ℕ} (origin : Node (Fin n)) (v : Fin n) :
    (departTo origin v).2 ≤ 64*(n+1)^2+4 := by
  have paid := equalFin_paid (base origin) v
  unfold departTo
  split <;> dsimp only <;> omega

private def adjacent {n : ℕ} (D : Input n) (origin : Node (Fin n)) : Node (Fin n) → Bool × ℕ
  | .inl (v,false) => departTo origin v
  | .inl (_,true) => (false,2)
  | .inr (u,v) =>
    if D.adjacency[u.val][v.val] then
      let reach := departTo origin u
      (reach.1,reach.2+4)
    else (false,4)

private theorem adjacent_iff {n : ℕ} (D : Input n) (origin target : Node (Fin n)) :
    (adjacent D origin target).1=true ↔ (EdgeLineReduction.graph D.graph).Adj origin target := by
  rcases target with ⟨v,side⟩ | ⟨u,v⟩
  · cases side <;> simp [adjacent,departTo_iff,EdgeLineReduction.graph,EdgeLineReduction.adjacency]
  · simp only [adjacent,EdgeLineReduction.graph,EdgeLineReduction.adjacency,Input.graph]
    split <;> simp_all [departTo_iff]

private theorem adjacent_paid {n : ℕ} (D : Input n) (origin target : Node (Fin n)) :
    (adjacent D origin target).2 ≤ 64*(n+1)^2+8 := by
  rcases target with ⟨v,side⟩ | ⟨u,v⟩
  · have paid := departTo_paid origin v
    cases side <;> simp only [adjacent] <;> omega
  · have paid := departTo_paid origin u
    simp only [adjacent]
    split <;> dsimp only <;> omega

private def price {n : ℕ} (D : Input n) : Node (Fin n) → Code × ℕ
  | .inl _ => (Code.zero,2)
  | .inr (u,v) => (if D.adjacency[u.val][v.val] then D.costs[u.val][v.val] else Code.zero,4)

private theorem price_paid {n : ℕ} (D : Input n) (node : Node (Fin n)) :
    (price D node).2 ≤ 4 := by
  rcases node with port | ⟨u,v⟩ <;> simp [price]

private def adjacentWithControl {n : ℕ} (D : Input n) (origin : Node (Fin n)) : Node (Fin n) → (Bool × ℕ) × ℕ
  | .inl port => (adjacent D origin (.inl port),0)
  | .inr (u,v) =>
    let present := BinaryVectorAccess.readMatrix D.adjacency u v
    if present.1 then
      let reach := departTo origin u
      ((reach.1,reach.2+4),present.2)
    else ((false,4),present.2)

private theorem adjacentWithControl_value {n : ℕ} (D : Input n) (origin target : Node (Fin n)) :
    (adjacentWithControl D origin target).1=adjacent D origin target := by
  rcases target with port | ⟨u,v⟩
  · rfl
  · simp only [adjacentWithControl,BinaryVectorAccess.readMatrix_value,adjacent]
    split <;> rfl

private theorem adjacentWithControl_paid {n width : ℕ} (D : Input n) (origin target : Node (Fin n))
    (fits : n.size≤width) : (adjacentWithControl D origin target).2 ≤ 2*BinaryVectorAccess.budget width := by
  rcases target with port | ⟨u,v⟩
  · exact Nat.zero_le _
  · have read := BinaryVectorAccess.readMatrix_paid D.adjacency u v fits fits
    unfold adjacentWithControl
    dsimp only
    split <;> exact read

private def priceWithControl {n : ℕ} (D : Input n) : Node (Fin n) → (Code × ℕ) × ℕ
  | .inl port => (price D (.inl port),0)
  | .inr (u,v) =>
    let present := BinaryVectorAccess.readMatrix D.adjacency u v
    if present.1 then
      let cost := BinaryVectorAccess.readMatrix D.costs u v
      ((cost.1,4),present.2+cost.2)
    else ((Code.zero,4),present.2)

private theorem priceWithControl_value {n : ℕ} (D : Input n) (node : Node (Fin n)) :
    (priceWithControl D node).1=price D node := by
  rcases node with port | ⟨u,v⟩
  · rfl
  · simp only [priceWithControl,BinaryVectorAccess.readMatrix_value,price]
    split <;> rfl

private theorem priceWithControl_paid {n width : ℕ} (D : Input n) (node : Node (Fin n)) (fits : n.size≤width) :
    (priceWithControl D node).2 ≤ 4*BinaryVectorAccess.budget width := by
  rcases node with port | ⟨u,v⟩
  · exact Nat.zero_le _
  · have arc := BinaryVectorAccess.readMatrix_paid D.adjacency u v fits fits
    have cost := BinaryVectorAccess.readMatrix_paid D.costs u v fits fits
    unfold priceWithControl
    dsimp only
    split <;> omega

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

private def arcEntry {n : ℕ} (D : Input n) (nodes : Vector (Node (Fin n)) (lineSize n))
    (origin : Node (Fin n)) (j : Fin (lineSize n)) : (Bool × ℕ) × ℕ :=
  let target := BinaryVectorAccess.read nodes j
  let arc := adjacentWithControl D origin target.1
  ((arc.1.1,arc.1.2+4),target.2+arc.2)

private def arcRow {n : ℕ} (D : Input n) (nodes : Vector (Node (Fin n)) (lineSize n)) (i : Fin (lineSize n)) :
    (Vector Bool (lineSize n) × ℕ) × ℕ :=
  let origin := BinaryVectorAccess.read nodes i
  let row := BinaryArrayBatch.runWithChildWork (arcEntry D nodes origin.1)
  (row.1,origin.2+row.2)

private def pricedEntry {n : ℕ} (D : Input n) (nodes : Vector (Node (Fin n)) (lineSize n))
    (i : Fin (lineSize n)) : (Code × ℕ) × ℕ :=
  let node := BinaryVectorAccess.read nodes i
  let result := priceWithControl D node.1
  ((result.1.1,result.1.2+2),node.2+result.2)

def prepareWithControl {n : ℕ} (D : Input n) : (GraphInput (lineSize n) × ℕ) × ℕ :=
  let data := labelsWithControl n
  let demanded := demandRows D.demands
  let arcs := BinaryArrayBatch.runWithChildWork (arcRow D data.1.1)
  let costs := BinaryArrayBatch.runWithChildWork (pricedEntry D data.1.1)
  ((⟨arcs.1.1,demanded.1,costs.1.1⟩,data.1.2+demanded.2+arcs.1.2+costs.1.2+4),data.2+arcs.2+costs.2)

def prepare {n : ℕ} (D : Input n) : GraphInput (lineSize n) × ℕ := (prepareWithControl D).1

theorem prepare_reference {n : ℕ} (D : Input n) : prepare D =
  let data := labels n
  let node := fun i : Fin (lineSize n) => data.1[i.val]
  let demanded := demandRows D.demands
  let arcs := batch fun i =>
    let origin := node i
    batch fun j =>
      let a := adjacent D origin (node j)
      (a.1,a.2+4)
  let costs := batch fun i =>
    let c := price D (node i)
    (c.1,c.2+2)
  (⟨arcs.1,demanded.1,costs.1⟩,data.2+demanded.2+arcs.2+costs.2+4) := by
  simp only [prepare,prepareWithControl,arcRow,arcEntry,pricedEntry,labels,
    BinaryArrayBatch.child_projection,BinaryVectorAccess.read_value,adjacentWithControl_value,priceWithControl_value,batch]

@[simp] theorem prepare_value {n : ℕ} (D : Input n) : (prepare D).1=lineInput D := by
  have arcs : (prepare D).1.adjacency=(lineInput D).adjacency := by
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    apply Bool.eq_iff_iff.mpr
    change (prepare D).1.adjacency[i][j]=true ↔ (lineInput D).graph.Adj ⟨i,hi⟩ ⟨j,hj⟩
    rw [lineInput_adj]
    simp only [prepare_reference,batch_value,labels_value,Vector.getElem_ofFn,adjacent_iff]
  have prices : (prepare D).1.costs=(lineInput D).costs := by
    apply Vector.ext
    intro i hi
    simp only [prepare_reference,batch_value,labels_value,lineInput,Vector.getElem_ofFn]
    cases index n ⟨i,hi⟩ with
    | inl port => rfl
    | inr arc => cases arc; rfl
  have demands : (prepare D).1.demands=(lineInput D).demands := by
    simp only [prepare_reference,demandRows_value,lineInput]
  generalize (prepare D).1 = actual at arcs demands prices ⊢
  generalize lineInput D = expected at arcs demands prices ⊢
  cases actual
  cases expected
  cases arcs
  cases demands
  cases prices
  rfl

def assemblyBudget {R : Type*} [Semiring R] (m : R) : R :=
  m*(m*(64*(m+1)^2+12)+8*m+4)+8*m+4+(m*6+8*m+4)+4

theorem prepare_paid {n : ℕ} (D : Input n) :
    (prepare D).2 ≤ budget (lineSize n) (lineSize n)+demandBudget (lineSize n) D.demands.length+
      assemblyBudget (lineSize n) := by
  let m := lineSize n
  let node := fun i : Fin m => (labels n).1[i.val]
  have hn : n ≤ m := by unfold m lineSize; omega
  have arcs := batch_paid (fun i : Fin m => batch fun j : Fin m =>
      let a := adjacent D (node i) (node j)
      (a.1,a.2+4))
    (cap := m*(64*(m+1)^2+12)+8*m+4) (fun i => by
      apply batch_paid
      intro j
      have paid := adjacent_paid D (node i) (node j)
      change (adjacent D (node i) (node j)).2+4 ≤ _
      have scale : 64*(n+1)^2 ≤ 64*(m+1)^2 := by gcongr
      omega)
  have prices := batch_paid (fun i : Fin m => let c := price D (node i); (c.1,c.2+2))
    (cap := 6) (fun i => Nat.add_le_add_right (price_paid D (node i)) 2)
  have setup : (labels n).2+(demandRows D.demands).2 ≤ budget m m+demandBudget m D.demands.length := by
    apply (Nat.add_le_add (labels_paid n) (demandRows_paid D.demands)).trans
    unfold budget demandBudget
    gcongr
  rw [prepare_reference]
  change _ ≤ budget m m+demandBudget m D.demands.length+assemblyBudget m
  unfold assemblyBudget
  exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add setup arcs) prices) 4).trans (by omega)

def controlBudget {R : Type*} [Semiring R] (m : R) : R :=
  let index := BinaryVectorAccess.budget m
  let entry := 64*(m+1)^2+12
  let row := m*entry+8*m+4
  BinaryArrayBatch.childCeiling m (2048*(m+3)^2) 0+
    BinaryArrayBatch.childCeiling m row (index+BinaryArrayBatch.childCeiling m entry (3*index))+
    BinaryArrayBatch.childCeiling m 6 (5*index)

/-- Additional measured scalar control of the same line-graph assembly.
Each row retains its reached label reads and its own batch work. -/
theorem prepare_control_paid {n : ℕ} (D : Input n) :
    (prepareWithControl D).2 ≤ controlBudget (lineSize n) := by
  let m := lineSize n
  let nodes := (labelsWithControl n).1.1
  let index := BinaryVectorAccess.budget m
  let entry := 64*(m+1)^2+12
  let row := m*entry+8*m+4
  have hn : n ≤ m := by unfold m lineSize; omega
  have dimensions : m.size ≤ m := BinaryNaturalOperations.size_le_self m
  have stored : n.size ≤ m := (BinaryNaturalOperations.size_le_self n).trans hn
  have reachable (i : Fin m) : (BinaryVectorAccess.read nodes i).2 ≤ index :=
    BinaryVectorAccess.read_paid nodes i dimensions
  have arcs (origin : Node (Fin n)) (j : Fin m) : (arcEntry D nodes origin j).1.2 ≤ entry := by
    have old := adjacent_paid D origin (BinaryVectorAccess.read nodes j).1
    have fits : 64*(n+1)^2 ≤ 64*(m+1)^2 := by gcongr
    simp only [arcEntry,adjacentWithControl_value]
    change (adjacent D origin (BinaryVectorAccess.read nodes j).1).2+4 ≤ entry
    unfold entry
    omega
  have rows (i : Fin m) : (arcRow D nodes i).1.2 ≤ row ∧
      (arcRow D nodes i).2 ≤ index+BinaryArrayBatch.childCeiling m entry (3*index) := by
    let origin := BinaryVectorAccess.read nodes i
    let cells := arcEntry D nodes origin.1
    constructor
    · change (BinaryArrayBatch.runWithChildWork cells).1.2 ≤ row
      rw [BinaryArrayBatch.child_projection]
      exact batch_paid (fun j => (cells j).1) (arcs origin.1)
    · change origin.2+(BinaryArrayBatch.runWithChildWork cells).2 ≤ _
      have each (j : Fin m) : (cells j).2 ≤ 3*index := by
        have tested := adjacentWithControl_paid D origin.1 (BinaryVectorAccess.read nodes j).1 stored
        change (BinaryVectorAccess.read nodes j).2+
          (adjacentWithControl D origin.1 (BinaryVectorAccess.read nodes j).1).2 ≤ _
        change _ ≤ 2*index at tested
        have lookup := reachable j
        omega
      have total := (BinaryArrayBatch.runWithChildWork_paid cells (arcs origin.1) each).trans
        (BinaryArrayBatch.childBudget_le m entry (3*index))
      exact Nat.add_le_add (reachable i) total
  have matrix := (BinaryArrayBatch.runWithChildWork_paid (arcRow D nodes)
      (fun i => (rows i).1) (fun i => (rows i).2)).trans (BinaryArrayBatch.childBudget_le m row _)
  have retail (i : Fin m) : (pricedEntry D nodes i).1.2 ≤ 6 := by
    simp only [pricedEntry,priceWithControl_value]
    exact Nat.add_le_add_right (price_paid D (BinaryVectorAccess.read nodes i).1) 2
  have priceReads (i : Fin m) : (pricedEntry D nodes i).2 ≤ 5*index := by
    have checked := priceWithControl_paid D (BinaryVectorAccess.read nodes i).1 stored
    change _ ≤ 4*index at checked
    have lookup := reachable i
    change (BinaryVectorAccess.read nodes i).2+(priceWithControl D (BinaryVectorAccess.read nodes i).1).2 ≤ _
    omega
  have prices := (BinaryArrayBatch.runWithChildWork_paid (pricedEntry D nodes) retail priceReads).trans
    (BinaryArrayBatch.childBudget_le m 6 (5*index))
  exact Nat.add_le_add (Nat.add_le_add (labels_bounds n).2 matrix) prices

open Polynomial in
theorem budget_eval (a b : Polynomial ℕ) (x : ℕ) : (budget a b).eval x=budget (a.eval x) (b.eval x) := by
  simp only [budget,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

open Polynomial in
theorem controlBudget_eval (m : Polynomial ℕ) (x : ℕ) : (controlBudget m).eval x=controlBudget (m.eval x) := by
  simp only [controlBudget,BinaryVectorAccess.budget,BinaryArrayBatch.childCeiling,
    eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_zero]

open Polynomial in
theorem prepare_control_polynomial : ∃ p : Polynomial ℕ,
    ∀ {n : ℕ} (D : Input n), (prepareWithControl D).2 ≤ p.eval n := by
  refine ⟨controlBudget (X*2+X*X),fun D => ?_⟩
  simp only [controlBudget_eval,eval_add,eval_mul,eval_X,eval_ofNat]
  exact prepare_control_paid D

/-- Each array constructed by the line-graph preparation has a bounded
persistent-copy schedule, including every inner adjacency row. -/
theorem prepare_arrays {n : ℕ} (D : Input n) :
    let nodes := (labels n).1
    BinaryArrayBatch.StorageModel nodes ∧
      (∀ i, BinaryArrayBatch.StorageModel (arcRow D nodes i).1.1) ∧
      BinaryArrayBatch.StorageModel (prepare D).1.adjacency ∧
      BinaryArrayBatch.StorageModel (prepare D).1.costs := by
  let nodes := (labels n).1
  exact ⟨BinaryArrayBatch.run_storage _,
    fun i => BinaryArrayBatch.runWithChildWork_storage (arcEntry D nodes (BinaryVectorAccess.read nodes i).1),
    BinaryArrayBatch.runWithChildWork_storage (arcRow D nodes),
    BinaryArrayBatch.runWithChildWork_storage (pricedEntry D nodes)⟩

open Polynomial in
theorem demandBudget_eval (a b : Polynomial ℕ) (x : ℕ) :
    (demandBudget a b).eval x=demandBudget (a.eval x) (b.eval x) := by
  simp only [demandBudget,eval_add,eval_mul,eval_pow,eval_ofNat]

open Polynomial in
theorem assemblyBudget_eval (a : Polynomial ℕ) (x : ℕ) :
    (assemblyBudget a).eval x=assemblyBudget (a.eval x) := by
  simp only [assemblyBudget,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

end DirectedFlowCutGap.BinaryLineLabels
