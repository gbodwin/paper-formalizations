import DirectedFlowCutGap.CandidateBudgetCutProgram

/-!
# Capacity predicates for the numbered candidate network

Each capacity is described by two Boolean flags. The unit flag charges a
threshold of an unremoved core vertex. The barrier flag enforces a port
pin, threshold nesting or the difference-bound implication.
-/

namespace DirectedFlowCutGap.CandidateCapacityFlags

open BinaryArithmetic IntegralNetworkFlow MinimumClosureCut CandidatePortDifferenceSystem
open EncodedCandidateCapacity (Input)
open CandidateEnumeration (Point Node Network)

variable {n L : ℕ}

def unitFlag (D : Input n) (sign : Bool) (a : Node n L) : Bool :=
  a.2.val != 0 && a.1.2 == sign &&
    match a.1.1 with
    | .inl v => !D.removed[v.val]
    | .inr _ => false

def shift (D : Input n) (L B : ℕ) (a b : Point n) : ℕ :=
  match a.2,b.2 with
  | false,true => if decide (a.1 = b.1) || (D.portAdjWithCost b.1 a.1).1 then 0 else L
  | true,false => if a.1 = b.1 then min L (D.portCapacity L B a.1) else L
  | _,_ => L

theorem shift_eq (D : Input n) (L B : ℕ) (a b : Point n) :
    (shift D L B a b : ℤ) = D.bound L B a b := by
  rcases a with ⟨u,i⟩
  rcases b with ⟨v,j⟩
  have d (p q : TerminalPorts.Vertex (Fin n)) := D.portAdjWithCost_value p q
  have nonneg : (0 : ℤ) ≤ L := Int.natCast_nonneg _
  cases i <;> cases j
  · simp [shift,Input.bound,orderBound,Input.gap,edgeBound]
  · by_cases eq : u=v
    · subst u
      have hEdge : 0 ≤ edgeBound D.graph L (v,false) (v,true) := by
        unfold edgeBound
        split <;> omega
      simpa [shift,Input.bound,orderBound,Input.gap] using hEdge
    · by_cases adj : (TerminalPorts.graph D.graph).Adj v u
      · simp [shift,eq,d,adj,Input.bound,orderBound,Input.gap,edgeBound,nonneg]
      · simp [shift,eq,d,adj,Input.bound,orderBound,Input.gap,edgeBound]
  · by_cases eq : u=v
    · simp [shift,Input.bound,orderBound,Input.gap,edgeBound,eq,min_comm]
    · simp [shift,Input.bound,orderBound,Input.gap,edgeBound,eq]
  · simp [shift,Input.bound,orderBound,Input.gap,edgeBound]

def barrierFlag (D : Input n) (L B : ℕ) (a b : Node n L) : Bool :=
  (decide (a.1=b.1) && b.2.val ≤ a.2.val) || a.2.val == b.2.val+shift D L B a.1 b.1

private theorem barrierFlag_eq_true (D : Input n) (L B : ℕ) (a b : Node n L) :
    barrierFlag D L B a b = true ↔ (a.1=b.1 ∧ b.2≤a.2) ∨
      ((b.2 : ℕ) : ℤ) = ((a.2 : ℕ) : ℤ)-D.bound L B a.1 b.1 := by
  simp only [barrierFlag,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,Fin.le_def,
    ← shift_eq]
  apply or_congr_right
  omega

def flags (D : Input n) (s t : Fin n) (L B : ℕ) : Network n L → Network n L → Bool×Bool
  | .inr false,.inl a => (unitFlag D false a,a.2.val == 0 || decide (a.1.1=TerminalPorts.sink t))
  | .inl a,.inr true => (unitFlag D true a,decide (0<a.2.val) && decide (a.1.1=TerminalPorts.source s))
  | .inl a,.inl b => (false,barrierFlag D L B a b)
  | _,_ => (false,false)

def amount (β : ℕ) (bits : Bool×Bool) : ℕ :=
  (if bits.1 then 1 else 0)+(if bits.2 then β+1 else 0)

private theorem negative_eq (D : Input n) (a : Node n L) :
    (if unitFlag D false a then 1 else 0)=(-D.nodeCost a).toNat := by
  rcases a with ⟨⟨u,b⟩,i⟩
  cases u with
  | inl u =>
    by_cases zero : i=0
    · simp [zero,unitFlag,Input.nodeCost]
    · have hn : i.val ≠ 0 := fun h => zero (Fin.ext h)
      cases b <;> cases h : D.removed[u.val] <;> simp [unitFlag,Input.nodeCost,Input.cost,zero,hn,h]
  | inr u =>
    by_cases zero : i=0 <;> simp [unitFlag,Input.nodeCost,Input.cost,zero]

private theorem positive_eq (D : Input n) (a : Node n L) :
    (if unitFlag D true a then 1 else 0)=(D.nodeCost a).toNat := by
  rcases a with ⟨⟨u,b⟩,i⟩
  cases u with
  | inl u =>
    by_cases zero : i=0
    · simp [zero,unitFlag,Input.nodeCost]
    · have hn : i.val ≠ 0 := fun h => zero (Fin.ext h)
      cases b <;> cases h : D.removed[u.val] <;> simp [unitFlag,Input.nodeCost,Input.cost,zero,hn,h]
  | inr u =>
    by_cases zero : i=0 <;> simp [unitFlag,Input.nodeCost,Input.cost,zero]

theorem amount_eq_direct (D : Input n) (s t : Fin n) (L B β : ℕ) (u v : Network n L) :
    amount β (flags D s t L B u v) = D.directCapacity s t L B β u v := by
  rcases u with a | a <;> rcases v with b | b
  · simp only [flags,amount,Bool.false_eq_true,ite_false,zero_add,Input.directCapacity,barrierFlag_eq_true]
  · cases b
    · rfl
    · have eq : (decide (0<a.2.val) && decide (a.1.1=TerminalPorts.source s))=true ↔
          (if a.1.1=TerminalPorts.source s then 0 else L) < a.2.val := by
        have le : a.2.val ≤ L := Nat.le_of_lt_succ a.2.isLt
        by_cases port : a.1.1=TerminalPorts.source s
        · simp [port]
        · simp [port,not_lt.mpr le]
      change ((if unitFlag D true a then 1 else 0) +
        if decide (0<a.2.val) && decide (a.1.1=TerminalPorts.source s) then β+1 else 0) = _
      rw [positive_eq D a]
      simp only [eq,Input.directCapacity]
  · cases a
    · have eq : (b.2.val == 0 || decide (b.1.1=TerminalPorts.sink t))=true ↔
          b.2.val ≤ (if b.1.1=TerminalPorts.sink t then L else 0) := by
        have le : b.2.val ≤ L := Nat.le_of_lt_succ b.2.isLt
        by_cases port : b.1.1=TerminalPorts.sink t
        · simp [port,le]
        · simp [port]
      change ((if unitFlag D false b then 1 else 0) +
        if b.2.val == 0 || decide (b.1.1=TerminalPorts.sink t) then β+1 else 0) = _
      rw [negative_eq D b]
      simp only [eq,Input.directCapacity]
    · rfl
  · cases a <;> cases b <;> rfl

theorem amount_eq_capacity (D : Input n) (s t : Fin n) (L B : ℕ) (u v : Network n L) :
    amount (value (CandidatePhysicalCut.fuelWord D s t L B)) (flags D s t L B u v) =
      CandidatePhysicalCut.capacities D s t L B (CandidatePhysicalCut.numberEquiv n L u)
        (CandidatePhysicalCut.numberEquiv n L v) := by
  rw [amount_eq_direct,CandidatePhysicalCut.fuelWord,value_bits,Input.directCapacity_eq]
  simp [CandidatePhysicalCut.capacities,ClosureMaxFlowRefinement.renamedCapacity,
    IntegralFlowRelabeling.capacity]

end DirectedFlowCutGap.CandidateCapacityFlags
