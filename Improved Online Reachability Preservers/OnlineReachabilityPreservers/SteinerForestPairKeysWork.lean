import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import OnlineReachabilityPreservers.SteinerForestNetwork
import OnlineReachabilityPreservers.DeterministicEnumerationWork
import OnlineReachabilityPreservers.SteinerHistoryEnumerationWork

/-! Explicit ordered-pair keys for the metric forest's weighted network. -/

namespace OnlineReachabilityPreservers

private def prependProductRowsWithWordWork {A B C : Type*} (make : A → B → C × ℕ)
    (a : A) (tail : List C) : List B → List C × ℕ
  | [] => (tail, 2)
  | b :: bs =>
    let row := make a b
    let rest := prependProductRowsWithWordWork make a tail bs
    (row.1 :: rest.1, row.2 + rest.2 + 7)

private theorem prependProductRowsWithWordWork_spec {A B C : Type*} (make : A → B → C × ℕ)
    (a : A) (tail : List C) (right : List B) (budget : ℕ)
    (each : ∀ b ∈ right, (make a b).2 ≤ budget) :
    let out := prependProductRowsWithWordWork make a tail right
    out.1 = right.map (fun b => (make a b).1) ++ tail ∧ out.2 ≤ right.length * (budget + 7) + 2 := by
  induction right with
  | nil => simp [prependProductRowsWithWordWork]
  | cons b bs ih =>
    obtain ⟨rows, work⟩ := ih (fun x hx => each x (List.mem_cons_of_mem _ hx))
    have one := each b List.mem_cons_self
    simp only [prependProductRowsWithWordWork, List.map_cons, List.cons_append, rows, List.length_cons, true_and]
    rw [Nat.succ_mul]
    omega

private def productRowsWithWordWork {A B C : Type*} (make : A → B → C × ℕ)
    (right : List B) : List A → List C × ℕ
  | [] => ([], 3)
  | a :: as =>
    let rest := productRowsWithWordWork make right as
    let prefixRows := prependProductRowsWithWordWork make a rest.1 right
    (prefixRows.1, rest.2 + prefixRows.2 + 6)

private theorem productRowsWithWordWork_spec {A B C : Type*} (make : A → B → C × ℕ)
    (left : List A) (right : List B) (budget : ℕ) (each : ∀ a ∈ left, ∀ b ∈ right, (make a b).2 ≤ budget) :
    let out := productRowsWithWordWork make right left
    out.1 = (left ×ˢ right).map (fun ab => (make ab.1 ab.2).1) ∧
      out.2 ≤ left.length * (right.length * (budget + 7) + 8) + 3 := by
  induction left with
  | nil => simp [productRowsWithWordWork]
  | cons a as ih =>
    let prior := productRowsWithWordWork make right as
    obtain ⟨rows, work⟩ := ih (fun x hx => each x (List.mem_cons_of_mem _ hx))
    obtain ⟨head, spent⟩ := prependProductRowsWithWordWork_spec make a prior.1 right budget (each a List.mem_cons_self)
    refine ⟨?_, ?_⟩
    · change (prependProductRowsWithWordWork make a prior.1 right).1 = _
      change (prependProductRowsWithWordWork make a prior.1 right).1 = _ at head
      change prior.1 = _ at rows
      rw [head, rows, List.product_cons, List.map_append, List.map_map]
      rfl
    · change prior.2 + (prependProductRowsWithWordWork make a prior.1 right).2 + 6 ≤
        (as.length + 1) * (right.length * (budget + 7) + 8) + 3
      change prior.2 ≤ _ at work
      change (prependProductRowsWithWordWork make a prior.1 right).2 ≤ _ at spent
      rw [Nat.add_mul, Nat.one_mul]
      omega

private def sideHistoryRow {V : Type*} {h : ℕ} (side : Bool) (node : HeightNode V h) :
    (Bool × HeightNode V h) × ℕ := ((side,node),3)

private def forestVertexRow {V : Type*} {h : ℕ} (root : V) (node : Bool × HeightNode V h) :
    HeightForestVertex V h × ℕ := (heightCopy root node.1 node.2,5)

private def networkVertexRow {V : Type*} {h : ℕ} (label : Fin 3) (v : HeightForestVertex V h) :
    ForestNetworkVertex V h × ℕ := (toLex (label,v),3)

private def pairKeyRow {V : Type*} (a b : V) : (V × V) × ℕ := ((a,b),3)

/-- Enumerate every network key once from root and history rows of the
metric forest. Pair construction follows the list order. -/
def forestNetworkPairKeysFromRowsWithWordWork {V : Type*} {h : ℕ} (roots : List V)
    (histories : List (HeightNode V h)) : List (ForestNetworkVertex V h × ForestNetworkVertex V h) × ℕ :=
  let nodes := productRowsWithWordWork sideHistoryRow histories [false,true]
  let forest := productRowsWithWordWork forestVertexRow nodes.1 roots
  let network := productRowsWithWordWork networkVertexRow forest.1 [0,1,2]
  let keys := productRowsWithWordWork pairKeyRow network.1 network.1
  (keys.1, nodes.2 + forest.2 + network.2 + keys.2 + 11)

def forestNetworkPairKeysFromRowsWordBudget (r h : ℕ) : ℕ :=
  let a := 2 * h
  let b := r * a
  let c := 3 * b
  (2 * (10 * h + 8) + 3) + (r * (12 * a + 8) + 3) + (3 * (10 * b + 8) + 3) +
    (c * (10 * c + 8) + 3) + 11

theorem forestNetworkPairKeysFromRowsWithWordWork_spec {V : Type*} {h : ℕ} (roots : List V)
    (histories : List (HeightNode V h)) (simpleRoots : roots.Nodup) (simpleHistories : histories.Nodup)
    (completeRoots : ∀ v, v ∈ roots) (completeHistories : ∀ node, node ∈ histories) :
    let out := forestNetworkPairKeysFromRowsWithWordWork roots histories
    out.1.Nodup ∧ (∀ key, key ∈ out.1) ∧
      out.1.length = (3 * (roots.length * (2 * histories.length)))^2 ∧
      out.2 ≤ forestNetworkPairKeysFromRowsWordBudget roots.length histories.length := by
  let sides := [false,true]
  let labels : List (Fin 3) := [0,1,2]
  let nodes := productRowsWithWordWork sideHistoryRow histories sides
  let forest := productRowsWithWordWork forestVertexRow nodes.1 roots
  let network := productRowsWithWordWork networkVertexRow forest.1 labels
  let keys := productRowsWithWordWork pairKeyRow network.1 network.1
  obtain ⟨nodeRows, nodeWork⟩ := productRowsWithWordWork_spec sideHistoryRow sides histories 3
    (fun _ _ _ _ => le_rfl)
  obtain ⟨forestRows, forestWork⟩ := productRowsWithWordWork_spec forestVertexRow roots nodes.1 5
    (fun _ _ _ _ => le_rfl)
  obtain ⟨networkRows, networkWork⟩ := productRowsWithWordWork_spec networkVertexRow labels forest.1 3
    (fun _ _ _ _ => le_rfl)
  obtain ⟨keyRows, keyWork⟩ := productRowsWithWordWork_spec pairKeyRow network.1 network.1 3
    (fun _ _ _ _ => le_rfl)
  change nodes.1 = _ at nodeRows
  change forest.1 = _ at forestRows
  change network.1 = _ at networkRows
  change keys.1 = _ at keyRows
  have nodeAll (x : Bool × HeightNode V h) : x ∈ nodes.1 := by
    rw [nodeRows]
    apply List.mem_map.mpr
    refine ⟨x, List.mem_product.mpr ⟨?_, completeHistories x.2⟩, rfl⟩
    cases x.1 <;> simp [sides]
  have forestAll (v : HeightForestVertex V h) : v ∈ forest.1 := by
    rw [forestRows]
    exact List.mem_map.mpr ⟨(heightForestRoot v, heightForestSide v, heightForestHistory v),
      List.mem_product.mpr ⟨completeRoots _, nodeAll _⟩,rfl⟩
  have labelsAll (i : Fin 3) : i ∈ labels := by
    fin_cases i <;> decide
  have networkAll (v : ForestNetworkVertex V h) : v ∈ network.1 := by
    rw [networkRows]
    exact List.mem_map.mpr ⟨ofLex v, List.mem_product.mpr ⟨labelsAll _, forestAll _⟩, rfl⟩
  have nodeSimple : nodes.1.Nodup := by
    rw [nodeRows]
    exact ((show sides.Nodup by decide).product simpleHistories).map (fun _ _ e => e)
  have forestSimple : forest.1.Nodup := by
    rw [forestRows]
    apply (simpleRoots.product nodeSimple).map
    intro x y equal
    apply Prod.ext (congrArg heightForestRoot equal)
    exact Prod.ext (congrArg heightForestSide equal) (congrArg heightForestHistory equal)
  have networkSimple : network.1.Nodup := by
    rw [networkRows]
    exact ((show labels.Nodup by decide).product forestSimple).map (fun _ _ e => congrArg ofLex e)
  have nodeCount : nodes.1.length = 2 * histories.length := by
    rw [nodeRows,List.length_map,List.length_product]
    rfl
  have forestCount : forest.1.length = roots.length * (2 * histories.length) := by
    rw [forestRows,List.length_map,List.length_product,nodeCount]
  have networkCount : network.1.length = 3 * (roots.length * (2 * histories.length)) := by
    rw [networkRows,List.length_map,List.length_product,forestCount]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change keys.1.Nodup
    rw [keyRows]
    exact (networkSimple.product networkSimple).map (fun _ _ e => e)
  · intro key
    change key ∈ keys.1
    rw [keyRows]
    exact List.mem_map.mpr ⟨key,List.mem_product.mpr ⟨networkAll _,networkAll _⟩,rfl⟩
  · change keys.1.length = _
    rw [keyRows,List.length_map,List.length_product,networkCount,pow_two]
  · change nodes.2 + forest.2 + network.2 + keys.2 + 11 ≤ _
    change nodes.2 ≤ _ at nodeWork
    change forest.2 ≤ _ at forestWork
    change network.2 ≤ _ at networkWork
    change keys.2 ≤ _ at keyWork
    rw [nodeCount] at forestWork
    rw [forestCount] at networkWork
    rw [networkCount] at keyWork
    dsimp only [forestNetworkPairKeysFromRowsWordBudget]
    dsimp only [sides,labels,List.length_cons,List.length_nil] at nodeWork networkWork
    have a : histories.length * (3 + 7) = 10 * histories.length := by ring
    have b : (2 * histories.length) * (5 + 7) = 12 * (2 * histories.length) := by ring
    have c (x : ℕ) : x * (3 + 7) = 10 * x := by ring
    rw [a] at nodeWork
    rw [b] at forestWork
    rw [c] at networkWork keyWork
    omega

/-- Prepare the full weighted-network key list directly from a finite
vertex count and a forest height. -/
def finForestNetworkPairKeysWithWordWork (n h : ℕ) :
    List (ForestNetworkVertex (Fin n) h × ForestNetworkVertex (Fin n) h) × ℕ :=
  let roots := finVerticesWithWordWork n
  let histories := heightNodesWithWordWork n h (fun i => (i,1))
  let keys := forestNetworkPairKeysFromRowsWithWordWork roots.1 histories.1
  (keys.1, roots.2 + histories.2 + keys.2 + 8)

def finForestNetworkPairKeysWordPolynomial (n h : ℕ) : ℕ :=
  let historyBound := (n+1)^h
  (8*n+1) + ((heightNodeIndexWordBudget h 1+9)*historyBound+5*h+7) +
    forestNetworkPairKeysFromRowsWordBudget n historyBound + 8

theorem finForestNetworkPairKeysWithWordWork_spec (n h : ℕ) :
    let out := finForestNetworkPairKeysWithWordWork n h
    out.1.Nodup ∧ (∀ key, key ∈ out.1) ∧
      out.1.length ≤ (6*n*(n+1)^h)^2 ∧ out.2 ≤ finForestNetworkPairKeysWordPolynomial n h := by
  let roots := finVerticesWithWordWork n
  let histories := heightNodesWithWordWork n h (fun i => (i,1))
  let keys := forestNetworkPairKeysFromRowsWithWordWork roots.1 histories.1
  obtain ⟨simpleRoots, allRoots, rootWork⟩ := finVerticesWithWordWork_spec n
  obtain ⟨allHistories, simpleHistories, _, historyCount, historyWork⟩ :=
    heightNodesWithWordWork_spec (Equiv.refl (Fin n)) (fun i => (i,1)) 1 (fun _ => rfl) (fun _ => le_rfl) h
  obtain ⟨simpleKeys, allKeys, keyCount, keyWork⟩ :=
    forestNetworkPairKeysFromRowsWithWordWork_spec roots.1 histories.1 simpleRoots simpleHistories allRoots allHistories
  have rootCount : roots.1.length = n := by
    change (finVerticesWithWordWork n).1.length = n
    rw [finVerticesWithWordWork_eq_sort]
    simp
  have many : histories.1.length ≤ (n+1)^h := historyCount.le.trans (heightLexBlockCount_le_pow n h)
  refine ⟨simpleKeys,allKeys,?_,?_⟩
  · change keys.1.length ≤ _
    rw [keyCount, rootCount]
    have len := Nat.pow_le_pow_left (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left n (Nat.mul_le_mul_left 2 many))) 2
    refine len.trans_eq ?_
    congr 1
    ring
  · have work : keys.2 ≤ forestNetworkPairKeysFromRowsWordBudget n ((n+1)^h) := by
      refine keyWork.trans ?_
      rw [rootCount]
      unfold forestNetworkPairKeysFromRowsWordBudget
      dsimp only
      gcongr
    have hWork : histories.2 ≤ (heightNodeIndexWordBudget h 1+9)*((n+1)^h)+5*h+7 := by
      exact historyWork.trans (by gcongr; exact heightLexBlockCount_le_pow n h)
    change roots.2 + histories.2 + keys.2 + 8 ≤ _
    change roots.2 = _ at rootWork
    rw [rootWork]
    dsimp only [finForestNetworkPairKeysWordPolynomial]
    omega

end OnlineReachabilityPreservers
