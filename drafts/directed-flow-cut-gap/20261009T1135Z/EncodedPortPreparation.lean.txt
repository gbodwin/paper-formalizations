import DirectedFlowCutGap.EncodedUnitCostOutput
import DirectedFlowCutGap.EncodedShortcutReachability
import DirectedFlowCutGap.RetainedSurvivorEnumeration

/-!
# Rational low-weight masks and explicit permanent-port encoding

The port labels are the three consecutive blocks of `Fin (3*n)`. All maps are
explicit arithmetic. The removal threshold is computed as an unreduced
rational once, and only weighted cores can be removed. Weight doubling and
clipping are exact raw-rational operations. The semantic equivalence targets
the frozen `UnitCostReduction.PreparedVertex` type.
-/

namespace DirectedFlowCutGap.EncodedPortPreparation

open scoped NNReal NNRat
open RawNonnegativeRational EncodedUnitCostReplication

abbrev Port (n : ℕ) := TerminalPorts.Vertex (Fin n)

def encodePort {n : ℕ} : Port n → Fin (3*n)
  | .inl v => ⟨v.val,by omega⟩
  | .inr (.inl v) => ⟨n+v.val,by omega⟩
  | .inr (.inr v) => ⟨2*n+v.val,by omega⟩

def decodePort {n : ℕ} (i : Fin (3*n)) : Port n :=
  if h : i.val<n then .inl ⟨i.val,h⟩ else
    if h' : i.val<2*n then .inr (.inl ⟨i.val-n,by omega⟩)
    else .inr (.inr ⟨i.val-2*n,by omega⟩)

@[simp] theorem decode_encode {n : ℕ} (p : Port n) : decodePort (encodePort p) = p := by
  rcases p with v | p
  · simp [encodePort,decodePort,v.isLt]
  · rcases p with v | v
    · have h₁ : ¬n+v.val<n := by omega
      have h₂ : n+v.val<2*n := by omega
      simp [encodePort,decodePort,h₁,h₂]
    · have h₁ : ¬2*n+v.val<n := by omega
      have h₂ : ¬2*n+v.val<2*n := by omega
      simp [encodePort,decodePort,h₁,h₂]

@[simp] theorem encode_decode {n : ℕ} (i : Fin (3*n)) : encodePort (decodePort i) = i := by
  unfold decodePort
  split_ifs <;> apply Fin.ext <;> dsimp [encodePort] <;> omega

def portEquiv (n : ℕ) : Fin (3*n) ≃ Port n where
  toFun := decodePort
  invFun := encodePort
  left_inv := encode_decode
  right_inv := decode_encode

def lowMask {n : ℕ} (D : Input n) : Vector Bool n :=
  let threshold := Code.one.div (Code.ofNat (2*n))
  Vector.ofFn (n := n) fun v => D.weights[v.val].le threshold

theorem lowMask_refines {n : ℕ} (D : Input n) (v : Fin n) :
    (lowMask D)[v.val] = true ↔ v∈UnitCostReduction.removed D.weight := by
  simp only [lowMask,Vector.getElem_ofFn,Code.le_eq_true,Code.value_div,
    Code.value_one,Code.value_ofNat,UnitCostReduction.mem_removed,
    Nat.cast_mul,Nat.cast_ofNat,Fintype.card_fin,Input.weight]
  unfold Code.realValue
  simpa only [NNRat.cast_div,NNRat.cast_one,NNRat.cast_mul,NNRat.cast_ofNat,
    NNRat.cast_natCast] using
    (NNRat.cast_le (K := ℝ≥0) (p := D.weights[v.val].value) (q := 1/(2*n))).symm

theorem lowThreshold_bounded (n : ℕ) :
    (Code.one.div (Code.ofNat (2*n))).Bounded (Nat.size (2*n)) := by
  have hd : (Code.ofNat (2*n)).Bounded (Nat.size (2*n)) :=
    ⟨(Nat.lt_size_self _).le,Nat.one_le_two_pow⟩
  simpa using Code.bounded_div Code.bounded_one hd

/-- These are the actual unreduced cross-products evaluated by the low-mask
test. Their width is additive in the input width and the size of `2*n`. -/
theorem lowMask_comparison_bits {n : ℕ} (D : Input n) (b : ℕ)
    (h : ∀ v : Fin n, D.weights[v.val].Bounded b) (v : Fin n) :
    let q := Code.one.div (Code.ofNat (2*n))
    Nat.size (D.weights[v.val].num*q.den) ≤ b+Nat.size (2*n)+1 ∧
      Nat.size (q.num*D.weights[v.val].den) ≤ b+Nat.size (2*n)+1 := by
  have hp := Code.comparison_intermediates (h v) (lowThreshold_bounded n)
  exact ⟨(Nat.size_le_size hp.1).trans_eq Nat.size_pow,
    (Nat.size_le_size hp.2).trans_eq Nat.size_pow⟩

/-- Constant-size Boolean port adjacency, including the direct same-vertex
source-to-sink edge representing an original length-zero path. -/
def portAdj {n : ℕ} (D : Input n) : Port n → Port n → Bool
  | .inl u,.inl v => D.adjacency[u.val][v.val]
  | .inr (.inl u),.inl v => D.adjacency[u.val][v.val]
  | .inl u,.inr (.inr v) => D.adjacency[u.val][v.val]
  | .inr (.inl u),.inr (.inr v) => decide (u=v) || D.adjacency[u.val][v.val]
  | _,_ => false

theorem portAdj_refines {n : ℕ} (D : Input n) (a b : Port n) :
    portAdj D a b = true ↔ (TerminalPorts.graph D.graph).Adj a b := by
  rcases a with a | a <;> rcases b with b | b
  · simp [portAdj,TerminalPorts.graph,Input.graph]
  · cases b <;> simp [portAdj,TerminalPorts.graph,Input.graph]
  · cases a <;> simp [portAdj,TerminalPorts.graph,Input.graph]
  · cases a <;> cases b <;> simp [portAdj,TerminalPorts.graph,Input.graph]

/-- Both arrays are materialized once. The rational threshold mask is shared
across all port-mask cells; port adjacency makes bounded input-array reads. -/
def portData {n : ℕ} (D : Input n) : EncodedShortcutReachability.Input (3*n) :=
  let N := 3*n
  let low := lowMask D
  { adjacency := Vector.ofFn (n := N) fun i => Vector.ofFn (n := N) fun j =>
      portAdj D (decodePort i) (decodePort j)
    removed := Vector.ofFn (n := N) fun i => match decodePort i with
      | .inl v => low[v.val]
      | .inr _ => false }

theorem portData_adj {n : ℕ} (D : Input n) (i j : Fin (3*n)) :
    (portData D).graph.Adj i j ↔ (TerminalPorts.graph D.graph).Adj (decodePort i) (decodePort j) := by
  change ((portData D).adjacency[i.val])[j.val] = true ↔ _
  simpa only [portData,Vector.getElem_ofFn] using portAdj_refines D (decodePort i) (decodePort j)

theorem portData_removed {n : ℕ} (D : Input n) (i : Fin (3*n)) :
    i∈(portData D).removedSet ↔
      decodePort i∈(UnitCostReduction.removed D.weight).image TerminalPorts.core := by
  rw [EncodedShortcutReachability.Input.mem_removedSet]
  cases hi : decodePort i with
  | inl v =>
    simpa [portData,hi,TerminalPorts.core] using lowMask_refines D v
  | inr p =>
    cases p <;> simp [portData,hi,TerminalPorts.core]

def survivorEquiv {n : ℕ} (D : Input n) :
    RetainedSurvivorEnumeration.Survivor (portData D).removed ≃
      UnitCostReduction.PreparedVertex D.weight where
  toFun a := ⟨decodePort a.val,by
    intro h
    have hr := (portData_removed D a.val).mpr h
    have ht := (EncodedShortcutReachability.Input.mem_removedSet _ _).mp hr
    simp [a.property] at ht⟩
  invFun a := ⟨encodePort a.val,by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hr := (EncodedShortcutReachability.Input.mem_removedSet _ _).mpr ht
    have hm := (portData_removed D (encodePort a.val)).mp hr
    rw [decode_encode] at hm
    exact a.property hm⟩
  left_inv a := Subtype.ext (encode_decode a.val)
  right_inv a := Subtype.ext (decode_encode a.val)

def clipOne (q : Code) : Code := if Code.one.le q then Code.one else q

@[simp] theorem clipOne_value (q : Code) : (clipOne q).value = min 1 q.value := by
  by_cases h : Code.one.le q = true
  · have hq : 1 ≤ q.value := by simpa using (Code.le_eq_true _ _).mp h
    simp [clipOne,h,min_eq_left hq]
  · have hq : q.value ≤ 1 := le_of_not_ge (by simpa using h)
    simp [clipOne,h,min_eq_right hq]

def preparedWeightCode {n : ℕ} (D : Input n) : Port n → Code
  | .inl v => clipOne ((Code.ofNat 2).mul D.weights[v.val])
  | .inr _ => Code.zero

def preparedCostCode {n : ℕ} (D : Input n) : Port n → Code
  | .inl v => D.costs[v.val]
  | .inr _ => Code.zero

theorem preparedWeight_refines {n : ℕ} (D : Input n)
    (a : RetainedSurvivorEnumeration.Survivor (portData D).removed) :
    (preparedWeightCode D (decodePort a.val)).realValue =
      UnitCostReduction.preparedWeight D.weight (survivorEquiv D a) := by
  change (preparedWeightCode D (decodePort a.val)).realValue =
    min 1 (2*TerminalPorts.extend D.weight (decodePort a.val))
  cases ha : decodePort a.val <;>
    simp [preparedWeightCode,Code.realValue,TerminalPorts.extend,Input.weight,
      NNRat.cast_min]

theorem preparedCost_refines {n : ℕ} (D : Input n)
    (a : RetainedSurvivorEnumeration.Survivor (portData D).removed) :
    (preparedCostCode D (decodePort a.val)).realValue =
      UnitCostReduction.preparedCost D.weight D.cost (survivorEquiv D a) := by
  change (preparedCostCode D (decodePort a.val)).realValue =
    TerminalPorts.extend D.cost (decodePort a.val)
  cases ha : decodePort a.val <;> simp [preparedCostCode,Code.realValue,TerminalPorts.extend,Input.cost]

theorem clipOne_bounded {q : Code} {b : ℕ} (h : q.Bounded b) : (clipOne q).Bounded b := by
  unfold clipOne
  split
  · exact Code.bounded_mono Code.bounded_one (Nat.zero_le _)
  · exact h

theorem preparedWeight_bounded {n : ℕ} (D : Input n) (b : ℕ)
    (h : ∀ v : Fin n, D.weights[v.val].Bounded b) (p : Port n) :
    (preparedWeightCode D p).Bounded (b+1) := by
  cases p with
  | inl v =>
    have ht : (Code.ofNat 2).Bounded 1 := by norm_num [Code.ofNat,Code.Bounded]
    simpa [preparedWeightCode,Nat.add_comm] using clipOne_bounded (Code.bounded_mul ht (h v))
  | inr p => exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)

section Relabel
variable {A B : Type*} [DecidableEq A] [DecidableEq B]
variable {G : Digraph A} {H : Digraph B}

omit [DecidableEq A] [DecidableEq B] in
private theorem nonempty_path_iff (e : A ≃ B)
    (h : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) (s t : A) :
    Nonempty (SimplePath G s t) ↔ Nonempty (SimplePath H (e s) (e t)) := by
  classical
  constructor
  · rintro ⟨p⟩
    exact ⟨FiniteGraphRelabeling.mapPath e h p⟩
  · rintro ⟨p⟩
    have q := FiniteGraphRelabeling.mapPath e.symm (FiniteGraphRelabeling.inverse_adj e h) p
    simpa only [Equiv.symm_apply_apply] using Nonempty.intro q

private def mapSurvivor (e : A ≃ B) (S : Finset A) (T : Finset B)
    (h : ∀ a, a∈S ↔ e a∈T) (a : ShortcutContraction.Survivor S) :
    ShortcutContraction.Survivor T := ⟨e a.val,fun hm => a.property ((h a.val).mpr hm)⟩

private theorem shortcut_relabel (e : A ≃ B)
    (hAdj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b))
    (S : Finset A) (T : Finset B) (hMem : ∀ a, a∈S ↔ e a∈T)
    (s t : ShortcutContraction.Survivor S) :
    (ShortcutContraction.graph G S).Adj s t ↔
      (ShortcutContraction.graph H T).Adj (mapSurvivor e S T hMem s) (mapSurvivor e S T hMem t) := by
  rw [ShortcutReachability.shortcut_iff_restricted,ShortcutReachability.shortcut_iff_restricted]
  have hr (a b : A) :
      (ShortcutReachability.restricted G S s.val t.val).Adj a b ↔
      (ShortcutReachability.restricted H T (e s.val) (e t.val)).Adj (e a) (e b) := by
    simp only [ShortcutReachability.restricted,hAdj,hMem,e.injective.eq_iff]
  have hp := nonempty_path_iff e hr s.val t.val
  have hn : e s.val≠e t.val ↔ s.val≠t.val := not_congr e.injective.eq_iff
  change (s.val≠t.val ∧ _) ↔ (e s.val≠e t.val ∧ _)
  dsimp only [mapSurvivor]
  rw [hn,← hp]

end Relabel

def booleanSurvivor {n : ℕ} (D : Input n)
    (a : RetainedSurvivorEnumeration.Survivor (portData D).removed) :
    ShortcutContraction.Survivor (portData D).removedSet :=
  ⟨a.val,by simp [EncodedShortcutReachability.Input.mem_removedSet,a.property]⟩

/-- Exact graph equality at surviving encoded labels, after actual Boolean
reachability materialization and the explicit permanent-port relabeling. -/
theorem preparedShortcut_refines {n : ℕ} (D : Input n)
    (a b : RetainedSurvivorEnumeration.Survivor (portData D).removed) :
    (portData D).materialize.adjacency[a.val.val][b.val.val] = true ↔
      (UnitCostReduction.preparedGraph D.graph D.weight).Adj (survivorEquiv D a) (survivorEquiv D b) := by
  refine ((portData D).materialize_refines (booleanSurvivor D a) (booleanSurvivor D b)).trans ?_
  exact shortcut_relabel (portEquiv n) (portData_adj D)
    (portData D).removedSet ((UnitCostReduction.removed D.weight).image TerminalPorts.core)
    (portData_removed D) (booleanSurvivor D a) (booleanSurvivor D b)

end DirectedFlowCutGap.EncodedPortPreparation
