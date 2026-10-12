import DirectedFlowCutGap.DemandCollectionRefinement

namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open GraphWalkExtension

def OptionRelated {α β : Type*} (R : α → β → Prop) : Option α → Option β → Prop
  | none,none => True
  | some a,some b => R a b
  | _,_ => False

theorem argminAux_related {α β : Type*} (R : α → β → Prop)
    (sa : α → Fraction×ℕ) (sb : β → Fraction×ℕ)
    (score : ∀ a b,R a b → (sa a).1=(sb b).1)
    (a : Option α) (b : Option β) (x : α) (y : β)
    (acc : OptionRelated R a b) (head : R x y) :
    OptionRelated R (BinaryFractionalGraphOracle.argminAux sa a x).1
      (BinaryFractionalGraphOracle.argminAux sb b y).1 := by
  cases a with
  | none =>
    cases b with
    | none => exact head
    | some b => exact False.elim acc
  | some a =>
    cases b with
    | none => exact False.elim acc
    | some b =>
      have ha := score a b acc
      have hx := score x y head
      simp only [BinaryFractionalGraphOracle.argminAux,ha,hx]
      split <;> assumption

theorem argminFrom_related {α β : Type*} (R : α → β → Prop)
    (sa : α → Fraction×ℕ) (sb : β → Fraction×ℕ)
    (score : ∀ a b,R a b → (sa a).1=(sb b).1)
    {xs : List α} {ys : List β} (related : List.Forall₂ R xs ys)
    (a : Option α) (b : Option β) (acc : OptionRelated R a b) :
    OptionRelated R (BinaryFractionalGraphOracle.argminFrom sa xs a).1
      (BinaryFractionalGraphOracle.argminFrom sb ys b).1 := by
  induction related generalizing a b with
  | nil => exact acc
  | cons head _ ih =>
    exact ih _ _ (argminAux_related R sa sb score a b _ _ acc head)

theorem argminAux_witness {α : Type*} (score : α → Fraction×ℕ) (a : Option α) (x z : α)
    (hz : (BinaryFractionalGraphOracle.argminAux score a x).1=some z) : z=x ∨ a=some z := by
  cases a with
  | none => exact Or.inl (Option.some.inj hz).symm
  | some a =>
    simp only [BinaryFractionalGraphOracle.argminAux] at hz
    split at hz
    · exact Or.inl (Option.some.inj hz).symm
    · exact Or.inr (congrArg some (Option.some.inj hz))

theorem argminFrom_witness {α : Type*} (score : α → Fraction×ℕ) (xs : List α) (a : Option α)
    (z : α) (hz : (BinaryFractionalGraphOracle.argminFrom score xs a).1=some z) : z∈xs ∨ a=some z := by
  induction xs generalizing a with
  | nil => exact Or.inr hz
  | cons x xs ih =>
    rcases ih _ hz with hmem|hacc
    · exact Or.inl (List.mem_cons_of_mem _ hmem)
    · rcases argminAux_witness score a x z hacc with rfl|hacc
      · exact Or.inl List.mem_cons_self
      · exact Or.inr hacc

def recordScore (z : Record) : Fraction×ℕ := (z.item.score,4)

theorem selected_records_refine {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {xs : List Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (EncodesDemand label) xs ds) (next : ℕ) :
    let zs := records ((ResidualSearch.Enumeration.fin n).vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList next xs
    OptionRelated (fun z q => z∈zs ∧ EncodesRecord label z q)
      (BinaryFractionalGraphOracle.argmin recordScore zs).1
      (BinaryFractionalGraphOracle.selected adjacency y ds).1 := by
  dsimp only
  let zs := records ((ResidualSearch.Enumeration.fin n).vertices.map label)
    (GraphRelaxationRefinement.matrix adjacency) y.toList next xs
  have h := argminFrom_related (EncodesRecord label) recordScore
    (fun q : BinaryFractionalGraphOracle.Selected n => (q.path.cost,4))
    (fun _ _ hr => hr.2.2) (records_refine adjacency y label hlabel encoded next) none none trivial
  change OptionRelated (EncodesRecord label) (BinaryFractionalGraphOracle.argmin recordScore zs).1
    (BinaryFractionalGraphOracle.selected adjacency y ds).1 at h
  cases ha : (BinaryFractionalGraphOracle.argmin recordScore zs).1 with
  | none =>
    cases hb : (BinaryFractionalGraphOracle.selected adjacency y ds).1 with
    | none => trivial
    | some q => simp [ha,hb,OptionRelated] at h
  | some z =>
    have hz : z∈zs := by
      rcases argminFrom_witness recordScore zs none z ha with hz|hz
      · exact hz
      · cases hz
    cases hb : (BinaryFractionalGraphOracle.selected adjacency y ds).1 with
    | none => simp [ha,hb,OptionRelated] at h
    | some q => exact ⟨hz,by simpa only [ha,hb,OptionRelated] using h⟩

theorem items_select (zs : List Record) :
    RetainedArgminProgram.select (zs.map Record.item)=
      (BinaryFractionalGraphOracle.argmin recordScore zs).1.map Record.item := by
  exact RetainedGraphArgmin.value_refines recordScore (fun z => z.item.payload) (fun z => z.item.address) zs

end DirectedFlowCutGap.DemandCollection
