import DirectedFlowCutGap.EncodedRootVisitExec

/-!
# Fixed encoded pass and round loops for shortcut reachability

These bodies use the retained vertex list itself as round fuel. The only
decisions are the closed encoded visit and final equality scan. A missing
representation propagates as an explicit failure. Each reached table is
related to the original CountedSearch state, including intermediate prefixes,
so its cardinality bound is not inferred merely from the final result.

Charges describe these fixed Boolean/list bodies and their certified scalar
calls. Creating the retained inputs and the common copying overhead for
argument/frame movement remain explicit whole-program obligations.
-/
namespace DirectedFlowCutGap.EncodedRootSearchExec
open BinaryArithmetic EncodedSequenceAccess EncodedSearchScanExec
open EncodedRootVisitExec
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

def pass (D : Input) : List Bits → List Entry → Option (List Entry) × ℕ
  | [],table => (some table,1)
  | v::vs,table =>
      let a := visit D table v
      match a.1 with
      | none => (none,a.2+4)
      | some next =>
          let b := pass D vs next
          (b.1,a.2+b.2+8)

inductive PassExec (D : Input) : List Bits → List Entry → Option (List Entry) → ℕ → Prop
  | nil (table : List Entry) : PassExec D [] table (some table) 1
  | failed (v : Bits) (vs : List Bits) (table : List Entry) (q : ℕ) :
      VisitExec D table v none q → PassExec D (v::vs) table none (q+4)
  | step (v : Bits) (vs : List Bits) (table next : List Entry)
      (out : Option (List Entry)) (q r : ℕ) :
      VisitExec D table v (some next) q → PassExec D vs next out r →
      PassExec D (v::vs) table out (q+r+8)

theorem PassExec.result {D : Input} {vs : List Bits} {table : List Entry}
    {out : Option (List Entry)} {q : ℕ} (h : PassExec D vs table out q) :
    out=(pass D vs table).1 ∧ q=(pass D vs table).2 := by
  induction h with
  | nil table => exact ⟨rfl,rfl⟩
  | failed v vs table q hv =>
      have a := hv.result
      constructor <;> simp only [pass,← a.1,← a.2]
  | step v vs table next out q r hv hp ih =>
      have a := hv.result
      constructor <;> simp only [pass,← a.1,← a.2,← ih.1,← ih.2]

theorem pass_exec (D : Input) (vs : List Bits) (table : List Entry) :
    PassExec D vs table (pass D vs table).1 (pass D vs table).2 := by
  induction vs generalizing table with
  | nil => exact .nil table
  | cons v vs ih =>
      have ha := visit_exec D table v
      cases h : (visit D table v).1 with
      | none =>
          rw [h] at ha
          simpa only [pass,h] using PassExec.failed v vs table _ ha
      | some next =>
          rw [h] at ha
          simpa only [pass,h] using PassExec.step v vs table next _ _ _ ha (ih next)

def rounds (D : Input) (vertices : List Bits) (target : Bits) :
    List Bits → Option (List Entry) × ℕ
  | [] =>
      let c := copyBits target
      (some [keyEntry c.1],c.2+8)
  | _::fuel =>
      let a := rounds D vertices target fuel
      match a.1 with
      | none => (none,a.2+4)
      | some table =>
          let b := pass D vertices table
          (b.1,a.2+b.2+8)

inductive RoundsExec (D : Input) (vertices : List Bits) (target : Bits) :
    List Bits → Option (List Entry) → ℕ → Prop
  | initial (out : Bits) (q : ℕ) : BitsCopyExec target out q →
      RoundsExec D vertices target [] (some [keyEntry out]) (q+8)
  | failed (head : Bits) (fuel : List Bits) (q : ℕ) :
      RoundsExec D vertices target fuel none q →
      RoundsExec D vertices target (head::fuel) none (q+4)
  | step (head : Bits) (fuel : List Bits) (table : List Entry)
      (out : Option (List Entry)) (q r : ℕ) :
      RoundsExec D vertices target fuel (some table) q → PassExec D vertices table out r →
      RoundsExec D vertices target (head::fuel) out (q+r+8)

theorem RoundsExec.result {D : Input} {vertices : List Bits} {target : Bits}
    {fuel : List Bits} {out : Option (List Entry)} {q : ℕ}
    (h : RoundsExec D vertices target fuel out q) :
    out=(rounds D vertices target fuel).1 ∧ q=(rounds D vertices target fuel).2 := by
  induction h with
  | initial out q hc =>
      have c := hc.result
      constructor <;> simp only [rounds,← c.1,← c.2]
  | failed head fuel q hr ih =>
      constructor <;> simp only [rounds,← ih.1,← ih.2]
  | step head fuel table out q r hr hp ih =>
      have b := hp.result
      constructor <;> simp only [rounds,← ih.1,← ih.2,← b.1,← b.2]

theorem rounds_exec (D : Input) (vertices : List Bits) (target : Bits) (fuel : List Bits) :
    RoundsExec D vertices target fuel (rounds D vertices target fuel).1
      (rounds D vertices target fuel).2 := by
  induction fuel with
  | nil => exact .initial _ _ (copyBits_exec target)
  | cons head fuel ih =>
      cases h : (rounds D vertices target fuel).1 with
      | none =>
          rw [h] at ih
          simpa only [rounds,h] using RoundsExec.failed head fuel _ ih
      | some table =>
          rw [h] at ih
          simpa only [rounds,h] using
            RoundsExec.step head fuel table _ _ _ ih (pass_exec D vertices table)

def search (D : Input) (vertices : List Bits) : Option Bool × ℕ :=
  let a := rounds D vertices D.target vertices
  match a.1 with
  | none => (none,a.2+4)
  | some table =>
      let r := foundScan (.lookup D.source) table
      (r.1,a.2+r.2+8)

inductive SearchExec (D : Input) (vertices : List Bits) : Option Bool → ℕ → Prop
  | failed (q : ℕ) : RoundsExec D vertices D.target vertices none q →
      SearchExec D vertices none (q+4)
  | finish (table : List Entry) (out : Option Bool) (q r : ℕ) :
      RoundsExec D vertices D.target vertices (some table) q →
      FoundExec (.lookup D.source) table out r → SearchExec D vertices out (q+r+8)

theorem SearchExec.result {D : Input} {vertices : List Bits} {out : Option Bool} {q : ℕ}
    (h : SearchExec D vertices out q) : out=(search D vertices).1 ∧ q=(search D vertices).2 := by
  cases h with
  | failed q ha =>
      have a := ha.result
      constructor <;> simp only [search,← a.1,← a.2]
  | finish table out q r ha hr =>
      have a := ha.result
      have r := hr.result
      constructor <;> simp only [search,← a.1,← a.2,← r.1,← r.2]

theorem search_exec (D : Input) (vertices : List Bits) :
    SearchExec D vertices (search D vertices).1 (search D vertices).2 := by
  have ha := rounds_exec D vertices D.target vertices
  cases h : (rounds D vertices D.target vertices).1 with
  | none =>
      rw [h] at ha
      simpa only [search,h] using SearchExec.failed _ ha
  | some table =>
      rw [h] at ha
      simpa only [search,h] using
        SearchExec.finish table _ _ _ ha (foundScan_exec (.lookup D.source) table)

variable {m : ℕ} (D : EncodedShortcutReachability.Input m)
variable (encode : Fin m → Bits) (he : ∀ v, value (encode v)=v.val) (s t : Fin m)
include he

theorem visit_state (S : ResidualSearch.State (D.restrictedGraph s t) t) (v : Fin m) :
    (visit (inputValue D (encode s) (encode t))
      (tableValue encode (CountedSearchRootProjection.roots S)) (encode v)).1 =
      some (tableValue encode (CountedSearchRootProjection.roots
        (CountedSearch.visit (D.restrictedTest s t) S v).1)) := by
  rw [visit_refines D encode he]
  rw [CountedSearchRootProjection.visit_roots (D.restrictedTest s t) S v]

theorem pass_state (vertices : List (Fin m))
    (S : ResidualSearch.State (D.restrictedGraph s t) t) :
    (pass (inputValue D (encode s) (encode t)) (vertices.map encode)
      (tableValue encode (CountedSearchRootProjection.roots S))).1 =
      some (tableValue encode (CountedSearchRootProjection.roots
        (CountedSearch.pass (D.restrictedTest s t) vertices S).1)) := by
  induction vertices generalizing S with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.map_cons,pass,visit_state D encode he s t S v,CountedSearch.pass,ih]

theorem rounds_state (E : ResidualSearch.Enumeration (Fin m)) (fuel : List Bits) :
    (rounds (inputValue D (encode s) (encode t)) (E.vertices.map encode) (encode t) fuel).1 =
      some (tableValue encode (CountedSearchRootProjection.roots
        (CountedSearch.rounds (t := t) E (D.restrictedTest s t) fuel.length).1)) := by
  induction fuel with
  | nil => simp [rounds,copyBits_spec,tableValue,CountedSearchRootProjection.roots,
      CountedSearch.rounds,ResidualSearch.State.initial]
  | cons head fuel ih =>
      simp only [rounds,ih,pass_state D encode he s t,CountedSearch.rounds,List.length_cons]

/-- The same complete enumeration is retained for visits and round fuel. -/
theorem search_found (E : ResidualSearch.Enumeration (Fin m)) :
    (search (inputValue D (encode s) (encode t)) (E.vertices.map encode)).1 =
      some (EncodedShortcutReachability.Input.found
        (CountedSearch.search E (D.restrictedTest s t) s t).1) := by
  have h := rounds_state D encode he s t E (E.vertices.map encode)
  have hl : (E.vertices.map encode).length = Fintype.card (Fin m) := by
    simpa only [List.length_map] using E.length_eq_card
  rw [hl] at h
  simp only [inputValue] at h
  simp only [search,inputValue,h]
  rw [lookup_found encode he]
  congr 1
  symm
  exact CountedSearchRootProjection.extract_found _ _ s

def passBound (m B length : ℕ) : ℕ := length*(EncodedRootVisitExec.visitBound m B+8)+1

theorem pass_bound (vertices : List (Fin m))
    (S : ResidualSearch.State (D.restrictedGraph s t) t) (B : ℕ)
    (hw : ∀ v, (encode v).length ≤ B) :
    (pass (inputValue D (encode s) (encode t)) (vertices.map encode)
      (tableValue encode (CountedSearchRootProjection.roots S))).2 ≤ passBound m B vertices.length := by
  induction vertices generalizing S with
  | nil => simp [pass,passBound]
  | cons v vs ih =>
      have hv := visit_bound D encode (CountedSearchRootProjection.roots S) s t v B hw (by
        simpa only [CountedSearchRootProjection.roots,List.length_map,Fintype.card_fin] using S.length_le_card)
      have hi := ih (CountedSearch.visit (D.restrictedTest s t) S v).1
      simp only [List.map_cons,pass,visit_state D encode he s t S v,List.length_cons]
      unfold passBound at *
      nlinarith

def roundsBound (m B length : ℕ) : ℕ := length*(passBound m B m+8)+4*B+9

theorem rounds_bound (E : ResidualSearch.Enumeration (Fin m)) (fuel : List Bits) (B : ℕ)
    (hw : ∀ v, (encode v).length ≤ B) :
    (rounds (inputValue D (encode s) (encode t)) (E.vertices.map encode) (encode t) fuel).2 ≤
      roundsBound m B fuel.length := by
  induction fuel with
  | nil =>
      have ht := hw t
      simp only [rounds,(copyBits_spec (encode t)).2,List.length_nil,roundsBound]
      omega
  | cons head fuel ih =>
      have hr := rounds_state D encode he s t E fuel
      have hp := pass_bound D encode he s t E.vertices
        (CountedSearch.rounds (t := t) E (D.restrictedTest s t) fuel.length).1 B hw
      have hl : E.vertices.length=m := by simpa only [Fintype.card_fin] using E.length_eq_card
      rw [hl] at hp
      simp only [rounds,hr,List.length_cons]
      unfold roundsBound at *
      nlinarith

def searchBound (m B : ℕ) : ℕ :=
  roundsBound m B m+scanBound m (16*(B+1)+4) B 1+12

theorem search_bound (E : ResidualSearch.Enumeration (Fin m)) (B : ℕ)
    (hw : ∀ v, (encode v).length ≤ B) :
    (search (inputValue D (encode s) (encode t)) (E.vertices.map encode)).2 ≤ searchBound m B := by
  have hr := rounds_state D encode he s t E (E.vertices.map encode)
  have ha := rounds_bound D encode he s t E (E.vertices.map encode) B hw
  let S := (CountedSearch.rounds (t := t) E (D.restrictedTest s t)
    (E.vertices.map encode).length).1
  have hk : (CountedSearchRootProjection.roots S).length ≤ m := by
    simpa only [CountedSearchRootProjection.roots,List.length_map,Fintype.card_fin] using S.length_le_card
  have hb := keyOnly_bound (.lookup (encode s))
    ((CountedSearchRootProjection.roots S).map encode) (16*(B+1)+4) B
    (by
      intro label hlabel
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hlabel
      exact lookup_check_bound (encode u) (encode s) B (hw u) (hw s))
    (by
      intro label hlabel
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hlabel
      exact hw u)
  have hm := Nat.mul_le_mul_right (16*(B+1)+4+12) hk
  have hl : (E.vertices.map encode).length=m := by
    simpa only [List.length_map,Fintype.card_fin] using E.length_eq_card
  rw [hl] at ha
  simp only [List.map_map,Function.comp_def,List.length_map] at hb
  simp only [inputValue] at hr ha
  simp only [search,inputValue,hr,foundScan,tableValue]
  unfold searchBound scanBound at *
  change _ ≤ _ at hb
  dsimp only [S] at hb hm
  omega

end DirectedFlowCutGap.EncodedRootSearchExec
