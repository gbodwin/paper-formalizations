import DirectedFlowCutGap.FractionalCoverRawGraph

/-!
# Widths of actual raw minimum-path caches

The synchronous recurrence extends a candidate by exactly one edge per round,
so its unreduced numerator/denominator widths grow linearly in the horizon.
Retained simple-path recovery sums at most n edge codes. These are actual raw
operand bounds; they do not instantiate natural arithmetic bit-cost allowances.
-/
namespace DirectedFlowCutGap.FractionalCoverRawOracle
open FractionalCoverRawCore RawNonnegativeRational IntegralNetworkFlow Tabulated
variable {V : Type*} [DecidableEq V]
variable {B b k : ℕ}

def CandidateBounded (q : Candidate V) (b k : ℕ) : Prop :=
  q.cost.Bounded (k*(b+1)) ∧ q.edges.length ≤ k

omit [DecidableEq V] in
lemma zero_bounded (b k : ℕ) : CandidateBounded (zero : Candidate V) b k :=
  ⟨Code.bounded_mono Code.bounded_zero (Nat.zero_le _),by simp [zero]⟩

omit [DecidableEq V] in
lemma extend_bounded (cost : V × V → Code) (hc : ∀ e, (cost e).Bounded b)
    (u v : V) {q : Candidate V} (hq : CandidateBounded q b k) :
    CandidateBounded (extend cost u v q) b (k+1) := by
  refine ⟨?_,by simpa [extend] using Nat.succ_le_succ hq.2⟩
  have h := Code.bounded_add (hc (u,v)) hq.1
  simpa only [extend,show b+k*(b+1)+1=(k+1)*(b+1) by ring] using h

omit [DecidableEq V] in
lemma pick_bounded (a b : Option (Candidate V)) (B k : ℕ)
    (ha : ∀ q, a=some q → CandidateBounded q B k)
    (hb : ∀ q, b=some q → CandidateBounded q B k) :
    ∀ q, pick a b=some q → CandidateBounded q B k := by
  cases a with
  | none => exact hb
  | some a =>
    cases b with
    | none => exact ha
    | some b =>
      intro q hq
      simp only [pick] at hq
      split at hq
      · cases hq; exact ha _ rfl
      · cases hq; exact hb _ rfl

omit [DecidableEq V] in
lemma scan_bounded (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → Code)
    (hc : ∀ e, (cost e).Bounded B) (u : V) (xs : Table V)
    (hx : ∀ z ∈ xs, CandidateBounded z.2 B k) :
    ∀ q, (scan G cost u xs).1=some q → CandidateBounded q B (k+1) := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    rcases x with ⟨v,p⟩
    have hp := hx (v,p) List.mem_cons_self
    have ht := ih (fun z hz => hx z (List.mem_cons_of_mem _ hz))
    intro q hq
    simp only [scan] at hq
    split at hq
    · apply pick_bounded _ _ B (k+1) ?_ ht q hq
      intro r hr
      cases hr
      exact extend_bounded cost hc u v hp
    · exact ht q hq

lemma atVertex_bounded (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → Code)
    (hc : ∀ e, (cost e).Bounded B) (t u : V) (xs : Table V)
    (hx : ∀ z ∈ xs, CandidateBounded z.2 B k) :
    ∀ q, (atVertex G cost t u xs).1=some q → CandidateBounded q B (k+1) := by
  intro q hq
  unfold atVertex at hq
  split at hq
  · cases hq
    exact zero_bounded _ _
  · exact scan_bounded G cost hc u xs hx q hq

lemma pass_bounded (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → Code)
    (hc : ∀ e, (cost e).Bounded B) (t : V) (old : Table V) (vs : List V)
    (ho : ∀ z ∈ old, CandidateBounded z.2 B k) :
    ∀ z ∈ (pass G cost t old vs).1, CandidateBounded z.2 B (k+1) := by
  induction vs with
  | nil => simp [pass]
  | cons u us ih =>
    intro z hz
    simp only [pass] at hz
    split at hz
    · exact ih z hz
    · rename_i p hp
      rcases List.mem_cons.mp hz with rfl | hz
      · exact atVertex_bounded G cost hc t u old ho p hp
      · exact ih z hz

/-- All cached costs are bounded at every synchronous round. -/
theorem rounds_bounded (vs : List V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → Code) (hc : ∀ e, (cost e).Bounded B) (t : V) (k : ℕ) :
    ∀ z ∈ (rounds vs G cost t k).1, CandidateBounded z.2 B k := by
  induction k with
  | zero =>
    intro z hz
    simp only [rounds,List.mem_singleton] at hz
    subst z
    exact zero_bounded _ _
  | succ k ih => exact pass_bounded G cost hc t _ vs ih

lemma lookup_bounded (u : V) (xs : Table V)
    (hx : ∀ z ∈ xs, CandidateBounded z.2 B k) :
    ∀ q, (lookup u xs).1=some q → CandidateBounded q B k := by
  induction xs with
  | nil => simp [lookup]
  | cons x xs ih =>
    rcases x with ⟨v,p⟩
    have hp := hx (v,p) List.mem_cons_self
    have ht := ih (fun z hz => hx z (List.mem_cons_of_mem _ hz))
    intro q hq
    simp only [lookup] at hq
    split at hq
    · apply pick_bounded _ _ B k ?_ ht q hq
      intro r hr
      cases hr
      exact hp
    · exact ht q hq

theorem minimize_bounded (E : ResidualSearch.Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (cost : V × V → Code) (hc : ∀ e, (cost e).Bounded B)
    (s t : V) {q : Candidate V} (hq : (minimize E G cost s t).1=some q) :
    CandidateBounded q B E.vertices.length :=
  lookup_bounded s _ (rounds_bounded E.vertices G cost hc t E.vertices.length) q hq

variable [Fintype V]

lemma recover_bounded (E : ResidualSearch.Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (cost : V × V → Code) (hc : ∀ e, (cost e).Bounded B)
    (s t : V) (es : List (V × V)) :
    CandidateBounded (recover E G cost s t es).1 B (Fintype.card V) := by
  have hlen := (RetainedPathSearch.search E (FractionalCoverPathOracle.supportTest G es) s t).edges_length_le
  have hsum := sumCodes_bounded
    ((RetainedPathSearch.search E (FractionalCoverPathOracle.supportTest G es) s t).edges.map cost) B
    (by intro q hq; obtain ⟨e,_,rfl⟩ := List.mem_map.mp hq; exact hc e)
  refine ⟨Code.bounded_mono hsum ?_,hlen⟩
  simp only [List.length_map]
  exact Nat.mul_le_mul_right (B+1) hlen

theorem shortest_bounded (E : ResidualSearch.Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (cost : V × V → Code) (hc : ∀ e, (cost e).Bounded B)
    (s t : V) {q : Candidate V} (hq : (shortest E G cost s t).1=some q) :
    CandidateBounded q B (Fintype.card V) := by
  unfold shortest at hq
  dsimp only at hq
  split at hq
  · cases hq
  · rename_i r _
    cases hq
    exact recover_bounded E G cost hc s t r.edges

omit [DecidableEq V] [Fintype V] in
/-- The actual natural cross-products used to compare two stored cache costs. -/
lemma comparison_width {a b : Candidate V} (ha : CandidateBounded a B k)
    (hb : CandidateBounded b B k) :
    a.cost.num*b.cost.den ≤ 2^(2*k*(B+1)) ∧
      b.cost.num*a.cost.den ≤ 2^(2*k*(B+1)) := by
  have h := Code.comparison_intermediates ha.1 hb.1
  simpa only [show k*(B+1)+k*(B+1)=2*k*(B+1) by ring] using h

end DirectedFlowCutGap.FractionalCoverRawOracle
