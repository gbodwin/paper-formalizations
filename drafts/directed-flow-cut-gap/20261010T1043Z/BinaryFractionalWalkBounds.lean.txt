import DirectedFlowCutGap.BinaryFractionalWalkOracle
import DirectedFlowCutGap.FractionalCoverRawOracleEncoding

/-!
# Actual operand widths and charges in the binary path oracle

These bounds follow every retained bounded-walk table and every recovered path.
The callback has an explicit stored-field bound and an explicit charge; the
vertex adapter discharges both with its concrete retained-row reads. No
callback is assigned unit charge here. Sequence representation overhead remains
a separate simulation theorem for the shared finite-data instruction model.
-/
namespace DirectedFlowCutGap.BinaryFractionalWalkBounds
open BinaryRational BinaryFractionalWalkOracle
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated
variable {n B C W : ℕ}

def OptionStored (q : Option (Candidate n)) (W : ℕ) : Prop :=
  ∀ p, q=some p → StoredBounded p.cost W

def TableStored (xs : Table n) (W : ℕ) : Prop :=
  ∀ z ∈ xs, StoredBounded z.2.cost W

theorem stored_mono {a : Fraction} {A B : ℕ} (ha : StoredBounded a A) (h : A≤ B) :
    StoredBounded a B := ⟨ha.1.trans h,ha.2.trans h⟩

theorem zero_stored : StoredBounded BinaryRational.zero 1 := by
  norm_num [StoredBounded,BinaryRational.zero]

theorem tableStored_mono {xs : Table n} {A B : ℕ} (h : TableStored xs A) (hab : A≤ B) :
    TableStored xs B := fun z hz => stored_mono (h z hz) hab

theorem extend_stored (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (u v : Fin n) (q : Candidate n) (hq : StoredBounded q.cost W) :
    StoredBounded (extend cost u v q).1.cost (W+B+2) := by
  have h := add_stored_bounded (BinaryFractionalRows.stored_raw_bound (hc (u,v)))
    (BinaryFractionalRows.stored_raw_bound hq)
  simpa only [extend,Nat.add_comm W B] using h

theorem pick_stored (a b : Option (Candidate n)) (ha : OptionStored a W)
    (hb : OptionStored b W) : OptionStored (pick a b).1 W := by
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

theorem scan_stored (adjacency : Adjacency n) (cost : Cost n)
    (hc : ∀ e, StoredBounded (cost e).1 B) (u : Fin n) (xs : Table n)
    (hx : TableStored xs W) : OptionStored (scan adjacency cost u xs).1 (W+B+2) := by
  induction xs with
  | nil => intro q hq; cases hq
  | cons z xs ih =>
    rcases z with ⟨v,p⟩
    have ht := ih (fun z hz => hx z (List.mem_cons_of_mem _ hz))
    unfold scan
    dsimp only
    split
    · apply pick_stored _ _ ?_ ht
      intro q hq
      cases hq
      exact extend_stored cost hc u v p (hx (v,p) List.mem_cons_self)
    · exact ht

theorem atVertex_stored (adjacency : Adjacency n) (cost : Cost n)
    (hc : ∀ e, StoredBounded (cost e).1 B) (t u : Fin n) (xs : Table n)
    (hx : TableStored xs W) : OptionStored (atVertex adjacency cost t u xs).1 (W+B+2) := by
  unfold atVertex
  split
  · intro q hq
    cases hq
    exact stored_mono zero_stored (by omega)
  · exact scan_stored adjacency cost hc u xs hx

theorem pass_stored (adjacency : Adjacency n) (cost : Cost n)
    (hc : ∀ e, StoredBounded (cost e).1 B) (t : Fin n) (old : Table n)
    (vs : List (Fin n)) (ho : TableStored old W) :
    TableStored (BinaryFractionalWalkOracle.pass adjacency cost t old vs).1 (W+B+2) := by
  induction vs with
  | nil => intro z hz; cases hz
  | cons u us ih =>
    intro z hz
    simp only [BinaryFractionalWalkOracle.pass] at hz
    split at hz
    · exact ih z hz
    · rename_i p hp
      rcases List.mem_cons.mp hz with rfl | hz
      · exact atVertex_stored adjacency cost hc t u old ho p hp
      · exact ih z hz

theorem pass_length (adjacency : Adjacency n) (cost : Cost n)
    (t : Fin n) (old : Table n) (vs : List (Fin n)) :
    (BinaryFractionalWalkOracle.pass adjacency cost t old vs).1.length ≤ vs.length := by
  induction vs with
  | nil => simp [BinaryFractionalWalkOracle.pass]
  | cons u us ih =>
    simp only [BinaryFractionalWalkOracle.pass,List.length_cons]
    split <;> simp only [List.length_cons] <;> omega

theorem rounds_stored (vs : List (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (t : Fin n) (fuel : List (Fin n)) :
    TableStored (rounds vs adjacency cost t fuel).1 (fuel.length*(B+2)+1) := by
  induction fuel with
  | nil =>
    intro z hz
    simp only [rounds,List.mem_singleton] at hz
    subst z
    simpa only [BinaryFractionalWalkOracle.zero,List.length_nil,Nat.zero_mul,Nat.zero_add] using zero_stored
  | cons u us ih =>
    have h := pass_stored adjacency cost hc t (rounds vs adjacency cost t us).1 vs ih
    simpa only [rounds,List.length_cons,show (us.length+1)*(B+2)+1=
      us.length*(B+2)+1+B+2 by ring] using h

theorem rounds_length (vs : List (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (t : Fin n) (fuel : List (Fin n)) :
    (rounds vs adjacency cost t fuel).1.length ≤ vs.length+1 := by
  cases fuel with
  | nil => simp [rounds]
  | cons u us => exact (pass_length adjacency cost t _ vs).trans (Nat.le_succ _)

theorem lookup_stored (u : Fin n) (xs : Table n) (hx : TableStored xs W) :
    OptionStored (lookup u xs).1 W := by
  induction xs with
  | nil => intro q hq; cases hq
  | cons z xs ih =>
    rcases z with ⟨v,p⟩
    have ht := ih (fun z hz => hx z (List.mem_cons_of_mem _ hz))
    unfold lookup
    dsimp only
    split
    · apply pick_stored _ _ ?_ ht
      intro q hq
      cases hq
      exact hx (v,p) List.mem_cons_self
    · exact ht

/-- The shared matrix callback performs two fixed reads. -/
theorem adjacent_charge (adjacency : Adjacency n) (u v : Fin n) :
    (adjacent adjacency u v).2=18 := rfl

def relaxBound (W B C : ℕ) : ℕ := C+4096*(W+B+3)^2+64

theorem relaxBound_mono {A W : ℕ} (h : A≤ W) (B C : ℕ) :
    relaxBound A B C ≤ relaxBound W B C := by
  unfold relaxBound
  have hsq : (A+B+3)^2 ≤ (W+B+3)^2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith

theorem pick_charge (a b : Option (Candidate n)) (ha : OptionStored a W)
    (hb : OptionStored b W) : (pick a b).2 ≤ 2048*(W+1)^2+6 := by
  cases a with
  | none => simp [pick]
  | some a =>
    cases b with
    | none => simp [pick]
    | some b =>
      have h := le_charge (ha a rfl) (hb b rfl)
      simpa only [pick] using Nat.add_le_add_right h 6

theorem extend_charge (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (hw : ∀ e, (cost e).2≤ C) (u v : Fin n) (q : Candidate n)
    (hq : StoredBounded q.cost W) :
    (extend cost u v q).2 ≤ C+2048*(W+B+3)^2+8 := by
  have ha := add_charge (stored_mono (hc (u,v)) (show B≤ W+B+2 by omega))
    (stored_mono hq (show W≤ W+B+2 by omega))
  have hw' := hw (u,v)
  simp only [extend]
  nlinarith

theorem scan_charge (adjacency : Adjacency n) (cost : Cost n)
    (hc : ∀ e, StoredBounded (cost e).1 B) (hw : ∀ e, (cost e).2≤ C)
    (u : Fin n) (xs : Table n) (hx : TableStored xs W) :
    (scan adjacency cost u xs).2 ≤ xs.length*relaxBound W B C+1 := by
  induction xs with
  | nil => simp [scan]
  | cons z xs ih =>
    rcases z with ⟨v,p⟩
    have hp := hx (v,p) List.mem_cons_self
    have ht : TableStored xs W := fun z hz => hx z (List.mem_cons_of_mem _ hz)
    have hi := ih ht
    have he := extend_charge cost hc hw u v p hp
    have hs := scan_stored adjacency cost hc u xs ht
    have hpick := pick_charge (some (extend cost u v p).1) (scan adjacency cost u xs).1
      (fun q hq => by cases hq; exact extend_stored cost hc u v p hp) hs
    simp only [scan,List.length_cons]
    split <;> simp only [adjacent_charge] <;> unfold relaxBound at * <;> nlinarith

theorem atVertex_charge (adjacency : Adjacency n) (cost : Cost n)
    (hc : ∀ e, StoredBounded (cost e).1 B) (hw : ∀ e, (cost e).2≤ C)
    (t u : Fin n) (xs : Table n) (hx : TableStored xs W) :
    (atVertex adjacency cost t u xs).2 ≤ xs.length*relaxBound W B C+7 := by
  have h := scan_charge adjacency cost hc hw u xs hx
  unfold atVertex
  split <;> dsimp only <;> omega

def passBound (N W B C : ℕ) : ℕ := N*((N+1)*relaxBound W B C+17)+1

theorem pass_charge (adjacency : Adjacency n) (cost : Cost n)
    (hc : ∀ e, StoredBounded (cost e).1 B) (hw : ∀ e, (cost e).2≤ C)
    (t : Fin n) (old : Table n) (vs : List (Fin n)) (ho : TableStored old W) :
    (BinaryFractionalWalkOracle.pass adjacency cost t old vs).2 ≤ vs.length*(old.length*relaxBound W B C+17)+1 := by
  induction vs with
  | nil => simp [BinaryFractionalWalkOracle.pass]
  | cons u us ih =>
    have h := atVertex_charge adjacency cost hc hw t u old ho
    simp only [BinaryFractionalWalkOracle.pass,List.length_cons]
    split <;> nlinarith

def roundsBound (N W B C K : ℕ) : ℕ := K*(passBound N W B C+6)+8

theorem rounds_charge (vs : List (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (hw : ∀ e, (cost e).2≤ C) (t : Fin n) (fuel : List (Fin n)) (K : ℕ)
    (hk : fuel.length≤ K) :
    (rounds vs adjacency cost t fuel).2 ≤
      roundsBound vs.length (K*(B+2)+1) B C fuel.length := by
  induction fuel with
  | nil => simp [rounds,roundsBound]
  | cons u us ih =>
    have hlen : us.length≤ K := by simp only [List.length_cons] at hk; omega
    have hi := ih hlen
    have hs := tableStored_mono (rounds_stored vs adjacency cost hc t us)
      (Nat.add_le_add_right (Nat.mul_le_mul_right (B+2) hlen) 1)
    have hp := pass_charge adjacency cost hc hw t (rounds vs adjacency cost t us).1 vs hs
    have hl := rounds_length vs adjacency cost t us
    have hm := Nat.mul_le_mul_right (relaxBound (K*(B+2)+1) B C) hl
    have hm' := Nat.mul_le_mul_left vs.length (Nat.add_le_add_right hm 17)
    simp only [rounds,List.length_cons]
    unfold roundsBound passBound at *
    nlinarith

theorem lookup_charge (u : Fin n) (xs : Table n) (hx : TableStored xs W) :
    (lookup u xs).2 ≤ xs.length*(2048*(W+1)^2+12)+1 := by
  induction xs with
  | nil => simp [lookup]
  | cons z xs ih =>
    rcases z with ⟨v,p⟩
    have ht : TableStored xs W := fun z hz => hx z (List.mem_cons_of_mem _ hz)
    have hi := ih ht
    have hp := pick_charge (some p) (lookup u xs).1
      (fun q hq => by cases hq; exact hx (v,p) List.mem_cons_self)
      (lookup_stored u xs ht)
    simp only [lookup,List.length_cons]
    split <;> nlinarith

def minimizeBound (N B C : ℕ) : ℕ :=
  roundsBound N (N*(B+2)+1) B C N+(N+1)*(2048*(N*(B+2)+2)^2+12)+8*N+9

theorem minimize_charge (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (hw : ∀ e, (cost e).2≤ C) (s t : Fin n) :
    (minimize E adjacency cost s t).2 ≤ minimizeBound E.vertices.length B C := by
  have hr := rounds_charge E.vertices adjacency cost hc hw t E.vertices E.vertices.length le_rfl
  have hl := rounds_length E.vertices adjacency cost t E.vertices
  have hs := rounds_stored E.vertices adjacency cost hc t E.vertices
  have hq := lookup_charge s (rounds E.vertices adjacency cost t E.vertices).1 hs
  have hm := Nat.mul_le_mul_right (2048*(E.vertices.length*(B+2)+2)^2+12) hl
  simp only [minimize]
  unfold minimizeBound
  nlinarith

theorem memberEdge_charge (e : Pair n) (es : List (Pair n)) :
    (memberEdge e es).2 ≤ 8*es.length+1 := by
  induction es with
  | nil => simp [memberEdge]
  | cons a as ih =>
    simp only [memberEdge,List.length_cons]
    split <;> dsimp only <;> omega

theorem supportTest_charge (adjacency : Adjacency n) (es : List (Pair n)) (u v : Fin n) :
    (supportTest adjacency es u v).2 ≤ 8*es.length+27 := by
  have hm := memberEdge_charge (u,v) es
  unfold supportTest
  dsimp only
  split <;> simp only [adjacent_charge] <;> omega

theorem costList_length (cost : Cost n) (es : List (Pair n)) :
    (costList cost es).1.length=es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [costList,List.length_cons] using congrArg Nat.succ ih

theorem costList_stored (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (es : List (Pair n)) : ∀ q ∈ (costList cost es).1, StoredBounded q B := by
  induction es with
  | nil => simp [costList]
  | cons e es ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hc e
    · exact ih q hq

theorem costList_charge (cost : Cost n) (hw : ∀ e, (cost e).2≤ C) (es : List (Pair n)) :
    (costList cost es).2 ≤ es.length*(C+6)+1 := by
  induction es with
  | nil => simp [costList]
  | cons e es ih =>
    have h := hw e
    simp only [costList,List.length_cons]
    nlinarith

theorem sumBound_mono {a b B : ℕ} (h : a≤ b) :
    BinaryFractionalRows.sumBound a B ≤ BinaryFractionalRows.sumBound b B := by
  have ha : (a+1)*(B+1)+1 ≤ (b+1)*(B+1)+1 := by nlinarith
  have hp := Nat.pow_le_pow_left ha 2
  have hm := Nat.mul_le_mul h (Nat.add_le_add_right (Nat.mul_le_mul_left 2048 hp) 4)
  exact Nat.add_le_add_right hm 1

def recoverBound (n L B C : ℕ) : ℕ :=
  RetainedPathSearch.searchBound n (8*L+27)+n*(C+6)+BinaryFractionalRows.sumBound n B+9

theorem recover_stored (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (s t : Fin n) (es : List (Pair n)) :
    StoredBounded (recover E adjacency cost s t es).1.cost (n*(B+1)+1) := by
  let r := RetainedPathSearch.search E (supportTest adjacency es) s t
  have hl : r.edges.length≤ n := by simpa using r.edges_length_le
  have hs := BinaryFractionalRows.sum_stored_bound (costList cost r.edges).1 B
    (fun q hq => BinaryFractionalRows.stored_raw_bound (costList_stored cost hc r.edges q hq))
  rw [costList_length] at hs
  exact stored_mono hs (Nat.add_le_add_right (Nat.mul_le_mul_right (B+1) hl) 1)

theorem recover_charge (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (hw : ∀ e, (cost e).2≤ C) (s t : Fin n) (es : List (Pair n)) :
    (recover E adjacency cost s t es).2 ≤ recoverBound n es.length B C := by
  let r := RetainedPathSearch.search E (supportTest adjacency es) s t
  have hl : r.edges.length≤ n := by simpa using r.edges_length_le
  have hs : r.work≤ RetainedPathSearch.searchBound n (8*es.length+27) := by
    simpa only [Fintype.card_fin] using RetainedPathSearch.search_bound E
      (supportTest adjacency es) (8*es.length+27) (supportTest_charge adjacency es) s t
  have hv := costList_charge cost hw r.edges
  have hm := Nat.mul_le_mul_right (C+6) hl
  have ha := BinaryFractionalRows.sum_charge (costList cost r.edges).1 B
    (costList_stored cost hc r.edges)
  rw [costList_length] at ha
  have hb := sumBound_mono (B := B) hl
  change r.work+(costList cost r.edges).2+
    (BinaryFractionalRows.sum (costList cost r.edges).1).2+8 ≤ _
  unfold recoverBound
  omega

theorem minimize_edges_length (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (s t : Fin n) {q : Candidate n} (hq : (minimize E adjacency cost s t).1=some q) :
    q.edges.length≤ n := by
  have hd := minimize_decode E adjacency cost s t
  rw [hq,Option.map_some] at hd
  have hb := FractionalCoverRawOracle.minimize_bounded E (graph adjacency) (decodeCost cost)
    (fun e => BinaryFractionalRows.stored_raw_bound (hc e)) s t hd.symm
  simpa only [BinaryFractionalWalkOracle.decode,E.length_eq_card,Fintype.card_fin] using hb.2

def shortestBound (n B C : ℕ) : ℕ := minimizeBound n B C+recoverBound n n B C+6

theorem shortest_stored (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (s t : Fin n) : OptionStored (shortest E adjacency cost s t).1 (n*(B+1)+1) := by
  unfold shortest
  dsimp only
  split
  · intro q hq; cases hq
  · rename_i p _
    intro q hq
    cases hq
    exact recover_stored E adjacency cost hc s t p.edges

theorem shortest_charge (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (hc : ∀ e, StoredBounded (cost e).1 B)
    (hw : ∀ e, (cost e).2≤ C) (s t : Fin n) :
    (shortest E adjacency cost s t).2 ≤ shortestBound n B C := by
  have hm := minimize_charge E adjacency cost hc hw s t
  rw [E.length_eq_card,Fintype.card_fin] at hm
  unfold shortest
  dsimp only
  split
  · unfold shortestBound; omega
  · rename_i q hq
    have hl := minimize_edges_length E adjacency cost hc s t hq
    have hr := recover_charge E adjacency cost hc hw s t q.edges
    have hmono : recoverBound n q.edges.length B C ≤ recoverBound n n B C := by
      unfold recoverBound RetainedPathSearch.searchBound RetainedPathSearch.visitBound
      gcongr
    unfold shortestBound
    omega

end DirectedFlowCutGap.BinaryFractionalWalkBounds
