import DirectedFlowCutGap.SupportSearchAccounts

/-! Bounds for the actual scans, in stored word widths and represented matrix
indices. These account for both real numeric comparisons and matrix reads. -/
namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic

def WordBound (W N : ℕ) (u : Bits) : Prop := u.length ≤ W ∧ value u ≤ N
def EdgeWidths (W : ℕ) (e : Bits × Bits) : Prop := e.1.length ≤ W ∧ e.2.length ≤ W

theorem edge_steps_le (W : ℕ) (e f : Bits × Bits) (he : EdgeWidths W e) (hf : EdgeWidths W f) :
    edgeSteps e f ≤ 64*W+49 := by
  have h1 := BinaryComparisonProgram.steps_bound e.1 f.1
  have h2 := BinaryComparisonProgram.steps_bound e.2 f.2
  obtain ⟨he1,he2⟩ := he
  obtain ⟨hf1,hf2⟩ := hf
  unfold edgeSteps
  split <;> omega

theorem member_steps_le (W : ℕ) (e : Bits × Bits) (es : List (Bits × Bits))
    (he : EdgeWidths W e) (hs : ∀ f∈es,EdgeWidths W f) :
    memberSteps e es ≤ es.length*(64*W+57)+3 := by
  induction es with
  | nil => simp [memberSteps]
  | cons f fs ih =>
    have hh := edge_steps_le W f e (hs f (by simp)) he
    have ht := ih (fun g hg => hs g (by simp [hg]))
    simp only [memberSteps,List.length_cons,Nat.add_mul,Nat.one_mul]
    split <;> omega

theorem adjacency_steps_le (W N : ℕ) (u v : Bits) (hu : WordBound W N u) (hv : WordBound W N v) :
    GraphAdjacencyProgram.steps u v ≤ 12*N+20*W+29 := by
  have h1 := BinaryPointerListRead.steps_bound u
  have h2 := BinaryPointerListRead.steps_bound v
  obtain ⟨hul,huv⟩ := hu
  obtain ⟨hvl,hvv⟩ := hv
  unfold GraphAdjacencyProgram.steps
  omega

def supportCap (S W N : ℕ) : ℕ := S*(64*W+57)+12*N+20*W+46

theorem support_steps_le (W N : ℕ) (adjacency : List Bits) (es : List (Bits × Bits)) (u v : Bits)
    (hu : WordBound W N u) (hv : WordBound W N v) (hs : ∀ e∈es,EdgeWidths W e) :
    supportSteps adjacency es u v ≤ supportCap es.length W N := by
  have ha := adjacency_steps_le W N u v hu hv
  have hm := member_steps_le W (u,v) es ⟨hu.1,hv.1⟩ hs
  unfold supportSteps supportCap
  split <;> omega

theorem lookup_steps_le (W : ℕ) (u : Bits) (xs : List Code)
    (hu : u.length ≤ W) (hx : ∀ x∈xs,x.1.length ≤ W) :
    lookupSteps u xs ≤ xs.length*(32*W+27)+3 := by
  induction xs with
  | nil => simp [lookupSteps]
  | cons x xs ih =>
    have hh := BinaryComparisonProgram.steps_bound x.1 u
    have hl := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [lookupSteps,List.length_cons,Nat.add_mul,Nat.one_mul]
    split <;> omega

theorem pred_steps_le (W N : ℕ) (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits)
    (xs : List Code) (hu : WordBound W N u) (hx : ∀ x∈xs,WordBound W N x.1)
    (hs : ∀ e∈es,EdgeWidths W e) :
    predSteps adjacency es u xs ≤ xs.length*(supportCap es.length W N+14)+3 := by
  induction xs with
  | nil => simp [predSteps]
  | cons x xs ih =>
    have hh := support_steps_le W N adjacency es u x.1 hu (hx x (by simp)) hs
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [predSteps,List.length_cons,Nat.add_mul,Nat.one_mul]
    split <;> omega

def scanCap (S W N : ℕ) : ℕ := S*(64*W+57)+12*N+52*W+87

theorem visit_steps_le (W N : ℕ) (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits)
    (xs : List Code) (hu : WordBound W N u) (hx : ∀ x∈xs,WordBound W N x.1)
    (hs : ∀ e∈es,EdgeWidths W e) :
    visitSteps adjacency es u xs ≤ xs.length*scanCap es.length W N+29 := by
  have hl := lookup_steps_le W u xs hu.1 (fun x h => (hx x h).1)
  have hp := pred_steps_le W N adjacency es u xs hu hx hs
  unfold visitSteps
  cases hlook : lookup u xs <;> simp only
  · cases hpred : predecessor adjacency es u xs <;> simp only
    all_goals dsimp only [scanCap,supportCap] at *
    all_goals nlinarith
  · dsimp only [scanCap,supportCap] at *
    nlinarith

end DirectedFlowCutGap.SupportRecoveryProgram
