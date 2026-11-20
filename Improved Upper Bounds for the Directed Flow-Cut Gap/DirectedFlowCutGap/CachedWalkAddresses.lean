import DirectedFlowCutGap.PaidCacheTrace

/-! Place the exact three-array traces for every completed cached allocation
in the order the fuel-free guard can execute them. -/
namespace DirectedFlowCutGap.PaidCacheTrace

open ImmutableReferenceSimulation
open CachedReferenceExecution (FastState)
open TotalGuardedPackedExecution (Next)
open CachedHeapCopies (appendBlocks append_end append_address)

def placeStep {C : ℕ} (p : Program C) (s : FastState C) (start : ℕ) : ℕ × List (ℕ × ℕ) :=
  match allocation p s with
  | none => (start,[])
  | some c => appendBlocks s.store c start

theorem placeStep_end {C : ℕ} (p : Program C) (s : FastState C) (start : ℕ) :
    (placeStep p s start).1=start+(traffic p s).1 := by
  unfold placeStep traffic
  cases choice : allocation p s with
  | none => simp only [Nat.add_zero]
  | some c => simpa only [Nat.add_assoc] using append_end s.store c start

theorem placeStep_address {C : ℕ} (p : Program C) (s : FastState C) (start : ℕ)
    (block : ℕ × ℕ) (placed : block ∈ (placeStep p s start).2) (offset : ℕ) (valid : offset<block.2) :
    start ≤ block.1+offset ∧ block.1+offset < start+(traffic p s).1 := by
  unfold placeStep at placed
  unfold traffic
  cases choice : allocation p s with
  | none => simp only [choice,List.not_mem_nil] at placed
  | some c =>
      simp only [choice] at placed
      simpa only [Nat.add_assoc] using append_address placed offset valid

inductive Layout {C : ℕ} (p : Program C) :
    FastState C → ℕ → FastState C → ℕ → List (ℕ × ℕ) → Prop where
  | done (s : FastState C) (start : ℕ) : Layout p s start s start []
  | step {s next final : FastState C} {start finish : ℕ} {blocks : List (ℕ × ℕ)} :
      Next p next s → Layout p next (placeStep p s start).1 final finish blocks →
      Layout p s start final finish ((placeStep p s start).2++blocks)

theorem Walk.layout {C steps cells copies : ℕ} {p : Program C} {initial final : FastState C}
    (observed : Walk p initial steps cells copies final) (start : ℕ) :
    ∃ blocks, Layout p initial start final (start+cells) blocks ∧
      ∀ (block : ℕ × ℕ), block ∈ blocks → ∀ offset<block.2,
        start ≤ block.1+offset ∧ block.1+offset < start+cells := by
  induction observed generalizing start with
  | done state => exact ⟨[],by simpa using Layout.done (p:=p) state start,by simp⟩
  | @step state next final k allocated copied progress rest ih =>
      let placed := placeStep p state start
      obtain ⟨later,tail,addresses⟩ := ih placed.1
      have endFirst : placed.1=start+(traffic p state).1 := placeStep_end p state start
      have endAll : placed.1+allocated=start+((traffic p state).1+allocated) := by rw [endFirst,Nat.add_assoc]
      refine ⟨placed.2++later,?_,?_⟩
      · rw [← endAll]
        exact Layout.step progress tail
      · intro block membership offset valid
        rcases List.mem_append.mp membership with first|after
        · obtain ⟨lo,hi⟩ := placeStep_address p state start block first offset valid
          exact ⟨lo,hi.trans_le (by omega)⟩
        · obtain ⟨lo,hi⟩ := addresses block after offset valid
          constructor <;> omega

theorem Walk.address_width {C steps cells copies : ℕ} {p : Program C} {initial final : FastState C}
    (observed : Walk p initial steps cells copies final) (start : ℕ) :
    ∃ blocks, Layout p initial start final (start+cells) blocks ∧
      ∀ block ∈ blocks, ∀ offset<block.2, (block.1+offset).size ≤ (start+cells).size := by
  obtain ⟨blocks,placed,bounds⟩ := observed.layout start
  exact ⟨blocks,placed,fun block member offset valid => Nat.size_le_size (bounds block member offset valid).2.le⟩

end DirectedFlowCutGap.PaidCacheTrace
