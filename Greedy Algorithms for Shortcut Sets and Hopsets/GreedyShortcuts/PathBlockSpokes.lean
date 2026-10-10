import GreedyShortcuts.PathBlockEnds
import GreedyShortcuts.PathFourRoutes

/-! Counted one-hop entry/exit spokes for actual nonempty blocks. -/
namespace GreedyShortcuts.PathBlocks
open Finset PathFour

def exits (m b : ℕ) : Finset (ℕ × ℕ) :=
  ((range m).filter (fun i => i < last m b (i/b))).image (fun i => (i,last m b (i/b)))

def entries (m b : ℕ) : Finset (ℕ × ℕ) :=
  ((range m).filter (fun i => start b (i/b) < i)).image (fun i => (start b (i/b),i))

def spokes (m b : ℕ) : Finset (ℕ × ℕ) := exits m b ∪ entries m b

theorem spokes_card (m b : ℕ) : (spokes m b).card ≤ 2*m := by
  have he : (exits m b).card ≤ m := by
    have h1 := Finset.card_image_le (s:=(range m).filter (fun i => i < last m b (i/b)))
      (f:=fun i => (i,last m b (i/b)))
    have h2 := Finset.card_filter_le (range m) (fun i => i < last m b (i/b))
    simpa only [exits,Finset.card_range] using h1.trans h2
  have hi : (entries m b).card ≤ m := by
    have h1 := Finset.card_image_le (s:=(range m).filter (fun i => start b (i/b) < i))
      (f:=fun i => (start b (i/b),i))
    have h2 := Finset.card_filter_le (range m) (fun i => start b (i/b) < i)
    simpa only [entries,Finset.card_range] using h1.trans h2
  have h := Finset.card_union_le (exits m b) (entries m b)
  change (spokes m b).card ≤ _ at h
  omega

theorem last_mem {m b a : ℕ} (ha : a < count m b) : last m b a∈endpoints m b :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_range.mpr ha,rfl⟩)

theorem start_mem {m b a : ℕ} (ha : a < count m b) : start b a∈endpoints m b :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_range.mpr ha,rfl⟩)

theorem spokes_forward {m b : ℕ} (hb : 0 < b) {e : ℕ × ℕ} (he : e∈spokes m b) :
    e.1 < e.2 ∧ e.2 < m := by
  rcases Finset.mem_union.mp he with hexit | hentry
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hexit
    have hii := Finset.mem_filter.mp hi
    exact ⟨hii.2,endpoints_lt hb (last_mem (vertex_block hb (Finset.mem_range.mp hii.1)).1)⟩
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hentry
    have hii := Finset.mem_filter.mp hi
    exact ⟨hii.2,Finset.mem_range.mp hii.1⟩

theorem exit_leg {m b i : ℕ} (hb : 0 < b) (hi : i < m) :
    Leg (spokes m b) i (last m b (i/b)) := by
  have hblock := vertex_block hb hi
  have hle : i ≤ last m b (i/b) := by dsimp [last];omega
  rcases lt_or_eq_of_le hle with hlt | he
  · right
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hlt⟩,rfl⟩)
  · exact Or.inl he

theorem entry_leg {m b i : ℕ} (hb : 0 < b) (hi : i < m) :
    Leg (spokes m b) (start b (i/b)) i := by
  have hblock := vertex_block hb hi
  rcases lt_or_eq_of_le hblock.2.1 with hlt | he
  · right
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hlt⟩,rfl⟩)
  · exact Or.inl he

/-- Distinct ordered blocks are connected in the original forward order. -/
theorem last_lt_next_start {m b a c : ℕ} (hb : 0 < b) (ha : a < count m b) (hac : a < c) :
    last m b a < start b c := by
  have hblock := block_bounds m a hb ha
  have hstop : stop m b a ≤ (a+1)*b := min_le_left _ _
  have hnext := Nat.mul_le_mul_right b (show a+1 ≤ c by omega)
  dsimp [last,start]
  omega

end GreedyShortcuts.PathBlocks
