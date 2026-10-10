import GreedyShortcuts.PathBlocks
import GreedyShortcuts.PathOrderedTwoHop

/-! Deduplicated first/last block endpoints and their real median budget. -/
namespace GreedyShortcuts.PathBlocks
open Finset

def endpoints (m b : ℕ) : Finset ℕ :=
  (range (count m b)).image (start b) ∪ (range (count m b)).image (last m b)

theorem endpoints_card_blocks (m b : ℕ) : (endpoints m b).card ≤ 2*count m b := by
  have h := Finset.card_union_le ((range (count m b)).image (start b))
    ((range (count m b)).image (last m b))
  have h1 : ((range (count m b)).image (start b)).card ≤ count m b := by
    simpa only [Finset.card_range] using
      (Finset.card_image_le (s:=range (count m b)) (f:=start b))
  have h2 : ((range (count m b)).image (last m b)).card ≤ count m b := by
    simpa only [Finset.card_range] using
      (Finset.card_image_le (s:=range (count m b)) (f:=last m b))
  change (endpoints m b).card ≤ _ at h
  omega

theorem endpoints_lt {m b u : ℕ} (hb : 0 < b) (hu : u∈endpoints m b) : u < m := by
  rcases Finset.mem_union.mp hu with h1 | h2
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h1
    have h := block_bounds m a hb (Finset.mem_range.mp ha)
    omega
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h2
    have h := block_bounds m a hb (Finset.mem_range.mp ha)
    dsimp [last]
    omega

theorem endpoints_card (m : ℕ) {b : ℕ} (hb : 0 < b) : (endpoints m b).card ≤ m := by
  have hsub : endpoints m b⊆range m := fun _ h => Finset.mem_range.mpr (endpoints_lt hb h)
  simpa only [Finset.card_range] using Finset.card_le_card hsub

def network (m b : ℕ) : Finset (ℕ × ℕ) :=
  PathMedian.orderedEdges (endpoints m b) (Nat.clog 2 (endpoints m b).card)

/-- The median depth is logarithmic in the actual deduplicated endpoint
count. The block scale is only an accounting upper bound on this depth. -/
theorem network_card {m b : ℕ} (hb : 0 < b) (hbm : b ≤ m) (hm : m ≤ 2^b) :
    (network m b).card ≤ 4*m := by
  have hq := endpoints_card m hb
  have hqb := endpoints_card_blocks m b
  have hdepth : Nat.clog 2 (endpoints m b).card ≤ b :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr (hq.trans hm)
  have hnet := PathMedian.orderedEdges_card (endpoints m b) (Nat.clog 2 (endpoints m b).card)
  have hmul := Nat.mul_le_mul_left (endpoints m b).card hdepth
  have hprod := Nat.mul_le_mul_right b hqb
  have hcount := count_mul_upper m b
  change (network m b).card ≤ _ at hnet
  nlinarith

theorem network_forward {m b : ℕ} (hb : 0 < b) {e : ℕ × ℕ} (he : e∈network m b) :
    e.1 < e.2 ∧ e.2 < m := by
  have h := PathMedian.orderedEdges_forward he
  exact ⟨h.1,endpoints_lt hb h.2.2⟩

end GreedyShortcuts.PathBlocks
