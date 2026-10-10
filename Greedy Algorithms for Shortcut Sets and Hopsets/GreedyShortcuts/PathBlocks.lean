import GreedyShortcuts.PathMedianEdges
import Mathlib.Algebra.Order.Floor.Div

/-! Actual nonempty consecutive blocks, including a short final block. -/
namespace GreedyShortcuts.PathBlocks
open Finset

def count (m b : ℕ) : ℕ := m ⌈/⌉ b

def start (b a : ℕ) : ℕ := a*b

def stop (m b a : ℕ) : ℕ := min ((a+1)*b) m

def size (m b a : ℕ) : ℕ := stop m b a-start b a

def last (m b a : ℕ) : ℕ := stop m b a-1

theorem count_mul_lower (m : ℕ) {b : ℕ} (hb : 0 < b) : m ≤ count m b*b := by
  have h : m ⌈/⌉ b ≤ count m b := le_rfl
  have hh : m ≤ b*count m b := (ceilDiv_le_iff_le_mul hb).mp h
  simpa only [Nat.mul_comm] using hh

theorem count_mul_upper (m b : ℕ) : count m b*b ≤ m+b := by
  have h := Nat.div_mul_le_self (m+b-1) b
  change count m b*b ≤ m+b
  dsimp [count]
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega

theorem index_iff (m a : ℕ) {b : ℕ} (hb : 0 < b) : a < count m b ↔ a*b < m := by
  constructor
  · intro ha
    by_contra hbad
    have hle : count m b ≤ a := (ceilDiv_le_iff_le_mul hb).mpr (by nlinarith)
    omega
  · intro ha
    by_contra hbad
    have hle : m ≤ b*a := (ceilDiv_le_iff_le_mul hb).mp (show count m b ≤ a by omega)
    nlinarith

theorem block_bounds (m a : ℕ) {b : ℕ} (hb : 0 < b) (ha : a < count m b) :
    start b a < stop m b a ∧ stop m b a ≤ m ∧ size m b a ≤ b := by
  have ham := (index_iff m a hb).mp ha
  have has : a*b < min ((a+1)*b) m := lt_min (by nlinarith) ham
  dsimp [start,stop,size]
  have hh : min ((a+1)*b) m ≤ (a+1)*b := min_le_left _ _
  have hmul : (a+1)*b=a*b+b := by ring
  exact ⟨has,min_le_right _ _,by omega⟩

theorem vertex_block {m b i : ℕ} (hb : 0 < b) (hi : i < m) :
    i/b < count m b ∧ start b (i/b) ≤ i ∧ i < stop m b (i/b) := by
  have hm := Nat.div_mul_le_self i b
  have hr := Nat.mod_lt i hb
  have he := Nat.mod_add_div i b
  refine ⟨(index_iff m (i/b) hb).mpr (by omega),hm,?_⟩
  dsimp [stop]
  apply lt_min
  · nlinarith
  · exact hi

/-- The actual block sizes sum to the exact original vertex count. -/
theorem sizes_sum (m : ℕ) {b : ℕ} (hb : 0 < b) :
    ∑ a∈range (count m b),size m b a=m := by
  let f : ℕ → ℕ := fun a => min (a*b) m
  have hf : Monotone f := by
    intro a c hac
    exact min_le_min_right m (Nat.mul_le_mul_right b hac)
  have he := Finset.sum_range_tsub hf (count m b)
  have hterm : ∀ a∈range (count m b),size m b a=f (a+1)-f a := by
    intro a ha
    have hstart : a*b < m := (index_iff m a hb).mp (Finset.mem_range.mp ha)
    simp only [size,stop,start,f,Nat.min_eq_left hstart.le]
  rw [Finset.sum_congr rfl hterm,he]
  have hlast : f (count m b)=m := min_eq_right (count_mul_lower m hb)
  rw [hlast]
  simp [f]

end GreedyShortcuts.PathBlocks
