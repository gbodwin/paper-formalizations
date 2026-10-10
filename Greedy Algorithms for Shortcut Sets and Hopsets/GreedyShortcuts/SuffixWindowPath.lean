import GreedyShortcuts.FamilyWindows
import GreedyShortcuts.CanonicalSegments

/-! The high-score window is an actual contiguous subwalk of a suffix path,
not just an abstract incidence witness. -/
namespace GreedyShortcuts.SuffixWindowPath

open Finset DirectedPaths CanonicalSegments
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def suffixSize {s t : V} (p : DWalk s t) : ℕ := (p.length + 1) / 4

def suffixOffset {s t : V} (p : DWalk s t) : ℕ := p.length + 1 - suffixSize p

theorem sum_shift (f : ℕ → ℕ) (o l r : ℕ) :
    (∑ j ∈ Finset.Icc l r, f (o+j)) = ∑ k ∈ Finset.Icc (o+l) (o+r), f k := by
  apply Finset.sum_bij (fun j _ => o+j)
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro i hi j hj hij
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k-o, Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro j hj
    rfl

theorem exists_suffix_window {s t : I → V} (p : ∀ i, DWalk (s i) (t i))
    (hp : ∀ i, (p i).IsPath) (β : ℕ) (hβ : 8 ≤ β)
    (hL : ∀ i, β < (p i).length) (hpos : 0 < ∑ i, (p i).length) :
    let m := fun i => suffixSize (p i)
    let vertex := fun i j => (p i).getVert (suffixOffset (p i)+j)
    ∃ (i : I) (a c : ℕ) (hac : a ≤ c), suffixOffset (p i) ≤ a ∧ c ≤ (p i).length ∧
      (segment (p i) a c hac).length + 1 ≤ β/8 ∧
      β * (∑ i, (p i).length) ≤ 256 * Fintype.card V *
        ∑ v ∈ (segment (p i) a c hac).support.toFinset, FamilyWindows.deg m vertex v := by
  dsimp only
  let m := fun i => suffixSize (p i)
  let vertex := fun i j => (p i).getVert (suffixOffset (p i)+j)
  let b := β/8
  have hb : 0 < b := by dsimp [b]; omega
  have hm : ∀ i, b ≤ m i := by
    intro i
    have hi := hL i
    dsimp [m,suffixSize,b]
    omega
  have hsizes : (∑ i, (p i).length) ≤ 8 * Fintype.card (FamilyWindows.Slots m) := by
    simp only [FamilyWindows.Slots,Fintype.card_sigma,Fintype.card_fin,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hh := hL i
    dsimp [m,suffixSize]
    omega
  have hslots : 0 < Fintype.card (FamilyWindows.Slots m) := by omega
  obtain ⟨x,hx⟩ := FamilyWindows.exists_window m vertex b hb hm hslots
  let i := x.1
  let a := x.2.val + 1 - b
  let c := min x.2.val (m i - 1)
  have hmpos : 0 < m i := hb.trans_le (hm i)
  have hxrange : x.2.val < m i + b - 1 := x.2.isLt
  have hac : a ≤ c := by dsimp [a,c]; omega
  have hc : c < m i := by dsimp [c]; omega
  have hmL : m i ≤ (p i).length+1 := by dsimp [m,suffixSize]; omega
  have hlast : suffixOffset (p i) + c ≤ (p i).length := by
    change (p i).length+1-m i+c ≤ (p i).length
    omega
  have habs : suffixOffset (p i)+a ≤ suffixOffset (p i)+c := Nat.add_le_add_left hac _
  have hscore : (∑ v ∈ (segment (p i) (suffixOffset (p i)+a)
      (suffixOffset (p i)+c) habs).support.toFinset, FamilyWindows.deg m vertex v) =
      FamilyWindows.windowScore m vertex b x := by
    rw [segment_sum (hp i) habs hlast]
    rw [← sum_shift]
    unfold FamilyWindows.windowScore FiniteWindows.score
    rw [FiniteWindows.nodes_eq _ _ _ hmpos hb hxrange]
  refine ⟨i,suffixOffset (p i)+a,suffixOffset (p i)+c,habs,by omega,hlast,?_,?_⟩
  · rw [segment_length (p i) habs hlast]
    have hn := FiniteWindows.nodes_card_le (m i) b x.2.val hmpos hb hxrange
    rw [FiniteWindows.nodes_eq _ _ _ hmpos hb hxrange,Nat.card_Icc] at hn
    dsimp [a,c,b] at *
    omega
  · rw [hscore]
    have hbeta : β ≤ 16*b := by dsimp [b]; omega
    have hmul := Nat.mul_le_mul hbeta hsizes
    have hw := Nat.mul_le_mul_left 128 hx
    nlinarith

end GreedyShortcuts.SuffixWindowPath
