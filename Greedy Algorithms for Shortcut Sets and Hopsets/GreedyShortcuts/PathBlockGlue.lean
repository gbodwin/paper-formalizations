import GreedyShortcuts.PathBlockSpokes

/-! A real block union: child routes stay in their block and cross-block
routes use two counted spokes plus a literal two-hop endpoint network. -/
namespace GreedyShortcuts.PathBlocks
open Finset PathFour

def children (m b : ℕ) (F : ℕ → Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (range (count m b)).biUnion (fun a => PathMedian.shift (start b a) (F (size m b a)))

def glue (m b : ℕ) (F : ℕ → Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (spokes m b ∪ network m b) ∪ children m b F

theorem children_subset {m b a : ℕ} (F : ℕ → Finset (ℕ × ℕ)) (ha : a < count m b) :
    PathMedian.shift (start b a) (F (size m b a))⊆children m b F := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_range.mpr ha,he⟩

theorem children_card (m K : ℕ) {b : ℕ} (hb : 0 < b) (F : ℕ → Finset (ℕ × ℕ))
    (hF : ∀ s ≤ b,(F s).card ≤ K*s) : (children m b F).card ≤ K*m := by
  calc
    (children m b F).card ≤ ∑ a∈range (count m b),
        (PathMedian.shift (start b a) (F (size m b a))).card := Finset.card_biUnion_le
    _ ≤ ∑ a∈range (count m b),K*size m b a := by
      apply Finset.sum_le_sum
      intro a ha
      exact (PathMedian.shift_card _ _).trans
        (hF _ (block_bounds m a hb (Finset.mem_range.mp ha)).2.2)
    _=K*m := by rw [← Finset.mul_sum,sizes_sum m hb]

theorem children_forward {m b : ℕ} (hb : 0 < b) (F : ℕ → Finset (ℕ × ℕ))
    (hF : ∀ s ≤ b,∀ e∈F s,e.1 < e.2 ∧ e.2 < s) {e : ℕ × ℕ} (he : e∈children m b F) :
    e.1 < e.2 ∧ e.2 < m := by
  obtain ⟨a,ha,he⟩ := Finset.mem_biUnion.mp he
  have hblock := block_bounds m a hb (Finset.mem_range.mp ha)
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  have hq' := hF _ hblock.2.2 q hq
  have hs : start b a+size m b a=stop m b a := by dsimp [size];omega
  dsimp only
  omega

theorem glue_card {m b K : ℕ} (hb : 0 < b) (hbm : b ≤ m) (hm : m ≤ 2^b)
    (F : ℕ → Finset (ℕ × ℕ)) (hF : ∀ s ≤ b,(F s).card ≤ K*s) :
    (glue m b F).card ≤ (K+6)*m := by
  have h1 := Finset.card_union_le (spokes m b) (network m b)
  have h2 := Finset.card_union_le (spokes m b ∪ network m b) (children m b F)
  have hs := spokes_card m b
  have hn := network_card hb hbm hm
  have hc := children_card m K hb F hF
  change (glue m b F).card ≤ _ at h2
  nlinarith

theorem glue_forward {m b : ℕ} (hb : 0 < b) (F : ℕ → Finset (ℕ × ℕ))
    (hF : ∀ s ≤ b,∀ e∈F s,e.1 < e.2 ∧ e.2 < s) {e : ℕ × ℕ} (he : e∈glue m b F) :
    e.1 < e.2 ∧ e.2 < m := by
  rcases Finset.mem_union.mp he with hleft | hright
  · rcases Finset.mem_union.mp hleft with hs | hn
    · exact spokes_forward hb hs
    · exact network_forward hb hn
  · exact children_forward hb F hF hright

theorem glue_route {m b : ℕ} (hb : 0 < b) (F : ℕ → Finset (ℕ × ℕ))
    (hF : ∀ s ≤ b,∀ i j,i ≤ j → j < s → Route (F s) i j)
    (i j : ℕ) (hij : i ≤ j) (hj : j < m) : Route (glue m b F) i j := by
  have hi : i < m := hij.trans_lt hj
  have hib := vertex_block hb hi
  have hjb := vertex_block hb hj
  have hspokes : spokes m b⊆glue m b F := fun _ h =>
    Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hnetwork : network m b⊆glue m b F := fun _ h =>
    Finset.mem_union_left _ (Finset.mem_union_right _ h)
  by_cases he : i/b=j/b
  · let a := i/b
    have hblock := block_bounds m a hb hib.1
    have his : start b a ≤ i := hib.2.1
    have hjs : start b a ≤ j := his.trans hij
    have hjstop : j < stop m b a := by simpa only [a,he] using hjb.2.2
    have hshort := hF (size m b a) hblock.2.2 (i-start b a) (j-start b a)
      (by omega) (by dsimp [size];omega)
    have hshift := route_shift (start b a) hshort
    have hsub : PathMedian.shift (start b a) (F (size m b a))⊆glue m b F :=
      fun _ h => Finset.mem_union_right _ (children_subset F hib.1 h)
    have hout := route_mono hsub hshift
    simpa only [Nat.add_sub_of_le his,Nat.add_sub_of_le hjs] using hout
  · have hbc : i/b < j/b := lt_of_le_of_ne (Nat.div_le_div_right hij) he
    have hxy := last_lt_next_start hb hib.1 hbc
    obtain ⟨z,_,_,_,hxz,hzy⟩ := PathMedian.ordered_two_legs (endpoints m b)
      (Nat.clog 2 (endpoints m b).card) (Nat.le_pow_clog (by decide) _)
      (last_mem hib.1) (start_mem hjb.1) hxy.le
    exact ⟨last m b (i/b),z,start b (j/b),leg_mono hspokes (exit_leg hb hi),
      leg_mono hnetwork hxz,leg_mono hnetwork hzy,leg_mono hspokes (entry_leg hb hj)⟩

end GreedyShortcuts.PathBlocks
