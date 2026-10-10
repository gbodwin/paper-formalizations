import GreedyShortcuts.PathBlockGlue
import GreedyShortcuts.PathRouteWitness

/-! Tower-scale finite-depth four-hop path preprocessing. Only actual block
vertices and the deduplicated logarithmic-depth endpoint network are used. -/
namespace GreedyShortcuts.PathFour
open Finset PathBlocks

def tower : ℕ → ℕ
  | 0 => 2
  | d+1 => 2^(tower d)

theorem tower_two_le (d : ℕ) : 2 ≤ tower d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change 2 ≤ 2^(tower d)
    exact ih.trans (Nat.lt_two_pow_self (n:=tower d)).le

def edges : ℕ → ℕ → Finset (ℕ × ℕ)
  | 0,m => PathMedian.edges 1 m
  | d+1,m => if m ≤ tower d then edges d m else PathBlocks.glue m (tower d) (edges d)

/-- At a sufficient finite tower depth, this exact edge set is forward,
uses at most (6d+1)m edges and provides four actual edge-or-equality legs. -/
theorem edges_spec (d m : ℕ) (hm : m ≤ tower d) :
    (∀ e∈edges d m,e.1 < e.2 ∧ e.2 < m) ∧
    (edges d m).card ≤ (6*d+1)*m ∧
    ∀ i j,i ≤ j → j < m → Route (edges d m) i j := by
  induction d generalizing m with
  | zero =>
    refine ⟨fun e he => PathMedian.edges_forward 1 m he,?_,?_⟩
    · simpa only [edges,Nat.mul_zero,Nat.zero_add,Nat.one_mul,Nat.mul_one] using
        PathMedian.edges_card 1 m
    · intro i j hij hj
      apply median_route 1 m i j
      · simpa only [tower,pow_one] using hm
      · exact hij
      · exact hj
  | succ d ih =>
    have hb : 0 < tower d := by have := tower_two_le d;omega
    by_cases hsmall : m ≤ tower d
    · have old := ih m hsmall
      simp only [edges,hsmall,ite_true]
      refine ⟨old.1,?_,old.2.2⟩
      nlinarith [old.2.1]
    · have hchildren := fun s hs => ih s hs
      simp only [edges,hsmall,ite_false]
      refine ⟨?_,?_,?_⟩
      · exact fun e he => PathBlocks.glue_forward hb (edges d)
          (fun s hs => (hchildren s hs).1) he
      · have hcard := PathBlocks.glue_card hb (by omega : tower d ≤ m) hm (edges d)
          (fun s hs => (hchildren s hs).2.1)
        convert hcard using 1
      · exact fun i j hij hj => PathBlocks.glue_route hb (edges d)
          (fun s hs => (hchildren s hs).2.2) i j hij hj

def towerWitness (d m : ℕ) (hm : m ≤ tower d) : ChainUnion.PathWitness m (6*d+1) :=
  witness m (6*d+1) (edges d m) (edges_spec d m hm).1
    (edges_spec d m hm).2.1 (edges_spec d m hm).2.2

end GreedyShortcuts.PathFour
