import GreedyShortcuts.ChainFirst
import Mathlib.Data.Finset.Sort

/-! A finite maximal packing of uniformly sized reachability chains.
This is an existence construction, with no efficient-runtime claim. -/
namespace GreedyShortcuts.UniformChainPacking
open Finset DirectedPaths ChainUnion
variable {V : Type*} [Fintype V] [DecidableEq V]

def FixedChain (G : V → V → Prop) (r : ℕ) :=
  {f : Fin r → V // Function.Injective f ∧ ∀ i j,i < j → Reachable G (f i) (f j)}

noncomputable instance (G : V → V → Prop) (r : ℕ) : Fintype (FixedChain G r) :=
  by unfold FixedChain; exact Fintype.ofFinite _

instance (G : V → V → Prop) (r : ℕ) : DecidableEq (FixedChain G r) :=
  inferInstanceAs (DecidableEq {_f : Fin r → V // _})

def FixedChain.chain {G : V → V → Prop} {r : ℕ} (c : FixedChain G r) : Chain G :=
  ⟨r,c.1,c.2.1,c.2.2⟩

def Compatible {G : V → V → Prop} {r : ℕ} (S : Finset (FixedChain G r)) : Prop :=
  ∀ a∈S,∀ b∈S,a≠b → Disjoint a.chain.support b.chain.support

theorem exists_packing (G : V → V → Prop) (r : ℕ) :
    ∃ S : Finset (FixedChain G r),Compatible S ∧
      ∀ J : Finset (FixedChain G r),Compatible J → J.card ≤ S.card := by
  classical
  let F := (Finset.univ : Finset (FixedChain G r)).powerset.filter Compatible
  have hn : F.Nonempty := ⟨∅,by simp [F,Compatible]⟩
  obtain ⟨S,hS,hmax⟩ := Finset.exists_max_image F Finset.card hn
  refine ⟨S,(Finset.mem_filter.mp hS).2,?_⟩
  intro J hJ
  exact hmax J (by simp [F,hJ])

noncomputable def packing (G : V → V → Prop) (r : ℕ) : Finset (FixedChain G r) :=
  Classical.choose (exists_packing G r)

theorem packing_spec (G : V → V → Prop) (r : ℕ) :
    Compatible (packing G r) ∧
    ∀ S : Finset (FixedChain G r),Compatible S → S.card ≤ (packing G r).card :=
  Classical.choose_spec (exists_packing G r)

theorem mem_packing_of_disjoint (G : V → V → Prop) (r : ℕ) (c : FixedChain G r)
    (h : ∀ d∈packing G r,Disjoint c.chain.support d.chain.support) : c∈packing G r := by
  classical
  by_contra hc
  have hp : Compatible (insert c (packing G r)) := by
    intro a ha b hb hab
    by_cases hac : a=c
    · subst a
      have hb' : b∈packing G r := (Finset.mem_insert.mp hb).resolve_left
        (fun hbc => hab hbc.symm)
      exact h b hb'
    · have ha' : a∈packing G r := (Finset.mem_insert.mp ha).resolve_left hac
      by_cases hbc : b=c
      · subst b
        exact (h a ha').symm
      · have hb' : b∈packing G r := (Finset.mem_insert.mp hb).resolve_left hbc
        exact (packing_spec G r).1 a ha' b hb' hab
  have hm := (packing_spec G r).2 _ hp
  rw [Finset.card_insert_of_notMem hc] at hm
  omega

def chains (G : V → V → Prop) (r : ℕ) : {c // c∈packing G r} → Chain G :=
  fun c => c.1.chain

theorem chains_disjoint (G : V → V → Prop) (r : ℕ) :
    Pairwise (fun i j : {c // c∈packing G r} =>
      Disjoint (chains G r i).support (chains G r j).support) := by
  intro i j hij
  exact (packing_spec G r).1 i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))

theorem packing_card_mul (G : V → V → Prop) (r : ℕ) :
    (packing G r).card*r≤Fintype.card V := by
  have h := ChainUnion.disjoint_length_sum (chains G r) (chains_disjoint G r)
  simpa [chains,FixedChain.chain] using h

theorem packing_card_le (G : V → V → Prop) (r : ℕ) (hr : 0<r) :
    (packing G r).card≤Fintype.card V/r :=
  (Nat.le_div_iff_mul_le hr).mpr (packing_card_mul G r)

end GreedyShortcuts.UniformChainPacking
