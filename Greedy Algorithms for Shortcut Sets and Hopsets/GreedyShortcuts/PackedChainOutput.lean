import GreedyShortcuts.PackedChainCover
import GreedyShortcuts.ChainQuadraticSharp

/-! An unconditional finite weaker chain-greedy theorem for every DAG.
A maximal packing constructs the cover and forward cliques construct the
constant-hop chain preprocessing. No efficient preprocessing is claimed. -/
namespace GreedyShortcuts.UniformChainPacking
open Finset DirectedPaths ChainUnion ChainCover
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cliqueWitness (r : ℕ) : PathWitness r r :=
  Classical.choice (pathWitness_nonempty r r (Nat.le_refl _))

noncomputable def packedOutput (G : V → V → Prop) (hG : CanonicalSegments.Acyclic G)
    (r : ℕ) (hr : 3 ≤ r) : Finset (V × V) :=
  (context G hG r r (cliqueWitness r)).shortcuts r (by omega)

/-- Actual legal output, explicit size and ordinary-hop guarantees, with the
chain cover and preprocessing witnesses both constructed internally. -/
theorem packedOutput_spec (G : V → V → Prop) (hG : CanonicalSegments.Acyclic G)
    (r : ℕ) (hr : 3 ≤ r) (hn : Fintype.card V ≤ r^3) :
    packedOutput G hG r hr ⊆ candidates G ∧
    (packedOutput G hG r hr).card ≤ 51*Fintype.card V*r+2 ∧
    ∀ s t,Reachable G s t → ∃ q : DWalk s t,
      Allowed (augment G (packedOutput G hG r hr)) q ∧ q.length ≤ 7*r+2 := by
  classical
  let T := context G hG r r (cliqueWitness r)
  have hI : Fintype.card {c // c∈packing G r} ≤ r^2 := by
    have hpack := packing_card_mul G r
    have hm : (packing G r).card*r ≤ r^2*r := by nlinarith
    have hc := Nat.le_of_mul_le_mul_right hm (by omega : 0 < r)
    simpa only [Fintype.card_coe] using hc
  have hnum : 25*(Fintype.card V*Fintype.card {c // c∈packing G r}) ≤
      (25*Fintype.card V*r)*r := by
    nlinarith [Nat.mul_le_mul_left (25*Fintype.card V) hI]
  have hdiv : 25*(Fintype.card V*Fintype.card {c // c∈packing G r})/r ≤
      25*Fintype.card V*r := by
    simpa only [Nat.mul_div_cancel _ (by omega : 0 < r)] using
      Nat.div_le_div_right (c:=r) hnum
  refine ⟨T.shortcuts_legal r (by omega),?_,?_⟩
  · have hc := T.shortcuts_card_quadratic_sharp r hr
    change (packedOutput G hG r hr).card ≤ r*Fintype.card V+
      2*(25*(Fintype.card V*Fintype.card {c // c∈packing G r})/r+1) at hc
    nlinarith
  · intro s t hst
    obtain ⟨q,hq,hlen⟩ := T.shortcuts_hop_bound
      (context_cover G hG r r (by omega) (cliqueWitness r)) r (by omega) hst
    exact ⟨q,hq,by omega⟩


/-- A canonical rounded cube-root scale, characterized without real powers. -/
theorem exists_radius (n : ℕ) : ∃ r : ℕ,3 ≤ r ∧ n ≤ r^3 := by
  refine ⟨n+3,by omega,?_⟩
  have hp : n+3 ≤ (n+3)^3 := le_self_pow (by omega) (by decide)
  exact (show n ≤ n+3 by omega).trans hp

noncomputable def radius (n : ℕ) : ℕ := Nat.find (exists_radius n)

theorem radius_spec (n : ℕ) : 3 ≤ radius n ∧ n ≤ (radius n)^3 :=
  Nat.find_spec (exists_radius n)

theorem radius_min (n r : ℕ) (hr : 3 ≤ r) (hn : n ≤ r^3) : radius n ≤ r :=
  Nat.find_min' (exists_radius n) ⟨hr,hn⟩

theorem radius_predecessor (n : ℕ) (h : 3 < radius n) : (radius n-1)^3 < n := by
  by_contra hn
  have hm := radius_min n (radius n-1) (by omega) (by omega)
  omega

noncomputable def defaultOutput (G : V → V → Prop) (hG : CanonicalSegments.Acyclic G) :
    Finset (V × V) :=
  packedOutput G hG (radius (Fintype.card V)) (radius_spec _).1

/-- Every finite DAG now has this actual weaker chain-greedy output, with
all cover, preprocessing and scale choices made internally. -/
theorem defaultOutput_spec (G : V → V → Prop) (hG : CanonicalSegments.Acyclic G) :
    defaultOutput G hG ⊆ candidates G ∧
    (defaultOutput G hG).card ≤ 51*Fintype.card V*radius (Fintype.card V)+2 ∧
    ∀ s t,Reachable G s t → ∃ q : DWalk s t,
      Allowed (augment G (defaultOutput G hG)) q ∧ q.length ≤ 7*radius (Fintype.card V)+2 :=
  packedOutput_spec G hG _ (radius_spec _).1 (radius_spec _).2

end GreedyShortcuts.UniformChainPacking
