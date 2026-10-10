import GreedyShortcuts.ChainLevels

/-! A concrete quadratic lower bound for the actual raw chain potential.
This is weaker than the paper's open cubic-progress claim. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem balanced_product (L : ℕ) (hL : 4 ≤ L) :
    L^2 ≤ 25*((L-(L/2+1))*(L/2+1-2)) := by
  have hrem := Nat.mod_lt L (by omega : 0 < 2)
  have hdiv := Nat.mod_add_div L 2
  have hpos : 0 < L/2-1 := by omega
  have hfirst : L/2-1 ≤ L-(L/2+1) := by omega
  have hsecond : L/2+1-2=L/2-1 := by omega
  have hfive : L ≤ 5*(L/2-1) := by omega
  rw [hsecond]
  have hprod := Nat.mul_le_mul_right (L/2-1) hfirst
  have hsq := Nat.mul_self_le_mul_self hfive
  nlinarith

/-- Every important pair of normalized distance at least four constructs a
legal shortcut with a genuine quadratic raw-potential drop. -/
theorem exists_quadratic_drop_for_pair {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (hst : (s,t) ∈ T.important) (hL : 4 ≤ T.distance H s t) :
    ∃ e ∈ candidates T.G,(T.distance H s t)^2 ≤ 
      25*(T.potential H-T.potential (insert e H)) := by
  classical
  obtain ⟨p,hp,hmin⟩ := T.distance_spec H (T.important_spec hst).1
  let k := T.distance H s t/2+1
  have hk : 2 ≤ k := by dsimp [k];omega
  have hkp : k ≤ T.count p := by dsimp [k];omega
  obtain ⟨i,_hi,hcount,hpair⟩ := T.exists_important_prefix_count hH p hp k hk hkp
  have he := p.append_take_drop_eq i
  have hallow : Allowed (T.graph H s) ((p.take i).append (p.drop i)) := by
    simpa only [he] using hp
  have hcost : T.count ((p.take i).append (p.drop i))=T.distance H s t := by
    simpa only [he] using hmin
  refine ⟨(s,p.getVert i),T.prefix_candidate hH (p.take i) (p.drop i)
    hallow hcost hpair (by omega),?_⟩
  have hdrop := T.one_source_product_drop hH (p.take i) (p.drop i) hallow hcost hpair
  rw [hcount] at hdrop
  exact (balanced_product (T.distance H s t) hL).trans (Nat.mul_le_mul_left 25 hdrop)

end GreedyShortcuts.ChainDistance.Context
