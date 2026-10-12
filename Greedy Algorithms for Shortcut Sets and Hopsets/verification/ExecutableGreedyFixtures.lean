import GreedyShortcuts.ChainExecutableGreedy

/-! Actual evaluation fixtures. These execute the definitions; they do not
replace the kernel proofs connecting them to the existing mathematical model. -/
open GreedyShortcuts GreedyShortcuts.DirectedPaths GreedyShortcuts.CanonicalSegments
open GreedyShortcuts.ChainUnion SimpleGraph
open LinearDistancePreservers.ConsistentTiebreaking

private def pathEdge {n : ℕ} (u v : Fin n) : Bool := decide (u.val+1=v.val)

private theorem path_monotone {n : ℕ} {s t : Fin n} (p : DWalk s t)
    (hp : Allowed (fun u v => pathEdge u v=true) p) : s.val≤t.val := by
  induction p with
  | nil => exact le_rfl
  | @cons s u t h p ih =>
    have hh := (allowed_cons _ h p).mp hp
    have ht := ih hh.2
    have he : s.val+1=u.val := by simpa [pathEdge] using hh.1
    omega

private def singletonContext (n : ℕ) : ChainDistance.Context (Fin n) (Fin n) where
  G u v := pathEdge u v=true
  acyclic := by
    apply (acyclic_iff_reachable_antisymm _).mpr
    intro s t hst hts
    obtain ⟨p,hp⟩ := hst
    obtain ⟨q,hq⟩ := hts
    exact Fin.ext (Nat.le_antisymm (path_monotone p hp) (path_monotone q hq))
  chains c := {
    length := 1
    node := fun _ => c
    injective := fun _ _ _ => Subsingleton.elim _ _
    forward := by intro i j hij; have := i.isLt; have := j.isLt; omega }
  disjoint := by
    intro i j hij
    simp [Chain.support,hij]
  K := 0
  witnesses _ := {
    edges := ∅
    forward := by simp
    card_le := by simp
    short := by
      intro i j _
      have h : i=j := Subsingleton.elim _ _
      subst j
      exact ⟨.nil,allowed_nil _ _,by simp⟩ }

#guard FiniteExecutableGreedy.select (fun x : ℕ => x) [4,2,3,2] = some 2
#guard FiniteExecutableGreedy.select (fun _ : ℕ => 0) [4,2,3] = some 4
#guard FiniteExecutableGreedy.select (fun x : ℕ => x) [] = none
#guard (ChainExecutableGreedy.choices (@pathEdge 3)).length = 3
#guard ChainExecutableGreedy.output (singletonContext 0) pathEdge 2 = ∅
#guard ChainExecutableGreedy.output (singletonContext 1) pathEdge 2 = ∅
#guard ChainExecutableGreedy.output (singletonContext 3) pathEdge 3 = ∅
#guard ChainExecutableGreedy.output (singletonContext 3) pathEdge 2 = {(0,2)}
#guard ChainExecutableObjective.stopped (singletonContext 3) pathEdge 2
    (ChainExecutableGreedy.output (singletonContext 3) pathEdge 2)
