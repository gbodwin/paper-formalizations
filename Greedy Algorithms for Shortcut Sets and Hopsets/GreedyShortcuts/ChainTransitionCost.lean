import GreedyShortcuts.FiniteDistanceDP
import GreedyShortcuts.ChainCounting
import GreedyShortcuts.ChainSubwalk

/-! Exact additive 0/1 cost of the actual chain-contiguous filtered walks.
Validity may be rebased in the proof; no rebased minimum is asserted. -/
namespace GreedyShortcuts.ChainTransitionCost
open Finset SimpleGraph DirectedPaths ChainFirst
open LinearDistancePreservers.ConsistentTiebreaking

variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

def present : Option I → ℕ
  | none => 0
  | some _ => 1

def charge (color : Fin n → Option I) (u v : Fin n) : ℕ :=
  if color u=color v then 0 else present (color v)

omit [Fintype I] in
theorem charge_le_one (color : Fin n → Option I) (u v : Fin n) : charge color u v ≤ 1 := by
  unfold charge
  split_ifs <;> cases color v <;> simp [present]

variable (T : ChainDistance.Context (Fin n) I)

theorem chainSet_cons {s u t : Fin n} (h : (⊤ : SimpleGraph (Fin n)).Adj s u) (p : DWalk u t) :
    T.chainSet (.cons h p)=(label T.chains s).toFinset ∪ T.chainSet p := by
  classical
  ext c
  simp only [T.mem_chainSet,Walk.support_cons,List.mem_cons,Finset.mem_union,Option.mem_toFinset]
  aesop

/-- A first label different from the next label cannot recur later. -/
theorem start_label_absent {H : Finset (Fin n × Fin n)} (hH : H ⊆ candidates T.G)
    {s u t : Fin n} (h : (⊤ : SimpleGraph (Fin n)).Adj s u) (p : DWalk u t)
    (hp : Allowed (T.graph H s) (.cons h p)) {c : I}
    (hs : label T.chains s=some c) (hu : label T.chains u≠some c) : c∉T.chainSet p := by
  intro hc
  obtain ⟨v,hv,hvc⟩ := (T.mem_chainSet p c).mp hc
  obtain ⟨j,hjv,hj⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have hh := T.graph_convex hH hp (i:=0) (j:=1) (k:=j+1)
    (by omega) (by omega) (by simpa using Nat.add_le_add_right hj 1) c
    (by simpa using hs) (by simpa only [Walk.getVert_cons_succ,hjv] using hvc)
  exact hu (by simpa using hh)

/-- Chain-set cardinality is exactly initial coverage plus entry charges. -/
theorem count_eq_entry_cost {H : Finset (Fin n × Fin n)} (hH : H ⊆ candidates T.G)
    {s t : Fin n} (p : DWalk s t) (hp : Allowed (T.graph H s) p) :
    T.count p=present (label T.chains s)+FiniteDistanceDP.walkCost (charge (label T.chains)) p := by
  classical
  induction p with
  | @nil u => cases hs : label T.chains u <;> simp [ChainDistance.Context.count,ChainDistance.Context.chainSet,hs,present]
  | @cons s u t h p ih =>
    have ht := (allowed_cons _ h p).mp hp
    have hsu : Reachable T.G s u :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) s u).mp (reachable_edge ht.1.1)
    have hp' := T.allowed_rebase hH hsu p ht.2
    have hind := ih hp'
    rw [FiniteDistanceDP.walkCost_cons]
    cases hs : label T.chains s with
    | none =>
      have hc : T.count (.cons h p)=T.count p := by
        unfold ChainDistance.Context.count
        rw [chainSet_cons,hs]
        simp
      rw [hc,hind]
      cases hu : label T.chains u <;> simp [charge,hs,hu,present]
    | some c =>
      by_cases hu : label T.chains u=some c
      · have hmem : c∈T.chainSet p := (T.mem_chainSet p c).mpr ⟨u,p.start_mem_support,hu⟩
        have hc : T.count (.cons h p)=T.count p := by
          unfold ChainDistance.Context.count
          rw [chainSet_cons,hs]
          simp [hmem]
        rw [hc,hind]
        simp [charge,hs,hu,present]
      · have hmem := start_label_absent T hH h p hp hs hu
        have hc : T.count (.cons h p)=T.count p+1 := by
          unfold ChainDistance.Context.count
          rw [chainSet_cons,hs]
          simp [hmem]
        rw [hc,hind]
        have hne : (some c : Option I)≠label T.chains u := Ne.symm hu
        simp only [charge,hs,ite_eq_right hne,present]
        omega

end GreedyShortcuts.ChainTransitionCost
