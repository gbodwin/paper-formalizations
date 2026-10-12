import GreedyShortcuts.LongestPathMaximum
import GreedyShortcuts.FiniteReachabilityDP
import GreedyShortcuts.PackedChainCover

/-! Search for an unused reachability chain through the original strict
transitive closure. Covered vertices may lie between consecutive chain nodes;
using only the original residual edge graph would not prove the cover property. -/
namespace GreedyShortcuts.ComputedChainSearch
open SimpleGraph DirectedPaths CanonicalSegments FiniteLongestPathDP ChainUnion
open LinearDistancePreservers.ConsistentTiebreaking
variable {n : ℕ}

def closure (edge : Fin n → Fin n → Bool) (u v : Fin n) : Bool :=
  decide (u≠v) && FiniteReachabilityDP.reaches edge u v

theorem closure_iff (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v) (u v : Fin n) :
    closure edge u v=true ↔ u≠v ∧ Reachable G u v := by
  simp [closure,FiniteReachabilityDP.reaches_iff G hG edge he]

theorem closure_acyclic (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v) :
    Acyclic (fun u v => closure edge u v=true) := by
  apply (acyclic_iff_reachable_antisymm _).mpr
  intro s t hst hts
  have hstep : ∀u v,closure edge u v=true → Reachable G u v :=
    fun u v h => ((closure_iff G hG edge he u v).mp h).2
  exact (acyclic_iff_reachable_antisymm G).mp hG s t
    (DirectedLift.reachable id hstep hst) (DirectedLift.reachable id hstep hts)

def ChainList (G : Fin n → Fin n → Prop) (xs : List (Fin n)) : Prop :=
  xs.Nodup ∧ ∀ (i j : ℕ) (hi : i<xs.length) (hj : j<xs.length),
    i<j → Reachable G xs[i] xs[j]

theorem maximum_chain (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (enabled : Fin n → Bool) : ChainList G (maximum (closure edge) enabled) := by
  have hcl := closure_acyclic G hG edge he
  refine ⟨maximum_nodup _ hcl (closure edge) (fun _ _ => Iff.rfl) enabled,?_⟩
  intro i j hi hj hij
  have hn : maximum (closure edge) enabled≠[] := by
    intro hz
    simp only [hz,List.length_nil] at hi
    omega
  obtain ⟨s,t,p,hp,_,hs⟩ := maximum_sound (closure edge) enabled hn
  have hiEq : (maximum (closure edge) enabled)[i]=p.getVert i := by
    simp only [←hs]
    exact p.support_getElem_eq_getVert _
  have hjEq : (maximum (closure edge) enabled)[j]=p.getVert j := by
    simp only [←hs]
    exact p.support_getElem_eq_getVert _
  rw [hiEq,hjEq]
  exact DirectedLift.reachable id (fun u v h => ((closure_iff G hG edge he u v).mp h).2)
    (ShortcutWalk.reachable_segment hp hij.le)

theorem chainList_take {G : Fin n → Fin n → Prop} {xs : List (Fin n)}
    (h : ChainList G xs) (r : ℕ) : ChainList G (xs.take r) := by
  refine ⟨h.1.take,?_⟩
  intro i j hi hj hij
  have hi' : i<xs.length := by simp only [List.length_take] at hi;omega
  have hj' : j<xs.length := by simp only [List.length_take] at hj;omega
  simpa only [List.getElem_take] using h.2 i j hi' hj' hij

/-- Literal prefix extraction; none means there is no sufficiently long row. -/
def find (edge : Fin n → Fin n → Bool) (enabled : Fin n → Bool) (r : ℕ) : Option (List (Fin n)) :=
  let xs := maximum (closure edge) enabled
  if r≤xs.length then some (xs.take r) else none

theorem find_spec (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (enabled : Fin n → Bool) (r : ℕ) {xs : List (Fin n)} (h : find edge enabled r=some xs) :
    xs.length=r ∧ ChainList G xs ∧ ∀v∈xs,enabled v=true := by
  dsimp only [find] at h
  split_ifs at h with hr
  · have hx := Option.some.inj h
    subst xs
    refine ⟨by simp [Nat.min_eq_left hr],chainList_take (maximum_chain G hG edge he enabled) r,?_⟩
    intro v hv
    exact maximum_enabled _ _ (List.mem_of_mem_take hv)

/-- Every supplied enabled reachability chain has an actual closure walk of
exactly one fewer edges. Used only to prove completeness of the computed search. -/
theorem chain_walk (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (enabled : Fin n → Bool) {r : ℕ} (c : UniformChainPacking.FixedChain G r)
    (hen : ∀i,enabled (c.1 i)=true) (k i : ℕ) (hi : i<r) (hk : i+k<r) :
    ∃t, ∃p : DWalk (c.1 ⟨i,hi⟩) t,
      Allowed (fun u v => closure edge u v=true) p ∧
      (∀v∈p.support,enabled v=true) ∧ p.length=k := by
  induction k generalizing i with
  | zero =>
    refine ⟨c.1 ⟨i,hi⟩,.nil,allowed_nil _ _,?_,rfl⟩
    simpa using hen ⟨i,hi⟩
  | succ k ih =>
    have hi' : i+1<r := by omega
    have hk' : (i+1)+k<r := by omega
    obtain ⟨t,p,hp,hena,hlen⟩ := ih (i+1) hi' hk'
    have hne : c.1 ⟨i,hi⟩≠c.1 ⟨i+1,hi'⟩ := by
      intro hh
      have hh' : i=i+1 := congrArg Fin.val (c.2.1 hh)
      omega
    have ha : (⊤ : SimpleGraph (Fin n)).Adj (c.1 ⟨i,hi⟩) (c.1 ⟨i+1,hi'⟩) := by simpa using hne
    have hg := (closure_iff G hG edge he _ _).mpr
      ⟨hne,c.2.2 ⟨i,hi⟩ ⟨i+1,hi'⟩ (by simp)⟩
    refine ⟨t,.cons ha p,(allowed_cons _ ha p).mpr ⟨hg,hp⟩,?_,?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hen _
      · exact hena v hv
    · simpa only [Walk.length_cons,Nat.add_right_cancel_iff] using hlen

theorem find_complete (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (enabled : Fin n → Bool) {r : ℕ} (hr : 0<r) (c : UniformChainPacking.FixedChain G r)
    (hen : ∀i,enabled (c.1 i)=true) : find edge enabled r≠none := by
  obtain ⟨t,p,hp,hena,hlen⟩ := chain_walk G hG edge he enabled c hen (r-1) 0 hr (by omega)
  have hm := maximum_complete _ (closure_acyclic G hG edge he)
    (closure edge) (fun _ _ => Iff.rfl) enabled p hp hena
  have hrm : r≤(maximum (closure edge) enabled).length := by omega
  simp [find,hrm]

end GreedyShortcuts.ComputedChainSearch
