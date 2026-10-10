import GreedyShortcuts.PathFourRoutes

/-! Convert the same four-leg numerical routes into native directed walks
and the existing finite path-preprocessing interface. -/
namespace GreedyShortcuts.PathFour
open Finset SimpleGraph DirectedPaths ChainUnion
open LinearDistancePreservers.ConsistentTiebreaking

def finEdges (E : Finset (ℕ × ℕ)) (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun e => (e.1.val,e.2.val)∈E)

theorem finEdges_card (E : Finset (ℕ × ℕ)) (m : ℕ) : (finEdges E m).card ≤ E.card := by
  let f : Fin m × Fin m → ℕ × ℕ := fun e => (e.1.val,e.2.val)
  have hf : Function.Injective f := by
    intro e e' he
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))
  have hs : (finEdges E m).image f⊆E := by
    intro e he
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hq).2
  rw [← Finset.card_image_of_injective (finEdges E m) hf]
  exact Finset.card_le_card hs

theorem route_walk {m : ℕ} (E : Finset (ℕ × ℕ))
    (hE : ∀ e∈E,e.1 < e.2 ∧ e.2 < m) (i j : Fin m) (hroute : Route E i.val j.val) :
    ∃ p : DWalk i j,Allowed (fun u v => (u,v)∈finEdges E m) p ∧ p.length ≤ 4 := by
  have right_bound : ∀ a b,a < m → Leg E a b → b < m := by
    intro a b ha hab
    rcases hab with rfl | he
    · exact ha
    · exact (hE _ he).2
  have one : ∀ a b : Fin m,Leg E a.val b.val →
      ∃ p : DWalk a b,Allowed (fun u v => (u,v)∈finEdges E m) p ∧ p.length ≤ 1 := by
    intro a b hab
    rcases hab with he | he
    · have hab' : a=b := Fin.ext he
      subst b
      exact ⟨.nil,allowed_nil _ _,by simp⟩
    · have hlt := (hE _ he).1
      have ha : (⊤ : SimpleGraph (Fin m)).Adj a b := by
        simpa using (show a≠b from fun h => (Nat.ne_of_lt hlt) (congrArg Fin.val h))
      exact ⟨.cons ha .nil,
        (DirectedPaths.allowed_cons (fun u v : Fin m => (u,v)∈finEdges E m) ha .nil).mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,allowed_nil _ _⟩,by simp⟩
  obtain ⟨a,b,c,h1,h2,h3,h4⟩ := hroute
  have ha := right_bound i.val a i.isLt h1
  have hb := right_bound a b ha h2
  have hc := right_bound b c hb h3
  obtain ⟨p,hp,hpl⟩ := one i ⟨a,ha⟩ h1
  obtain ⟨q,hq,hql⟩ := one ⟨a,ha⟩ ⟨b,hb⟩ h2
  obtain ⟨r,hr,hrl⟩ := one ⟨b,hb⟩ ⟨c,hc⟩ h3
  obtain ⟨s,hs,hsl⟩ := one ⟨c,hc⟩ j h4
  refine ⟨((p.append q).append r).append s,?_,?_⟩
  · exact (allowed_append _ _ _).mpr ⟨(allowed_append _ _ _).mpr
      ⟨(allowed_append _ _ _).mpr ⟨hp,hq⟩,hr⟩,hs⟩
  · simp only [Walk.length_append]
    omega

def witness (m K : ℕ) (E : Finset (ℕ × ℕ))
    (hE : ∀ e∈E,e.1 < e.2 ∧ e.2 < m) (hcard : E.card ≤ K*m)
    (hroutes : ∀ i j,i ≤ j → j < m → Route E i j) : PathWitness m K where
  edges := finEdges E m
  forward := fun _ he => (hE _ (Finset.mem_filter.mp he).2).1
  card_le := (finEdges_card E m).trans hcard
  short := fun i j hij => route_walk E hE i j (hroutes i.val j.val hij j.isLt)

end GreedyShortcuts.PathFour
