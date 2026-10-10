import GreedyShortcuts.PathMedianEdges

/-! A literal finite two-hop path witness obtained from the median network.
The logarithmic edge budget is proved; no physical runtime is asserted. -/
namespace GreedyShortcuts.PathMedian
open Finset SimpleGraph DirectedPaths ChainUnion
open LinearDistancePreservers.ConsistentTiebreaking

def finEdges (d m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun e => (e.1.val,e.2.val)∈edges d m)

theorem finEdges_forward (d m : ℕ) {e : Fin m × Fin m} (he : e∈finEdges d m) :
    e.1<e.2 :=
  (edges_forward d m (Finset.mem_filter.mp he).2).1

theorem finEdges_card (d m : ℕ) : (finEdges d m).card≤m*d := by
  let f : Fin m × Fin m → ℕ × ℕ := fun e => (e.1.val,e.2.val)
  have hf : Function.Injective f := by
    intro e e' he
    apply Prod.ext
    · apply Fin.ext;exact congrArg Prod.fst he
    · apply Fin.ext;exact congrArg Prod.snd he
  have hs : (finEdges d m).image f ⊆ edges d m := by
    intro e he
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hq).2
  calc
    (finEdges d m).card=((finEdges d m).image f).card := (Finset.card_image_of_injective _ hf).symm
    _≤(edges d m).card := Finset.card_le_card hs
    _≤m*d := edges_card d m

theorem finEdges_short (d m : ℕ) (hm : m≤2^d) (i j : Fin m) (hij : i≤j) :
    ∃ p : DWalk i j,Allowed (fun u v => (u,v)∈finEdges d m) p ∧ p.length≤2 := by
  obtain ⟨z,hiz,hzj,hizE,hzjE⟩ := two_legs d m i.val j.val hm hij j.isLt
  let zz : Fin m := ⟨z,lt_of_le_of_lt hzj j.isLt⟩
  have leg : ∀ a b : Fin m,(a.val=b.val ∨ (a.val,b.val)∈edges d m) →
      ∃ p : DWalk a b,Allowed (fun u v => (u,v)∈finEdges d m) p ∧ p.length≤1 := by
    intro a b hab
    rcases hab with he | he
    · have hab' : a=b := Fin.ext he
      subst b
      exact ⟨.nil,allowed_nil _ _,by simp⟩
    · have hlt := (edges_forward d m he).1
      have ha : (⊤ : SimpleGraph (Fin m)).Adj a b := by
        simpa using (show a≠b from fun h => (Nat.ne_of_lt hlt) (congrArg Fin.val h))
      refine ⟨.cons ha .nil,?_,by simp⟩
      exact (DirectedPaths.allowed_cons (fun u v : Fin m => (u,v)∈finEdges d m) ha .nil).mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,allowed_nil _ _⟩
  obtain ⟨p,hp,hpl⟩ := leg i zz hizE
  obtain ⟨q,hq,hql⟩ := leg zz j hzjE
  refine ⟨p.append q,(allowed_append _ p q).mpr ⟨hp,hq⟩,?_⟩
  simpa only [Walk.length_append] using Nat.add_le_add hpl hql

/-- Every ordered path has a concrete two-hop network with at most
m*ceil(log_2(m)) edges, including empty and singleton paths. -/
def witness (m : ℕ) : PathWitness m (Nat.clog 2 m) where
  edges := finEdges (Nat.clog 2 m) m
  forward := fun _ h => finEdges_forward _ _ h
  card_le := by simpa only [Nat.mul_comm] using finEdges_card (Nat.clog 2 m) m
  short := by
    intro i j hij
    obtain ⟨p,hp,hl⟩ := finEdges_short (Nat.clog 2 m) m (Nat.le_pow_clog (by decide) m) i j hij
    exact ⟨p,hp,by omega⟩


/-- A common budget works for every path shorter than the ambient size. -/
def witnessLE (m K : ℕ) (hK : Nat.clog 2 m≤K) : PathWitness m K where
  edges := (witness m).edges
  forward := (witness m).forward
  card_le := (witness m).card_le.trans (Nat.mul_le_mul_right m hK)
  short := (witness m).short


/-- The existing disjoint-chain union now has a fully constructed logarithmic
path witness rather than a supplied preprocessing theorem. -/
theorem supershortcut_union {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] {G : V → V → Prop} (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support)) :
    ∃ H : Finset (V × V),H ⊆ candidates G ∧
      H.card≤Nat.clog 2 (Fintype.card V)*Fintype.card V ∧
      ∀ c (i j : Fin (C c).length),i≤j →
        hopDist (augment G H) ((C c).node i) ((C c).node j)≤4 := by
  apply ChainUnion.supershortcut_union C hdisj (Nat.clog 2 (Fintype.card V))
  intro m hm
  exact ⟨witnessLE m _ ((Nat.clog_monotone 2) hm)⟩

end GreedyShortcuts.PathMedian
